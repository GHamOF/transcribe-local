#!/usr/bin/env python3
"""
meeting_tray.py — a system-tray button for meeting_recorder.py.

Left-click the tray icon to START recording; left-click again to STOP.
On stop, a small popup asks for a title and the number of speakers, then the
audio is sent to the TranscriptionSuite server and the diarized transcript is
written to the output folder (see meeting_recorder.OUTPUT_DIR) — no terminal,
no typing python commands.

The icon is grey when idle, red while recording (hover it for the elapsed time)
and amber while transcribing.

Run it with pythonw.exe so there's no console window:
    pythonw meeting_tray.py

Deps: pip install soundcard numpy requests pystray pillow   (tkinter ships with Python)
"""
import os, sys, time, threading, queue, json
from datetime import datetime, timedelta

if sys.platform == "darwin":          # the macOS menu-bar app is its own module
    import runpy
    runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "meeting_tray_mac.py"),
                   run_name="__main__")
    sys.exit(0)

# --- make this importable no matter where it's launched from, and give the
#     (console-less) pythonw process somewhere for prints to go BEFORE we import
#     meeting_recorder, which writes to sys.stdout at import time. ------------
_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)
try:
    _logf = open(os.path.join(_HERE, "tray.log"), "a", buffering=1, encoding="utf-8", errors="replace")
    sys.stdout = _logf
    sys.stderr = _logf
except Exception:
    pass

# --- single instance: a named mutex. (Was a localhost port bind, but Windows
#     reserves random port ranges for Hyper-V/Docker at boot; when 49731 landed in
#     one the bind failed and the tray silently exited as if already running.)
import ctypes, ctypes.wintypes
_k32 =ctypes.WinDLL("kernel32", use_last_error=True)
_k32.CreateMutexW.restype = ctypes.c_void_p
_guard = _k32.CreateMutexW(None, False, "Local\\MeetingRecorderTray")
if ctypes.get_last_error() == 183:   # ERROR_ALREADY_EXISTS
    sys.exit(0)

# --- DPI awareness, before any window exists. Without it Windows stretches every
#     window like a bitmap on a scaled display (125%, 150%, …): blurry dialogs, and
#     a tray icon scaled up from 32 px. ------------------------------------------
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(1)    # PROCESS_SYSTEM_DPI_AWARE
except Exception:
    pass

import contextlib
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import pystray
from PIL import Image, ImageDraw
import meeting_recorder as mr


# ---------------------------------------------------------------- shared state
state = {"recording": False, "stop_event": None, "rec_thread": None, "wav": None,
         "started": 0.0, "started_wall": 0.0, "busy": 0, "status": "",   # busy = transcriptions/warm-ups running
         "quitting": False,
         "warm_until": None,   # a warm-up nobody records after is stopped at this (aware) time
         "restart": False}     # start a new recording as soon as this one has stopped
lock = threading.Lock()
ui_q = queue.Queue()          # tray thread -> tk main thread requests
icon = None
root = None

# Optional features, toggled from the tray menu and kept across restarts.
SETTINGS_FILE = os.path.join(_HERE, "tray-settings.json")
settings = {"calendar_prompt": False, "call_prompt": False, "end_prompt": False,
            "mic_ignore": []}   # mic_users() keys silenced with "Never for …"
# The call the current recording belongs to, as mic sessions (see recording_tick).
# asked: None, "switch"/"ended" while that prompt is open, "kept" after "Keep
# recording" on a call that ended (no asking again until it comes back).
rec_watch = {"id": None, "known": set(), "active": 0.0, "asked": None, "pending": set()}


def load_settings():
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as f:
            settings.update({k: v for k, v in json.load(f).items() if k in settings})
    except FileNotFoundError:
        pass
    except Exception as e:
        print(f"settings: could not read {SETTINGS_FILE}: {type(e).__name__}: {e}")


def save_settings():
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(settings, f, indent=2)
    except Exception as e:
        print(f"settings: could not write {SETTINGS_FILE}: {type(e).__name__}: {e}")


# ---------------------------------------------------------------- tray icon art
_IMAGES = {}


def make_image(kind):
    """The 64 px tray glyph for "idle", "rec" or "busy". PIL draws without
    anti-aliasing, so it's drawn at 4x and scaled down for smooth edges."""
    if kind not in _IMAGES:
        s = 4
        img = Image.new("RGBA", (64 * s, 64 * s), (0, 0, 0, 0))
        d = ImageDraw.Draw(img)
        box = lambda a, b: (a * s, a * s, b * s - 1, b * s - 1)
        if kind == "rec":
            d.ellipse(box(10, 54), fill=(224, 48, 48, 255))             # red disc
        elif kind == "busy":
            d.ellipse(box(10, 54), fill=(232, 150, 20, 255))            # amber: working
        else:
            d.ellipse(box(12, 52), outline=(150, 158, 168, 255), width=5 * s)
            d.ellipse(box(26, 38), fill=(150, 158, 168, 255))            # grey mic dot
        _IMAGES[kind] = img.resize((64, 64), Image.LANCZOS)
    return _IMAGES[kind]


def _clock(secs):
    secs = int(secs)
    return (f"{secs // 3600}:{secs // 60 % 60:02d}:{secs % 60:02d}" if secs >= 3600
            else f"{secs // 60}:{secs % 60:02d}")


def status_line():
    """What the tray is doing, in a few words (the menu's first line)."""
    if state["recording"]:
        return "Recording since " + time.strftime("%H:%M", time.localtime(state["started_wall"]))
    if state["busy"]:
        return state["status"] or "Working…"
    return "Idle"


_shown = {"kind": None, "menu": None}
_icon_lock = threading.Lock()     # called from the tray, tk, recording and worker threads


def refresh_icon():
    """Bring the icon, tooltip and menu up to date, touching only what changed:
    pystray writes a temp .ico and makes a new icon handle on every icon set,
    and rebuilds the whole menu on every update_menu. Never raises — this runs
    inside progress callbacks, where an error would fail a finished job."""
    if icon is None:
        return
    try:
        with _icon_lock:          # read state inside it too, or a stale view could be applied last
            rec, busy = state["recording"], state["busy"]
            kind = "rec" if rec else "busy" if busy else "idle"
            if rec:
                title = f"Meeting recorder — RECORDING {_clock(time.monotonic() - state['started'])}"
            else:
                title = "Meeting recorder — " + (status_line() if busy else "idle")
            title = title[:127]   # the shell's limit; longer raises ValueError in pystray
            menu = (kind, status_line())
            if kind != _shown["kind"]:
                icon.icon = make_image(kind)
                _shown["kind"] = kind
            if title != icon.title:
                icon.title = title
            if menu != _shown["menu"]:
                icon.update_menu()
                _shown["menu"] = menu
    except Exception as e:
        print(f"refresh_icon: {type(e).__name__}: {e}")


def hide_from_capture(win):
    """Keep a window out of screen shares and screenshots: Teams, Zoom, browsers,
    OBS and the Snipping Tool all capture through APIs that honour this, and show
    what's behind it instead. Our dialogs can pop up mid-meeting (a prompt, or a
    transcript finishing). Call it right after creating the window.

    Tk only creates the real top-level window when it's first shown, and
    recreates it on some style changes, so it's applied on <Map>; until then the
    window is fully transparent, so not a single frame can be captured."""
    def on_map(e):
        if e.widget is not win:
            return                            # the binding fires for child widgets too
        try:
            u32 = ctypes.windll.user32
            u32.SetWindowDisplayAffinity.argtypes = [ctypes.wintypes.HWND, ctypes.wintypes.DWORD]
            hwnd = int(win.wm_frame(), 16)    # the real top-level window, not tk's inner one
            if not u32.SetWindowDisplayAffinity(hwnd, 0x11):      # WDA_EXCLUDEFROMCAPTURE (Windows 10 2004+)
                if not u32.SetWindowDisplayAffinity(hwnd, 0x01):  # WDA_MONITOR: a black box, at least
                    print("hide_from_capture: failed, window stays invisible")
                    return
                print("hide_from_capture: excluding failed, window shows as black in captures")
        except Exception as e:
            print(f"hide_from_capture: {type(e).__name__}: {e}")
            return
        win.attributes("-alpha", 1.0)

    win.attributes("-alpha", 0.0)
    win.bind("<Map>", on_map, add="+")


def notify(title, msg):
    """A tray balloon. Windows draws these itself, so unlike our dialogs they'd
    show in a screen share: skipped while an app has the mic (a call, most likely).
    Every balloon duplicates a dialog or the icon's colour, so nothing is lost."""
    try:
        if mic_users():
            return
        icon.notify(msg, title)
    except Exception:
        pass


# ---------------------------------------------------------------- record control
def start_recording():
    with lock:
        if state["recording"]:
            return
        os.makedirs(mr.AUDIO_DIR, exist_ok=True)
        wav = os.path.join(mr.AUDIO_DIR, f"{mr._ts()}.wav")
        ev = threading.Event()
        th = threading.Thread(target=record_thread_main, args=(wav, ev), daemon=True)
        state.update(recording=True, stop_event=ev, rec_thread=th, wav=wav,
                     started=time.monotonic(), started_wall=time.time())
    th.start()
    refresh_icon()
    notify("Recording started", "Click the tray icon again to stop.")


def record_thread_main(wav, ev):
    """Run the capture. On ANY crash, reset state and surface a dialog instead of
    dying silently and leaving the icon stuck red. On a clean stop, hand the audio
    (with its peak levels) to the tk thread for the title/speakers popup."""
    try:
        wav_, secs, peak_mic, peak_sys = mr.record_session(wav, ev)   # blocks until ev set
    except Exception as e:
        with lock:
            state["recording"] = False
            restart, state["restart"] = state["restart"], False
        refresh_icon()
        if restart and not state["quitting"]:
            start_recording()
        ui_q.put(("result", {"ok": False, "title": "Recording crashed",
                             "body": f"{type(e).__name__}: {e}\n\nAudio may be incomplete:\n{wav}"}))
        return
    with lock:
        state["recording"] = False
        restart, state["restart"] = state["restart"], False
    refresh_icon()
    if not state["quitting"]:
        if restart:                       # "Stop and record the new call": no gap before the next one
            start_recording()
        ui_q.put(("ask", {"wav": wav_, "secs": secs, "peak_mic": peak_mic, "peak_sys": peak_sys}))


def stop_recording():
    """Signal the capture thread to finish; record_thread_main pops the dialog
    when it returns (and flips the icon back to idle)."""
    with lock:
        ev = state["stop_event"] if state["recording"] else None
    if ev:
        ev.set()


# ---------------------------------------------------------------- result dialog
def show_result(ok, title, body, folder=None):
    """A visible, guaranteed outcome dialog (tray balloons are unreliable here).
    Success auto-closes after 15 s; failures stay until dismissed."""
    win = tk.Toplevel(root)
    hide_from_capture(win)
    win.title(title)
    win.resizable(False, False)
    win.attributes("-topmost", True)
    glyph = "✓" if ok else "⚠"
    color = "#137333" if ok else "#c5221f"
    tk.Label(win, text=glyph, font=("Segoe UI", 22), fg=color).grid(
        row=0, column=0, rowspan=2, padx=(16, 8), pady=16)
    tk.Label(win, text=title, font=("Segoe UI", 11, "bold")).grid(
        row=0, column=1, sticky="w", pady=(16, 0), padx=(0, 16))
    tk.Label(win, text=body, justify="left", foreground="#333",
             wraplength="390p").grid(     # points, so it scales with the display (520 px at 100%)
        row=1, column=1, sticky="w", pady=(2, 10), padx=(0, 16))
    btns = ttk.Frame(win)
    btns.grid(row=2, column=1, sticky="e", padx=16, pady=(0, 14))
    if folder:
        ttk.Button(btns, text="Open folder",
                   command=lambda: (os.startfile(folder) if os.path.isdir(folder) else None)).pack(side="left", padx=4)
    ttk.Button(btns, text="OK", command=win.destroy).pack(side="left", padx=4)
    win.bind("<Return>", lambda e: win.destroy())
    win.bind("<Escape>", lambda e: win.destroy())
    win.update_idletasks()
    w, h = win.winfo_width(), win.winfo_height()
    win.geometry(f"+{(win.winfo_screenwidth() - w) // 2}+{(win.winfo_screenheight() - h) // 3}")
    win.focus_force()
    if ok:
        win.after(15000, lambda: win.winfo_exists() and win.destroy())
    notify(title, body.splitlines()[0])   # best-effort balloon too; harmless if it no-ops


# ---------------------------------------------------------------- popup dialog
def show_transcribe_dialog(wav, secs=None, peak_mic=None, peak_sys=None):
    if not wav or not os.path.exists(wav) or os.path.getsize(wav) < 1024:
        show_result(False, "No audio",
                    "The recording is missing or empty — nothing to transcribe.\n\n"
                    f"{wav}")
        return

    win = tk.Toplevel(root)
    hide_from_capture(win)
    win.title("Transcribe recording")
    win.resizable(False, False)
    win.attributes("-topmost", True)
    pad = {"padx": 12, "pady": 6}

    heading = "Transcribe existing recording"
    if secs is not None:
        heading = f"Recording saved  ({int(secs) // 60}m {int(secs) % 60}s)"
    ttk.Label(win, text=heading, font=("Segoe UI", 10, "bold")).grid(
        row=0, column=0, columnspan=2, sticky="w", **pad)
    head = ttk.Frame(win)
    head.grid(row=1, column=0, columnspan=2, sticky="w", padx=12)
    ttk.Label(head, text=os.path.basename(wav), foreground="#666").pack(anchor="w")
    warns = []
    if secs is not None and secs < 2:
        warns.append("⚠ Very short recording — did capture start in time?")
    if peak_mic is not None and peak_mic < 0.001:
        warns.append("⚠ Your mic was silent — your own voice isn't in this recording.")
    if peak_sys is not None and peak_sys < 0.001:
        warns.append("⚠ System was silent — no remote audio (fine if nobody else spoke).")
    for w in warns:
        tk.Label(head, text=w, foreground="#c5221f", justify="left").pack(anchor="w")

    ttk.Label(win, text="Title:").grid(row=2, column=0, sticky="e", **pad)
    title_var = tk.StringVar()
    title_entry = ttk.Entry(win, textvariable=title_var, width=34)
    title_entry.grid(row=2, column=1, sticky="w", **pad)

    ttk.Label(win, text="Speakers:").grid(row=3, column=0, sticky="e", **pad)
    spk_var = tk.StringVar(value="0")
    spk = ttk.Spinbox(win, from_=0, to=12, textvariable=spk_var, width=6)
    spk.grid(row=3, column=1, sticky="w", **pad)
    ttk.Label(win, text="0 = let the model decide", foreground="#666").grid(
        row=4, column=1, sticky="w", padx=12)

    diar_var = tk.BooleanVar(value=True)
    ttk.Checkbutton(win, text="Diarize (label who said what)", variable=diar_var).grid(
        row=5, column=1, sticky="w", **pad)

    ttk.Label(win, text="Language:").grid(row=6, column=0, sticky="e", **pad)
    lang_var = tk.StringVar(value=mr.LANGUAGE)
    ttk.Combobox(win, textvariable=lang_var, width=6,      # a list, but any code can be typed
                 values=mr.LANGS if mr.LANGUAGE in mr.LANGS else [mr.LANGUAGE] + mr.LANGS).grid(
        row=6, column=1, sticky="w", **pad)

    btns = ttk.Frame(win)
    btns.grid(row=7, column=0, columnspan=2, sticky="e", padx=12, pady=(10, 12))

    def submit():
        title = title_var.get().strip()
        try:                                  # an empty or typed-over box mustn't block Transcribe
            speakers = max(int(spk_var.get().strip() or 0), 0) or None
        except ValueError:
            speakers = None
        diar = diar_var.get()
        lang = lang_var.get().strip() or mr.LANGUAGE
        win.destroy()
        threading.Thread(target=transcribe_worker,
                         args=(wav, title, speakers, diar, lang), daemon=True).start()
        notify("Transcribing…", "Starting the server if needed (a minute or two), then transcribing.")

    def later():
        win.destroy()
        show_result(True, "Saved for later",
                    f"Audio kept:\n{wav}\n\nRight-click the tray icon → "
                    "“Transcribe an existing recording…” when you want the transcript.",
                    folder=os.path.dirname(wav))

    ttk.Button(btns, text="Transcribe later", command=later).pack(side="left", padx=4)
    ttk.Button(btns, text="Transcribe", command=submit).pack(side="left", padx=4)

    win.bind("<Return>", lambda e: submit())
    win.bind("<Escape>", lambda e: later())
    win.update_idletasks()
    # center on screen
    w, h = win.winfo_width(), win.winfo_height()
    x = (win.winfo_screenwidth() - w) // 2
    y = (win.winfo_screenheight() - h) // 3
    win.geometry(f"+{x}+{y}")
    win.focus_force()
    title_entry.focus_set()


def transcribe_worker(wav, title, speakers, diar, lang):
    def progress(msg):
        print(msg)
        state["status"] = (str(msg).strip().splitlines() or [""])[0]   # tooltip and menu: one line
        refresh_icon()

    with lock:
        state["busy"] += 1
    refresh_icon()
    try:
        ui_q.put(mr.transcription_job(wav, title, speakers, diar, lang, progress))
    finally:
        with lock:
            state["busy"] -= 1
            if not state["busy"]:
                state["status"] = ""
        refresh_icon()


# ---------------------------------------------------------------- speaker names
def show_name_dialog(txt, then=None, title="", new=False):
    """Show sample context for every speaker plus a name box each; on Save,
    replace the [speaker N] labels in the .txt. `then` is a result payload to
    show once this dialog closes. The inbox copy (if configured) is written
    after Save — and after Skip too for a `new` transcript, so every meeting
    lands in the inbox once."""
    def finish(saved):
        line = mr.inbox_copy_line(txt, title) if (saved or new) else None
        if then:
            body = then["body"] + (f"\n{line}" if line else "")
            show_result(then["ok"] and not (line or "").startswith("⚠"),
                        then["title"], body, then.get("folder"))
        elif saved:
            show_result(not (line or "").startswith("⚠"), "Speakers renamed",
                        os.path.basename(txt) + (f"\n{line}" if line else ""),
                        folder=os.path.dirname(txt))

    turns = mr.read_turns(txt)
    speakers = sorted(dict.fromkeys(s for s, _ in turns),
                      key=lambda s: (len(s), s))   # speaker 2 before speaker 10
    if not speakers:
        finish(False); return

    win = tk.Toplevel(root)
    hide_from_capture(win)
    win.title("Who is who?")
    win.attributes("-topmost", True)
    win.columnconfigure(0, weight=1)
    win.rowconfigure(2, weight=1)
    ttk.Label(win, text="Name the speakers", font=("Segoe UI", 10, "bold")).grid(
        row=0, column=0, columnspan=2, sticky="w", padx=12, pady=(10, 0))
    ttk.Label(win, text=os.path.basename(txt), foreground="#666").grid(
        row=1, column=0, columnspan=2, sticky="w", padx=12)

    frame = ttk.Frame(win)
    frame.grid(row=2, column=0, columnspan=2, sticky="nsew", padx=12, pady=8)
    view = tk.Text(frame, width=100, height=26, wrap="word", font=("Segoe UI", 10),
                   relief="solid", borderwidth=1, padx=8, pady=6)
    sb = ttk.Scrollbar(frame, orient="vertical", command=view.yview)
    view.configure(yscrollcommand=sb.set)
    view.pack(side="left", fill="both", expand=True)
    sb.pack(side="right", fill="y")
    palette = ["#1a73e8", "#c5221f", "#137333", "#b06000", "#8430ce", "#007b83",
               "#d01884", "#5f6368"]
    for n, spk in enumerate(speakers):
        view.tag_configure(spk, foreground=palette[n % len(palette)],
                           font=("Segoe UI", 10, "bold"))
    view.tag_configure("hl", background="#fff4c2")     # every turn of the chosen speaker
    view.tag_configure("cur", background="#ffd54f")    # the turn we just jumped to
    view.tag_raise("cur", "hl")

    # the whole transcript, remembering where each speaker's turns sit
    sections = {spk: [] for spk in speakers}
    for spk, text in turns:
        start = view.index("end-1c")
        view.insert("end", f"[{spk}] ", spk)
        view.insert("end", text)
        sections[spk].append((start, view.index("end-1c")))
        view.insert("end", "\n\n")
    view.configure(state="disabled")

    pos = {"spk": None, "i": -1}
    counters = {}

    def jump(spk):
        """Highlight all of `spk`'s turns and step to the next one (wrapping)."""
        if pos["spk"] != spk:
            view.tag_remove("hl", "1.0", "end")
            for a, b in sections[spk]:
                view.tag_add("hl", a, b)
            if pos["spk"] in counters:
                counters[pos["spk"]].configure(text="")
            pos.update(spk=spk, i=-1)
        pos["i"] = (pos["i"] + 1) % len(sections[spk])
        a, b = sections[spk][pos["i"]]
        view.tag_remove("cur", "1.0", "end")
        view.tag_add("cur", a, b)
        view.see(b)
        view.see(a)
        counters[spk].configure(text=f"{pos['i'] + 1}/{len(sections[spk])}")

    boxes = ttk.Frame(win)
    boxes.grid(row=3, column=0, columnspan=2, sticky="w", padx=12)
    vars_ = {}
    for n, spk in enumerate(speakers):
        tk.Label(boxes, text=spk + ":", fg=palette[n % len(palette)],
                 font=("Segoe UI", 10, "bold")).grid(row=n, column=0, sticky="e", pady=3)
        v = tk.StringVar()
        e = ttk.Entry(boxes, textvariable=v, width=30)
        e.grid(row=n, column=1, sticky="w", padx=8, pady=3)
        if n == 0:
            e.focus_set()
        vars_[spk] = v
        ttk.Button(boxes, text=f"Next ▸  ({len(sections[spk])} turns)",
                   command=lambda s=spk: jump(s)).grid(row=n, column=2, sticky="w", pady=3)
        counters[spk] = ttk.Label(boxes, text="", foreground="#666", width=8)
        counters[spk].grid(row=n, column=3, sticky="w", padx=6)
    ttk.Label(win, text="Leave a box empty to keep that label.", foreground="#666").grid(
        row=4, column=0, columnspan=2, sticky="w", padx=12, pady=(4, 0))

    def save():
        names = {k: v.get() for k, v in vars_.items()}
        win.destroy()
        try:
            mr.rename_speakers(txt, names)
        except Exception as e:
            show_result(False, "Could not rename speakers", f"{type(e).__name__}: {e}\n\n{txt}")
            return
        finish(True)

    def skip():
        win.destroy()
        finish(False)

    btns = ttk.Frame(win)
    btns.grid(row=5, column=0, columnspan=2, sticky="e", padx=12, pady=(8, 12))
    ttk.Button(btns, text="Skip", command=skip).pack(side="left", padx=4)
    ttk.Button(btns, text="Save names", command=save).pack(side="left", padx=4)
    win.bind("<Return>", lambda e: save())
    win.bind("<Escape>", lambda e: skip())
    win.protocol("WM_DELETE_WINDOW", skip)
    win.update_idletasks()
    w, h = win.winfo_width(), win.winfo_height()
    win.geometry(f"+{(win.winfo_screenwidth() - w) // 2}+{max(0, (win.winfo_screenheight() - h) // 4)}")
    win.focus_force()


@contextlib.contextmanager
def topmost_parent():
    """The root is withdrawn, so a bare file dialog or message box opens behind
    other windows and looks like "nothing happened". Give it a visible, topmost
    parent."""
    parent = tk.Toplevel(root)
    parent.overrideredirect(True)
    parent.geometry("1x1+0+0")
    parent.attributes("-topmost", True)
    parent.update()
    try:
        yield parent
    finally:
        parent.destroy()


def pick_transcript_to_name():
    with topmost_parent() as parent:
        path = filedialog.askopenfilename(
            parent=parent, title="Pick a transcript to name speakers in",
            initialdir=mr.OUTPUT_DIR,
            filetypes=[("Transcript", "*.txt"), ("All files", "*.*")])
    if path:
        path = os.path.normpath(path)
        if not mr.read_turns(path):
            show_result(False, "No speaker labels", f"No [speaker] lines found in:\n{path}")
        else:
            show_name_dialog(path, title=mr.title_from_txt(path))


# ---------------------------------------------------------------- meeting prompts
# All off by default (tray menu → Meeting prompts…). The calendar one offers to
# warm the server up WARMUP_LEAD before a meeting; it learns of meetings from
# the new Outlook's reminder notifications (it has no API to ask). The mic one
# offers to record when an app opens the mic: a call answered, a meeting's join
# screen. Apps can be silenced from the prompt ("Never for …"). The end one,
# while recording, asks what to do when the call ends or another one starts.
WATCH_EVERY = 60             # s between checks, for all
CALL_GAP = 150               # s an app must leave the mic closed (two checks in a row) before its call counts as over
# Audio routers open the real mic whenever any app uses their virtual one, so
# they'd be named instead of the app that's actually in the call.
MIC_ROUTERS = ("steelseriessonar", "nvidia broadcast", "voicemeeter", "krisp")
WARMUP_LEAD = 120            # s before a meeting to offer the warm-up
KEEP_REMINDERS = timedelta(hours=6)
LATE_OFFER = timedelta(minutes=5)    # still offer it this long after the start (a late reminder)
MEETING_LENGTH = timedelta(hours=1)  # reminders carry no end time
WARM_GRACE = timedelta(minutes=10)   # after the meeting's end, before an unused warm-up is stopped
_MIC_STORE = r"Software\Microsoft\Windows\CurrentVersion\CapabilityAccessManager\ConsentStore\microphone"
_WPN_DB = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Microsoft", "Windows", "Notifications", "wpndatabase.db")


def outlook_reminders():
    """(start, title) of the meetings the new Outlook has shown a reminder for,
    read from Windows' notification store. A reminder leaves the store once
    dismissed, so callers keep their own copy."""
    import sqlite3, pathlib, urllib.parse, xml.etree.ElementTree as ET
    db = sqlite3.connect(pathlib.Path(_WPN_DB).as_uri() + "?mode=ro", uri=True, timeout=5)
    try:
        rows = db.execute("select n.Payload from Notification n join NotificationHandler h"
                          " on n.HandlerId = h.RecordId where n.Type = 'toast'"
                          " and h.PrimaryId like 'Microsoft.OutlookForWindows%'").fetchall()
    finally:
        db.close()
    out = []
    for (payload,) in rows:
        try:
            toast = ET.fromstring(payload.decode("utf-8") if isinstance(payload, bytes) else payload)
            launch = urllib.parse.parse_qs(toast.get("launch", ""))
            if launch.get("notificationType") != ["EventReminder"]:
                continue
            start = datetime.fromisoformat(json.loads(launch["itemId"][0])["meetingTime"].replace("Z", "+00:00"))
            title = (toast.findtext(".//text") or "").strip() or "Meeting"
            out.append((start.astimezone(), title))
        except Exception:
            continue                         # some other toast shape; not a meeting we can read
    return out


def mic_users():
    """The apps holding the microphone right now, minus this tray itself, audio
    routers and the ones silenced with "Never for …": what Windows' own mic-in-use indicator
    reads. {key: session}: the key is the consent-store key name, a package name for store apps
    (MSTeams_8wekyb3d8bbwe) or an exe path with # for \\ for the rest; an app's
    LastUsedTimeStop is 0 while it has the mic open. The session is its
    LastUsedTimeStart, which changes each time the app reopens the mic, so a call
    switch shows even when it falls between two checks."""
    import winreg
    skip = {sys.executable.replace("\\", "#").lower()} | {a.lower() for a in settings["mic_ignore"]}
    users = {}
    for path in (_MIC_STORE, _MIC_STORE + r"\NonPackaged"):
        try:
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER, path) as k:
                for i in range(winreg.QueryInfoKey(k)[0]):
                    name = winreg.EnumKey(k, i)
                    low = name.lower()
                    if low == "nonpackaged" or low in skip or any(r in low for r in MIC_ROUTERS):
                        continue
                    try:
                        with winreg.OpenKey(k, name) as app:
                            if winreg.QueryValueEx(app, "LastUsedTimeStop")[0] == 0:
                                users[name] = winreg.QueryValueEx(app, "LastUsedTimeStart")[0]
                    except OSError:
                        pass
        except OSError:
            pass
    return users


def app_name(key):
    """A readable name for a mic_users() key: the exe's name, or the package's."""
    if "#" in key:
        return os.path.splitext(key.rsplit("#", 1)[-1])[0]
    return key.split("_")[0].removeprefix("Microsoft.")


def show_prompt(title, body, buttons, timeout, on_dismiss=None):
    """A question in the bottom-right corner, like a notification: it doesn't
    grab focus from the call. buttons = [(label, action)]; the last is the
    default (Enter), an action of None just closes it. Esc, the close box and
    the `timeout` (s) run on_dismiss."""
    win = tk.Toplevel(root)
    hide_from_capture(win)
    win.title(title)
    win.resizable(False, False)
    win.attributes("-topmost", True)
    tk.Label(win, text=title, font=("Segoe UI", 11, "bold")).grid(
        row=0, column=0, sticky="w", padx=16, pady=(14, 0))
    tk.Label(win, text=body, justify="left", foreground="#333").grid(
        row=1, column=0, sticky="w", padx=16, pady=(2, 10))

    def dismiss():
        if win.winfo_exists():
            win.destroy()
            if on_dismiss:
                on_dismiss()

    def press(action):
        if action is None:
            return dismiss()
        win.destroy()
        action()

    btns = ttk.Frame(win)
    btns.grid(row=2, column=0, sticky="e", padx=16, pady=(0, 14))
    for label, action in buttons:
        ttk.Button(btns, text=label, command=lambda a=action: press(a)).pack(side="left", padx=4)
    win.bind("<Return>", lambda e: press(buttons[-1][1]))
    win.bind("<Escape>", lambda e: dismiss())
    win.protocol("WM_DELETE_WINDOW", dismiss)
    win.update_idletasks()
    area = ctypes.wintypes.RECT()          # the desktop minus the taskbar
    if not ctypes.windll.user32.SystemParametersInfoW(0x30, 0, ctypes.byref(area), 0):   # SPI_GETWORKAREA
        area.right, area.bottom = win.winfo_screenwidth(), win.winfo_screenheight() - 48
    win.geometry(f"+{area.right - win.winfo_width() - 16}+{area.bottom - win.winfo_height() - 16}")
    win.after(timeout * 1000, dismiss)


def show_warm_prompt(title, start, end):
    def go():
        with lock:
            state["warm_until"] = end + WARM_GRACE
        threading.Thread(target=warm_worker, daemon=True).start()
    verb = "starts" if start > datetime.now().astimezone() else "started"
    show_prompt("Meeting starting soon", f"“{title}” {verb} at {start:%H:%M}.\n"
                "Warm up the transcription server now, so the transcript\n"
                "doesn't have to wait for it afterwards?",
                [("Not now", None), ("Warm up", go)],
                timeout=max(60, int((start - datetime.now().astimezone()).total_seconds())))


def show_call_prompt(app):
    def never():
        settings["mic_ignore"].append(app)
        save_settings()
    name = app_name(app)
    show_prompt("Microphone in use", f"{name} is using your microphone.\nStart recording?",
                [(f"Never for {name}", never), ("Not now", None),
                 ("Record", lambda: None if state["recording"] else start_recording())], timeout=120)


_settings_win = None


def show_settings_dialog():
    """The meeting prompts as checkboxes in a window that stays open (a tray
    menu closes on every click). Each change is saved straight away."""
    global _settings_win
    if _settings_win is not None and _settings_win.winfo_exists():
        _settings_win.deiconify()
        _settings_win.lift()
        _settings_win.focus_force()
        return
    win = _settings_win = tk.Toplevel(root)
    hide_from_capture(win)
    win.title("Meeting prompts")
    win.resizable(False, False)
    win.attributes("-topmost", True)
    ttk.Label(win, text="Meeting prompts", font=("Segoe UI", 10, "bold")).grid(
        row=0, column=0, columnspan=2, sticky="w", padx=12, pady=(10, 4))

    options = [
        ("calendar_prompt", "Offer to warm up the server before meetings",
         "About 2 minutes ahead, from Outlook's meeting reminders."),
        ("call_prompt", "Offer to record when an app starts using the mic",
         "Teams, Zoom, a browser call: when you answer or join."),
        ("end_prompt", "Offer to stop when the call ends or changes",
         "While recording: the call ended, or you switched to another one."),
    ]
    for n, (key, label, hint) in enumerate(options):
        var = tk.BooleanVar(value=settings[key])

        def toggle(key=key, var=var):
            settings[key] = var.get()
            save_settings()

        ttk.Checkbutton(win, text=label, variable=var, command=toggle).grid(
            row=1 + 2 * n, column=0, columnspan=2, sticky="w", padx=12, pady=(6, 0))
        ttk.Label(win, text=hint, foreground="#666").grid(
            row=2 + 2 * n, column=0, columnspan=2, sticky="w", padx=(34, 12))

    silenced = ttk.Label(win, foreground="#666")
    silenced.grid(row=7, column=0, sticky="w", padx=12, pady=(12, 0))
    unsilence = ttk.Button(win, text="Ask again")
    unsilence.grid(row=7, column=1, sticky="e", padx=12, pady=(12, 0))

    def show_silenced():
        names = ", ".join(app_name(a) for a in settings["mic_ignore"])
        silenced.configure(text=f"Silenced apps: {names}" if names else "No silenced apps.")
        unsilence.configure(state="normal" if names else "disabled")

    def ask_again():
        settings["mic_ignore"].clear()
        save_settings()
        show_silenced()

    unsilence.configure(command=ask_again)
    show_silenced()
    ttk.Button(win, text="Close", command=win.destroy).grid(
        row=8, column=1, sticky="e", padx=12, pady=(12, 12))
    win.bind("<Escape>", lambda e: win.destroy())
    win.update_idletasks()
    w, h = win.winfo_width(), win.winfo_height()
    win.geometry(f"+{(win.winfo_screenwidth() - w) // 2}+{(win.winfo_screenheight() - h) // 3}")
    win.focus_force()


def show_end_prompt(kind, rec_id, old, new):
    """While recording: the call seems over ("ended"), or over with another one
    started ("switch"). Ignoring it keeps recording; nothing stops on its own."""
    def keep():
        with lock:
            if rec_watch["id"] == rec_id:
                if kind == "switch":             # the new call belongs to this recording too
                    rec_watch["known"] |= rec_watch["pending"]
                rec_watch.update(asked="kept" if kind == "ended" else None,
                                 pending=set(), active=time.monotonic())

    def ours():
        return state["recording"] and state["started"] == rec_id

    def stop():
        keep()                                   # settles the watch state; the recording ends anyway
        if ours():
            stop_recording()

    def restart():
        keep()
        if ours():
            state["restart"] = True              # record_thread_main starts the next one
            stop_recording()
        elif not state["recording"]:
            start_recording()

    if kind == "switch":
        what = (f"{old} closed the microphone and opened it again." if old == new
                else f"{old} stopped using the microphone and {new} started.")
        show_prompt("New call?", f"{what}\nLooks like you switched calls. What should happen to the recording?",
                    [("Keep recording", keep), ("Stop", stop), ("Stop and record the new call", restart)],
                    timeout=300, on_dismiss=keep)
    else:
        show_prompt("Call ended?", f"{old} stopped using the microphone.\nStop the recording?",
                    [("Keep recording", keep), ("Stop recording", stop)],
                    timeout=300, on_dismiss=keep)


def warm_worker():
    def progress(msg):
        print(msg)
        state["status"] = (str(msg).strip().splitlines() or [""])[0]   # tooltip and menu: one line
        refresh_icon()

    with lock:
        state["busy"] += 1
    refresh_icon()
    try:
        mr.warm_up_server(progress)
        notify("Transcription server ready", "It stays up for the meeting, and stops after the transcript.")
    except Exception as e:
        with lock:
            state["warm_until"] = None
        ui_q.put(("result", {"ok": False, "title": "Could not warm up the server",
                             "body": f"{type(e).__name__}: {e}"}))
    finally:
        with lock:
            state["busy"] -= 1
            if not state["busy"]:
                state["status"] = ""
        refresh_icon()


def watch_main():
    """Background loop behind the meeting prompts; asks the tk thread to show them."""
    cal = {"reminders": {}, "error": None}     # reminders: start -> title
    asked = set()                    # meeting starts already offered a warm-up
    seen = {}                        # mic_users() key -> last time it had the mic
    while True:
        try:
            now = time.monotonic()
            users = mic_users()
            new = sorted(u for u in users if u not in seen or now - seen[u] >= CALL_GAP)
            seen.update(dict.fromkeys(users, now))
            if settings["call_prompt"] and new and not state["recording"]:
                ui_q.put(("call_ask", {"app": new[0]}))
            recording_tick(users)
            calendar_tick(cal, asked)
            release_tick(meeting_on=bool(users))
        except Exception as e:
            print(f"watch: {type(e).__name__}: {e}")
        time.sleep(WATCH_EVERY)


def recording_tick(users):
    """While recording, watch the mic sessions of the call being recorded: all
    gone for CALL_GAP → "call ended?"; all gone with a new one open → "new call?".
    A recording started outside a call adopts the first call that comes along;
    an app joining alongside the call just becomes part of it."""
    with lock:
        if not (settings["end_prompt"] and state["recording"]):
            rec_watch["id"] = None
            return
        now, sessions = time.monotonic(), set(users.items())
        if rec_watch["id"] != state["started"]:  # a new recording
            rec_watch.update(id=state["started"], known=sessions, active=now, asked=None, pending=set())
            return
        known = rec_watch["known"]
        if sessions & known:
            rec_watch["active"] = now
            if rec_watch["asked"] == "kept":
                rec_watch["asked"] = None
        if rec_watch["asked"] in ("switch", "ended"):
            return                               # a prompt is open; its answer decides
        new = sessions - known
        if new and (not known or sessions & known):
            known |= new                         # first call of the recording, or someone joined alongside
            rec_watch["active"] = now
        elif new:
            rec_watch.update(asked="switch", pending=new)
            ui_q.put(("end_ask", {"kind": "switch", "rec_id": rec_watch["id"],
                                  "old": _names(known), "new": _names(new)}))
        elif known and not sessions and rec_watch["asked"] is None and now - rec_watch["active"] >= CALL_GAP:
            rec_watch["asked"] = "ended"
            ui_q.put(("end_ask", {"kind": "ended", "rec_id": rec_watch["id"],
                                  "old": _names(known), "new": ""}))


def _names(sessions):
    return " and ".join(sorted({app_name(app) for app, _ in sessions}))


def calendar_tick(cal, asked):
    if not settings["calendar_prompt"]:
        return
    now = datetime.now().astimezone()
    try:
        for start, title in outlook_reminders():
            cal["reminders"].setdefault(start, title)
        cal["error"] = None
    except Exception as e:
        if cal["error"] is None:             # say it once, not every check
            print(f"outlook reminders: {type(e).__name__}: {e}")
        cal["error"] = e
    for start in [s for s in cal["reminders"] if s < now - KEEP_REMINDERS]:
        del cal["reminders"][start]
    for start, title in sorted(cal["reminders"].items()):
        # keyed on the start time: two meetings at once need only one warm-up
        if start in asked or not -LATE_OFFER < start - now <= timedelta(seconds=WARMUP_LEAD):
            continue
        asked.add(start)
        end = start + MEETING_LENGTH
        if state["recording"]:
            continue
        if mr.server_healthy():
            with lock:                       # back-to-back meetings: keep a warm-up alive for this one too
                if state["warm_until"]:
                    state["warm_until"] = max(state["warm_until"], end + WARM_GRACE)
            continue
        ui_q.put(("warm_ask", {"title": title, "start": start, "end": end}))


def release_tick(meeting_on):
    """Stop a warm-up whose meeting is over without anything being recorded.
    meeting_on (an app still has the mic) means it ran past its assumed end:
    keep waiting."""
    with lock:
        until = state["warm_until"]
        if (not until or datetime.now().astimezone() < until or meeting_on
                or state["recording"] or state["busy"]):
            return
        state["warm_until"] = None
    if mr.release_idle_server(print):
        print("warm-up went unused — server stopped")


# ---------------------------------------------------------------- tray menu
def on_toggle(icon_, item):
    if state["recording"]:
        stop_recording()
    else:
        start_recording()


def on_pick_file(icon_, item):
    ui_q.put(("pick", {}))


def on_name_file(icon_, item):
    ui_q.put(("pick_names", {}))


def on_open_folder(icon_, item):
    try:
        os.makedirs(mr.OUTPUT_DIR, exist_ok=True)
        os.startfile(mr.OUTPUT_DIR)
    except Exception as e:
        print(f"open folder: {type(e).__name__}: {e}")


def on_settings(icon_, item):
    ui_q.put(("settings", {}))


def on_quit(icon_, item):
    ui_q.put(("quit", {}))        # the tk thread asks first if a transcription is running


def quit_app():
    """Quit, unless a running transcription should be kept. A recording is
    stopped and its WAV finalised first: the WAV trails real time by a few
    seconds (mr.TIMELINE_LAG), and the process exiting under it would cut off
    the end of the meeting. Returns False if the user cancelled."""
    if state["busy"]:
        with topmost_parent() as parent:
            if not messagebox.askyesno(
                    "Quit meeting recorder?",
                    "A transcription is still running and will be abandoned.\n"
                    "The audio stays saved; transcribe it again later from the tray menu.\n\n"
                    "Quit anyway?", icon="warning", default="no", parent=parent):
                return False
    state["quitting"] = True
    with lock:
        ev, th = state["stop_event"], state["rec_thread"]
        recording = state["recording"]
    if recording and ev:
        ev.set()
        th.join(10)
    try:
        icon.stop()
    except Exception:
        pass
    root.quit()
    return True


def build_menu():
    return pystray.Menu(
        pystray.MenuItem(lambda item: status_line(), None, enabled=False),
        pystray.Menu.SEPARATOR,
        pystray.MenuItem(
            lambda item: "■  Stop recording" if state["recording"] else "●  Start recording",
            on_toggle, default=True),
        pystray.MenuItem("Transcribe an existing recording…", on_pick_file),
        pystray.MenuItem("Name speakers in a transcript…", on_name_file),
        pystray.MenuItem("Open transcripts folder", on_open_folder),
        pystray.MenuItem("Meeting prompts…", on_settings),
        pystray.Menu.SEPARATOR,
        pystray.MenuItem("Quit", on_quit),
    )


# ---------------------------------------------------------------- health / heartbeat
# On 2026-10-01 the icon vanished from the taskbar while the process stayed alive,
# so the watchdog (which only checked for the process) saw nothing wrong. Now the
# tk thread re-adds a missing icon itself, and writes a heartbeat the watchdog uses
# to spot a hung tray: "<pid> <recording 0|1>", refreshed every HEALTH_EVERY seconds.
HEARTBEAT = os.path.join(_HERE, "tray.heartbeat")
HEALTH_EVERY = 30
_last_health = 0.0


def _icon_present():
    """NIM_MODIFY fails when the shell has no icon for our (hwnd, id)."""
    from pystray._util import win32 as w
    hwnd = getattr(icon, "_hwnd", None)
    if not hwnd:
        return True       # tray thread not up yet; nothing to judge
    return bool(w.Shell_NotifyIcon(w.NIM_MODIFY, w.NOTIFYICONDATAW(
        cbSize=ctypes.sizeof(w.NOTIFYICONDATAW), hWnd=hwnd, hID=id(icon),
        uFlags=w.NIF_TIP, szTip=icon.title)))


def health_tick():
    global _last_health
    now = time.monotonic()
    if now - _last_health < HEALTH_EVERY:
        return
    _last_health = now
    try:
        if not _icon_present():
            print(time.strftime("%Y-%m-%d %H:%M:%S"), "tray icon missing — re-adding it")
            icon._show()
    except Exception as e:
        print(f"health: icon check failed: {type(e).__name__}: {e}")
    try:
        with open(HEARTBEAT, "w") as f:
            f.write(f"{os.getpid()} {int(bool(state['recording']))}\n")
    except Exception:
        pass


# ---------------------------------------------------------------- tk pump loop
def pump():
    health_tick()
    if state["recording"]:
        refresh_icon()                    # the tooltip's running clock (only changes once a second)
    try:
        while True:
            kind, payload = ui_q.get_nowait()
            try:
                if kind == "quit":
                    if quit_app():
                        return
                elif kind == "ask":
                    show_transcribe_dialog(payload["wav"], payload.get("secs"),
                                           payload.get("peak_mic"), payload.get("peak_sys"))
                elif kind == "result":
                    show_result(payload["ok"], payload["title"], payload["body"], payload.get("folder"))
                elif kind == "pick":
                    pick_and_transcribe()
                elif kind == "name":
                    show_name_dialog(payload["txt"], payload.get("then"),
                                     payload.get("title", ""), payload.get("new", False))
                elif kind == "pick_names":
                    pick_transcript_to_name()
                elif kind == "warm_ask":
                    show_warm_prompt(payload["title"], payload["start"], payload["end"])
                elif kind == "call_ask":
                    show_call_prompt(payload["app"])
                elif kind == "settings":
                    show_settings_dialog()
                elif kind == "end_ask":
                    show_end_prompt(payload["kind"], payload["rec_id"], payload["old"], payload["new"])
            except Exception as e:
                # never let one bad dialog kill the pump (and with it every later click)
                import traceback
                print(f"pump: {kind} handler failed: {type(e).__name__}: {e}")
                traceback.print_exc()
    except queue.Empty:
        pass
    root.after(150, pump)


def pick_and_transcribe():
    with topmost_parent() as parent:
        path = filedialog.askopenfilename(
            parent=parent,
            title="Pick a recording to transcribe",
            initialdir=mr.AUDIO_DIR if os.path.isdir(mr.AUDIO_DIR) else None,
            filetypes=[("Audio", "*.wav *.mp3 *.m4a *.ogg *.opus *.flac *.webm *.aac"),
                       ("All files", "*.*")])
    print(f"pick: {path!r}")
    if path:
        show_transcribe_dialog(os.path.normpath(path))


def main():
    global icon, root
    load_settings()
    root = tk.Tk()
    root.withdraw()                       # no main window; we live in the tray
    icon = pystray.Icon("meeting_recorder", make_image("idle"), "Meeting recorder — idle", build_menu())
    _shown.update(kind="idle", menu=("idle", status_line()))
    icon.run_detached()                   # tray in its own thread
    root.after(150, pump)                 # tk owns the main thread (dialogs need it)
    threading.Thread(target=watch_main, daemon=True).start()   # the optional meeting prompts
    root.mainloop()


if __name__ == "__main__":
    main()
