import codecs
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import tkinter as tk
import webbrowser
from datetime import datetime
from tkinter import filedialog, font, messagebox

APP_NAME = "Notepad--"
APP_VERSION = "2.1"
REPO_URL = "https://github.com/MZGSZM/Notepad--"


def resource_path(relative_path):
    """Absolute path to a bundled resource, for dev and for PyInstaller.

    Uses the script directory rather than the CWD, so the icon still resolves
    when the app is launched from a file association or a different directory.
    """
    base_path = getattr(sys, "_MEIPASS", None)
    if base_path is None:
        try:
            base_path = os.path.dirname(os.path.abspath(__file__))
        except NameError:
            base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


class NotepadMinusMinus:
    # ----------------------------------------------------------------------
    # Theme / syntax tables
    # ----------------------------------------------------------------------
    THEMES = {
        "light": {
            "bg": "white", "fg": "black", "insert": "black",
            "gutter_bg": "#f0f0f0", "gutter_fg": "#808080",
            "status_bg": "#f0f0f0", "status_fg": "black",
            "widget_bg": "#f0f0f0", "widget_fg": "black",
            "entry_bg": "white", "entry_fg": "black",
            "sel_bg": "#0078D7", "sel_fg": "white",
            "keyword": "#0000cd", "string": "#a31515", "comment": "#008000",
        },
        "dark": {
            "bg": "#1e1e1e", "fg": "#d4d4d4", "insert": "#d4d4d4",
            "gutter_bg": "#252526", "gutter_fg": "#6a6a6a",
            "status_bg": "#252526", "status_fg": "#d4d4d4",
            "widget_bg": "#2d2d30", "widget_fg": "#d4d4d4",
            "entry_bg": "#1e1e1e", "entry_fg": "#d4d4d4",
            "sel_bg": "#0078D7", "sel_fg": "white",
            "keyword": "#569cd6", "string": "#ce9178", "comment": "#6a9955",
        },
    }

    # 'strings' controls whether quoted text is highlighted at all. Plain text
    # files get nothing, so prose with apostrophes is left alone.
    SYNTAX_RULES = {
        "python": {
            "keywords": r"\b(def|class|if|else|elif|import|from|return|for|while|in|is|not|and|or|"
                        r"try|except|finally|with|as|pass|break|continue|raise|yield|assert|del|"
                        r"lambda|global|nonlocal|async|await|True|False|None)\b",
            "comments": r"#[^\n]*",
            "strings": True,
        },
        "c_style": {
            "keywords": r"\b(int|float|double|char|bool|void|long|short|unsigned|signed|if|else|for|"
                        r"while|do|return|switch|case|default|break|continue|goto|struct|enum|union|"
                        r"typedef|class|public|private|protected|static|final|new|delete|this|import|"
                        r"package|namespace|using|function|var|let|const|null|true|false)\b",
            "comments": r"//[^\n]*|/\*.*?\*/",
            "strings": True,
        },
        "html": {
            "keywords": r"</?[a-zA-Z][a-zA-Z0-9:-]*(?:\s[^<>]*?)?/?>",
            "comments": r"<!--.*?-->",
            "strings": False,
        },
        "sql": {
            "keywords": r"\b(SELECT|FROM|WHERE|INSERT|INTO|UPDATE|SET|DELETE|CREATE|DROP|TABLE|VIEW|"
                        r"INDEX|ALTER|JOIN|INNER|OUTER|LEFT|RIGHT|FULL|ON|AS|GROUP|BY|HAVING|ORDER|"
                        r"ASC|DESC|LIMIT|OFFSET|VALUES|DISTINCT|UNION|AND|OR|NOT|NULL|PRIMARY|KEY)\b",
            "comments": r"--[^\n]*",
            "strings": True,
        },
        "shell": {
            "keywords": r"\b(if|then|else|elif|fi|for|while|do|done|case|esac|function|return|local|"
                        r"export|source|echo|exit|set|unset|read|shift|trap)\b",
            "comments": r"#[^\n]*",
            "strings": True,
        },
        "json": {
            "keywords": r"\b(true|false|null)\b",
            "comments": r"",
            "strings": True,
        },
        "generic": {"keywords": r"", "comments": r"", "strings": False},
    }

    EXTENSIONS = {
        ".py": "python", ".pyw": "python",
        ".c": "c_style", ".h": "c_style", ".cpp": "c_style", ".cc": "c_style",
        ".hpp": "c_style", ".java": "c_style", ".js": "c_style", ".jsx": "c_style",
        ".ts": "c_style", ".tsx": "c_style", ".cs": "c_style", ".go": "c_style",
        ".rs": "c_style", ".php": "c_style",
        ".html": "html", ".htm": "html", ".xml": "html", ".xhtml": "html", ".svg": "html",
        ".sql": "sql",
        ".sh": "shell", ".bash": "shell", ".zsh": "shell",
        ".json": "json",
    }

    ENCODINGS = [
        ("UTF-8", "utf-8"),
        ("UTF-8 with BOM", "utf-8-sig"),
        ("UTF-16 LE", "utf-16-le"),
        ("UTF-16 BE", "utf-16-be"),
        ("ANSI (latin-1)", "latin-1"),
    ]

    NEWLINES = [("Windows (CRLF)", "\r\n"), ("Unix (LF)", "\n"), ("Classic Mac (CR)", "\r")]

    # ----------------------------------------------------------------------
    # Construction
    # ----------------------------------------------------------------------
    def __init__(self, root):
        self.root = root
        self.root.title(APP_NAME)

        self.config_dir = self._get_config_dir()
        self.config_file = os.path.join(self.config_dir, "config.json")

        # --- document state ---
        self.filename = "Untitled"
        self.file_path = None
        self.is_dirty = False
        self.current_lang = "generic"
        self.encoding = "utf-8"
        self.newline = "\r\n" if os.name == "nt" else "\n"

        # --- view state ---
        self.is_dark_theme = tk.BooleanVar(value=False)
        self.show_line_numbers = tk.BooleanVar(value=False)
        self.syntax_highlighting = tk.BooleanVar(value=False)
        self.word_wrap = tk.BooleanVar(value=False)
        self.encoding_var = tk.StringVar(value=self.encoding)
        self.newline_var = tk.StringVar(value=self.newline)
        self.current_font_family = "Consolas"
        self.current_font_size = 12

        self._refresh_job = None
        self._icon_images = []          # keep PhotoImage refs alive
        self._compiled_pattern = None
        self._compiled_lang = None
        self.search_state = {"target": "", "replacement": "", "match_case": False}

        self._load_config()
        self.encoding_var.set(self.encoding)
        self.newline_var.set(self.newline)

        self._setup_icon()
        self._build_ui()
        self._build_menus()
        self._bind_events()

        self.apply_font()
        self.apply_theme()
        self.toggle_word_wrap()
        self.toggle_line_numbers()

        self.root.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.text_area.edit_modified(False)
        self._update_title()

        if len(sys.argv) > 1:
            self.load_file_content(sys.argv[1])
        else:
            self._refresh_view()

    def _setup_icon(self):
        self.icon_path = None
        try:
            if sys.platform.startswith("win"):
                path = resource_path("app_icon.ico")
                if os.path.exists(path):
                    self.icon_path = path
                    self.root.iconbitmap(path)
            else:
                path = resource_path("app_icon.png")
                if os.path.exists(path):
                    self.icon_path = path
                    img = tk.PhotoImage(file=path)
                    self._icon_images.append(img)
                    self.root.iconphoto(True, img)
        except Exception as exc:
            print(f"Icon load error: {exc}", file=sys.stderr)

    def _build_ui(self):
        self.status_bar = tk.Label(self.root, text="", bd=1, relief=tk.SUNKEN, anchor=tk.E, padx=10)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        self.main_frame = tk.Frame(self.root)
        self.main_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=1)
        self.main_frame.grid_rowconfigure(0, weight=1)
        self.main_frame.grid_columnconfigure(1, weight=1)

        # Gutter is a Canvas, not a second Text widget: the only way to keep
        # numbers aligned when word wrap turns one logical line into several
        # display lines (todo #1).
        self.gutter = tk.Canvas(self.main_frame, width=40, highlightthickness=0, takefocus=0)
        self.gutter.grid(row=0, column=0, sticky="ns")

        self.text_area = tk.Text(
            self.main_frame, undo=True, wrap=tk.NONE, autoseparators=True, maxundo=-1,
            yscrollcommand=self._on_text_yscroll, xscrollcommand=self._on_text_xscroll,
        )
        self.text_area.grid(row=0, column=1, sticky="nsew")

        self.scrollbar_y = tk.Scrollbar(self.main_frame, command=self._on_scrollbar_y)
        self.scrollbar_y.grid(row=0, column=2, sticky="ns")
        self.scrollbar_x = tk.Scrollbar(self.main_frame, orient=tk.HORIZONTAL,
                                        command=self.text_area.xview)
        self.scrollbar_x.grid(row=1, column=1, sticky="ew")

        for tag in ("keyword", "string", "comment"):
            self.text_area.tag_config(tag)

        geo = getattr(self, "_saved_geometry", None)
        self.root.geometry(geo if geo else "960x720")

    def _bind_events(self):
        self.text_area.bind("<KeyRelease>", lambda e: self._schedule_refresh())
        self.text_area.bind("<ButtonRelease>", lambda e: self._schedule_refresh(10))
        self.text_area.bind("<<Modified>>", self._on_modified)
        self.text_area.bind("<Configure>", lambda e: self._schedule_refresh(10))

        # Shortcuts are bound on the Text widget and return "break".
        # Binding them on root let Tk's default Text class bindings fire first:
        # Ctrl+O inserted a newline, Ctrl+H deleted a character, Ctrl+F/N/P
        # moved the cursor. Widget bindings run before class bindings, so
        # "break" now suppresses them.
        accel = {
            "<Control-n>": self.new_file,
            "<Control-N>": self.new_file,
            "<Control-o>": self.open_file,
            "<Control-O>": self.open_file,
            "<Control-s>": self.save_file,
            "<Control-S>": self.save_file,
            "<Control-Shift-S>": self.save_file_as,
            "<Control-p>": self.print_file,
            "<Control-P>": self.print_file,
            "<Control-f>": self.open_find_dialog,
            "<Control-F>": self.open_find_dialog,
            "<Control-h>": self.open_replace_dialog,
            "<Control-H>": self.open_replace_dialog,
            "<Control-g>": self.open_goto_dialog,
            "<Control-G>": self.open_goto_dialog,
            "<Control-a>": self.select_all,
            "<Control-A>": self.select_all,
            "<Control-z>": self.undo,
            "<Control-y>": self.redo,
            "<Control-Shift-Z>": self.redo,
            "<F3>": self.find_next_again,
            "<Shift-F3>": self.find_previous_again,
            "<F5>": self.insert_time_date,
        }
        for sequence, handler in accel.items():
            self.text_area.bind(sequence, self._as_break(handler))

    @staticmethod
    def _as_break(handler):
        def wrapper(event=None):
            handler()
            return "break"
        return wrapper

    # ----------------------------------------------------------------------
    # Scrolling, gutter, refresh
    # ----------------------------------------------------------------------
    def _on_text_yscroll(self, first, last):
        self.scrollbar_y.set(first, last)
        self._schedule_refresh(10)

    def _on_text_xscroll(self, first, last):
        self.scrollbar_x.set(first, last)

    def _on_scrollbar_y(self, *args):
        self.text_area.yview(*args)
        self._schedule_refresh(10)

    def _schedule_refresh(self, delay=60):
        """Coalesce view updates. Without this, every keystroke re-ran the
        regex pass and rebuilt the gutter over the whole document."""
        if self._refresh_job is not None:
            self.root.after_cancel(self._refresh_job)
        self._refresh_job = self.root.after(delay, self._refresh_view)

    def _refresh_view(self):
        self._refresh_job = None
        self.update_line_numbers()
        self.update_status_bar()
        self.highlight_syntax()

    def update_line_numbers(self):
        if not self.show_line_numbers.get():
            return
        self.gutter.delete("all")
        colors = self._colors()
        total = int(self.text_area.index("end-1c").split(".")[0])
        width = max(34, self.text_font.measure("0") * max(2, len(str(total))) + 12)
        if int(self.gutter.cget("width")) != width:
            self.gutter.config(width=width)

        index = self.text_area.index("@0,0")
        while True:
            dline = self.text_area.dlineinfo(index)
            if dline is None:
                break
            line_no = index.split(".")[0]
            self.gutter.create_text(width - 6, dline[1], anchor="ne", text=line_no,
                                    fill=colors["gutter_fg"], font=self.text_font)
            next_index = self.text_area.index(f"{index}+1line linestart")
            if next_index == index:
                break
            index = next_index
            if int(index.split(".")[0]) > total:
                break

    def toggle_line_numbers(self):
        if self.show_line_numbers.get():
            self.gutter.grid(row=0, column=0, sticky="ns")
            self.update_line_numbers()
        else:
            self.gutter.grid_remove()

    def toggle_word_wrap(self):
        wrapping = self.word_wrap.get()
        self.text_area.config(wrap=tk.WORD if wrapping else tk.NONE)
        if wrapping:
            self.scrollbar_x.grid_remove()
        else:
            self.scrollbar_x.grid(row=1, column=1, sticky="ew")
        self._schedule_refresh(10)

    # ----------------------------------------------------------------------
    # Syntax highlighting
    # ----------------------------------------------------------------------
    def detect_language(self):
        if not self.file_path:
            self.current_lang = "generic"
        else:
            _, ext = os.path.splitext(self.file_path)
            self.current_lang = self.EXTENSIONS.get(ext.lower(), "generic")
        self._compiled_pattern = None

    def _pattern(self):
        """Comments, strings and keywords are matched in a single alternation
        so the first match at a position wins. Previously each rule ran
        separately, so a '#' inside a string turned the rest of the line into
        a comment."""
        if self._compiled_pattern is not None and self._compiled_lang == self.current_lang:
            return self._compiled_pattern
        rules = self.SYNTAX_RULES.get(self.current_lang, self.SYNTAX_RULES["generic"])
        parts = []
        if rules.get("comments"):
            parts.append(f"(?P<comment>{rules['comments']})")
        if rules.get("strings"):
            parts.append(r"(?P<string>\"(?:\\.|[^\"\\\n])*\"|'(?:\\.|[^'\\\n])*')")
        if rules.get("keywords"):
            parts.append(f"(?P<keyword>{rules['keywords']})")
        self._compiled_pattern = re.compile("|".join(parts), re.MULTILINE | re.DOTALL) if parts else None
        self._compiled_lang = self.current_lang
        return self._compiled_pattern

    def highlight_syntax(self, event=None):
        # Only the visible window is scanned; it is re-run on scroll. A full
        # document pass on every keystroke made large files unusable.
        first = self.text_area.index("@0,0 linestart")
        last = self.text_area.index(f"@0,{self.text_area.winfo_height()} lineend +1line")
        for tag in ("keyword", "string", "comment"):
            self.text_area.tag_remove(tag, first, last)

        if not self.syntax_highlighting.get():
            return
        pattern = self._pattern()
        if pattern is None:
            return

        chunk = self.text_area.get(first, last)
        for match in pattern.finditer(chunk):
            tag = match.lastgroup
            if not tag:
                continue
            self.text_area.tag_add(tag, f"{first}+{match.start()}c", f"{first}+{match.end()}c")

    # ----------------------------------------------------------------------
    # Theme and config
    # ----------------------------------------------------------------------
    def _colors(self):
        return self.THEMES["dark" if self.is_dark_theme.get() else "light"]

    def apply_theme(self):
        c = self._colors()
        self.root.config(bg=c["bg"])
        self.text_area.config(bg=c["bg"], fg=c["fg"], insertbackground=c["insert"],
                              selectbackground=c["sel_bg"], selectforeground=c["sel_fg"],
                              inactiveselectbackground=c["sel_bg"])
        self.status_bar.config(bg=c["status_bg"], fg=c["status_fg"])
        self.gutter.config(bg=c["gutter_bg"])
        self.text_area.tag_config("keyword", foreground=c["keyword"])
        self.text_area.tag_config("string", foreground=c["string"])
        self.text_area.tag_config("comment", foreground=c["comment"])
        try:
            self.menu_bar.config(bg=c["widget_bg"], fg=c["widget_fg"])
        except tk.TclError:
            pass  # Windows ignores menu colours
        for window in (getattr(self, "find_window", None), getattr(self, "replace_window", None)):
            if window is not None and window.winfo_exists():
                self._style_window(window)
        self._schedule_refresh(10)

    def _style_window(self, window):
        c = self._colors()
        window.config(bg=c["widget_bg"])
        for child in window.winfo_children():
            cls = child.winfo_class()
            try:
                if cls in ("Label", "Checkbutton", "Radiobutton", "Frame"):
                    child.config(bg=c["widget_bg"], fg=c["widget_fg"])
                    if cls in ("Checkbutton", "Radiobutton"):
                        child.config(selectcolor=c["entry_bg"], activebackground=c["widget_bg"],
                                     activeforeground=c["widget_fg"])
                elif cls == "Button":
                    child.config(bg=c["widget_bg"], fg=c["widget_fg"],
                                 activebackground=c["entry_bg"], activeforeground=c["widget_fg"])
                elif cls in ("Entry", "Listbox", "Text"):
                    child.config(bg=c["entry_bg"], fg=c["entry_fg"], insertbackground=c["insert"])
            except tk.TclError:
                pass
            if child.winfo_children():
                self._style_window(child)

    def _get_config_dir(self):
        if sys.platform == "win32":
            base = os.environ.get("APPDATA") or os.path.join(os.path.expanduser("~"), "AppData", "Roaming")
            config_dir = os.path.join(base, "Notepad--")
        else:
            base = os.environ.get("XDG_CONFIG_HOME") or os.path.join(os.path.expanduser("~"), ".config")
            config_dir = os.path.join(base, "notepad--")
        try:
            os.makedirs(config_dir, exist_ok=True)
        except OSError:
            config_dir = tempfile.gettempdir()
        return config_dir

    def _load_config(self):
        if not os.path.exists(self.config_file):
            return
        try:
            with open(self.config_file, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except (OSError, ValueError) as exc:
            print(f"Could not load config: {exc}", file=sys.stderr)
            return
        self.is_dark_theme.set(bool(cfg.get("is_dark_theme", False)))
        self.show_line_numbers.set(bool(cfg.get("show_line_numbers", False)))
        self.syntax_highlighting.set(bool(cfg.get("syntax_highlighting", False)))
        self.word_wrap.set(bool(cfg.get("word_wrap", False)))
        self.current_font_family = cfg.get("font_family", self.current_font_family)
        try:
            self.current_font_size = max(6, min(96, int(cfg.get("font_size", self.current_font_size))))
        except (TypeError, ValueError):
            pass
        geometry = cfg.get("geometry")
        if isinstance(geometry, str) and re.fullmatch(r"\d+x\d+(?:[+-]-?\d+[+-]-?\d+)?", geometry):
            self._saved_geometry = geometry

    def _save_config(self):
        cfg = {
            "is_dark_theme": self.is_dark_theme.get(),
            "show_line_numbers": self.show_line_numbers.get(),
            "syntax_highlighting": self.syntax_highlighting.get(),
            "word_wrap": self.word_wrap.get(),
            "font_family": self.current_font_family,
            "font_size": self.current_font_size,
            "geometry": self.root.winfo_geometry(),
        }
        try:
            tmp = self.config_file + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=4)
            os.replace(tmp, self.config_file)
        except OSError as exc:
            print(f"Could not save config: {exc}", file=sys.stderr)

    # ----------------------------------------------------------------------
    # Menus
    # ----------------------------------------------------------------------
    def _build_menus(self):
        self.menu_bar = tk.Menu(self.root)
        self.root.config(menu=self.menu_bar)

        file_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New", accelerator="Ctrl+N", command=self.new_file)
        file_menu.add_command(label="Open...", accelerator="Ctrl+O", command=self.open_file)
        file_menu.add_command(label="Save", accelerator="Ctrl+S", command=self.save_file)
        file_menu.add_command(label="Save As...", accelerator="Ctrl+Shift+S", command=self.save_file_as)
        file_menu.add_separator()
        file_menu.add_command(label="Print", accelerator="Ctrl+P", command=self.print_file)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_exit)

        edit_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.menu_bar.add_cascade(label="Edit", menu=edit_menu)
        edit_menu.add_command(label="Undo", accelerator="Ctrl+Z", command=self.undo)
        edit_menu.add_command(label="Redo", accelerator="Ctrl+Y", command=self.redo)
        edit_menu.add_separator()
        edit_menu.add_command(label="Cut", accelerator="Ctrl+X",
                              command=lambda: self.text_area.event_generate("<<Cut>>"))
        edit_menu.add_command(label="Copy", accelerator="Ctrl+C",
                              command=lambda: self.text_area.event_generate("<<Copy>>"))
        edit_menu.add_command(label="Paste", accelerator="Ctrl+V",
                              command=lambda: self.text_area.event_generate("<<Paste>>"))
        edit_menu.add_command(label="Delete", accelerator="Del", command=self.delete_selection)
        edit_menu.add_separator()
        edit_menu.add_command(label="Find...", accelerator="Ctrl+F", command=self.open_find_dialog)
        edit_menu.add_command(label="Find Next", accelerator="F3", command=self.find_next_again)
        edit_menu.add_command(label="Replace...", accelerator="Ctrl+H", command=self.open_replace_dialog)
        edit_menu.add_command(label="Go To Line...", accelerator="Ctrl+G", command=self.open_goto_dialog)
        edit_menu.add_separator()
        edit_menu.add_command(label="Select All", accelerator="Ctrl+A", command=self.select_all)
        edit_menu.add_command(label="Time/Date", accelerator="F5", command=self.insert_time_date)

        format_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.menu_bar.add_cascade(label="Format", menu=format_menu)
        format_menu.add_checkbutton(label="Word Wrap", variable=self.word_wrap,
                                    command=self.toggle_word_wrap)
        format_menu.add_command(label="Font...", command=self.open_font_dialog)
        format_menu.add_separator()

        enc_menu = tk.Menu(format_menu, tearoff=0)
        format_menu.add_cascade(label="Encoding", menu=enc_menu)
        for label, value in self.ENCODINGS:
            enc_menu.add_radiobutton(label=label, value=value, variable=self.encoding_var,
                                     command=self._on_encoding_changed)
        nl_menu = tk.Menu(format_menu, tearoff=0)
        format_menu.add_cascade(label="Line Endings", menu=nl_menu)
        for label, value in self.NEWLINES:
            nl_menu.add_radiobutton(label=label, value=value, variable=self.newline_var,
                                    command=self._on_newline_changed)

        view_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.menu_bar.add_cascade(label="View", menu=view_menu)
        view_menu.add_checkbutton(label="Show Line Numbers", variable=self.show_line_numbers,
                                  command=self.toggle_line_numbers)
        view_menu.add_checkbutton(label="Dark Theme", variable=self.is_dark_theme,
                                  command=self.apply_theme)
        view_menu.add_checkbutton(label="Syntax Highlighting", variable=self.syntax_highlighting,
                                  command=lambda: self._schedule_refresh(0))

        help_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.menu_bar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label=f"About {APP_NAME}", command=self.show_about)

    def _on_encoding_changed(self):
        self.encoding = self.encoding_var.get()
        self._mark_dirty()
        self.update_status_bar()

    def _on_newline_changed(self):
        self.newline = self.newline_var.get()
        self._mark_dirty()
        self.update_status_bar()

    # ----------------------------------------------------------------------
    # Dirty state, title, status bar
    # ----------------------------------------------------------------------
    def _on_modified(self, event=None):
        if not self.text_area.edit_modified():
            return
        # Re-arm: <<Modified>> only fires on a False -> True transition.
        self.text_area.edit_modified(False)
        if not self.is_dirty:
            self.is_dirty = True
            self._update_title()
        self._schedule_refresh()

    def _mark_dirty(self):
        if not self.is_dirty:
            self.is_dirty = True
            self._update_title()

    def _clear_dirty(self):
        self.is_dirty = False
        self.text_area.edit_modified(False)
        self._update_title()

    def _update_title(self):
        star = "*" if self.is_dirty else ""
        self.root.title(f"{star}{self.filename} - {APP_NAME}")

    def update_status_bar(self, event=None):
        row, col = self.text_area.index(tk.INSERT).split(".")
        content = self.text_area.get("1.0", "end-1c")
        nl_name = {"\r\n": "CRLF", "\n": "LF", "\r": "CR"}.get(self.newline, "LF")
        enc_name = dict((v, k) for k, v in self.ENCODINGS).get(self.encoding, self.encoding)
        self.status_bar.config(
            text=f"Ln {row}, Col {int(col) + 1} | Words: {len(content.split())} | "
                 f"Chars: {len(content)} | {enc_name} | {nl_name}"
        )

    # ----------------------------------------------------------------------
    # File operations
    # ----------------------------------------------------------------------
    def new_file(self):
        if not self.check_save():
            return
        self.text_area.delete("1.0", tk.END)
        self.text_area.edit_reset()
        self.filename = "Untitled"
        self.file_path = None
        self.encoding = "utf-8"
        self.newline = "\r\n" if os.name == "nt" else "\n"
        self.encoding_var.set(self.encoding)
        self.newline_var.set(self.newline)
        self.detect_language()
        self._clear_dirty()
        self._refresh_view()

    def open_file(self):
        if not self.check_save():
            return
        path = filedialog.askopenfilename(
            filetypes=[("Text Documents", "*.txt"), ("All Files", "*.*")])
        if path:
            self.load_file_content(path)

    @staticmethod
    def _decode(raw):
        """Decode, reporting the encoding used. BOMs are consumed, not left in
        the text: decoding UTF-16 with the -le/-be codecs used to leave a
        U+FEFF as the first character of every such file."""
        if raw.startswith(codecs.BOM_UTF8):
            return raw[len(codecs.BOM_UTF8):].decode("utf-8", "replace"), "utf-8-sig"
        if raw.startswith(codecs.BOM_UTF16_LE):
            return raw[2:].decode("utf-16-le", "replace"), "utf-16-le"
        if raw.startswith(codecs.BOM_UTF16_BE):
            return raw[2:].decode("utf-16-be", "replace"), "utf-16-be"
        try:
            return raw.decode("utf-8"), "utf-8"
        except UnicodeDecodeError:
            return raw.decode("latin-1"), "latin-1"

    @staticmethod
    def _normalise_newlines(text):
        """Return (text with LF only, dominant original ending).

        The widget only ever holds LF. Keeping CR characters in the buffer was
        the root of 'extra newlines': on Windows, open(path, 'w') translates
        every LF to CRLF, so a file loaded as CRLF was written back as CR CRLF,
        gaining one CR per save. A run of CRs before a LF is collapsed, which
        also repairs files already damaged that way.
        """
        crlf = text.count("\r\n")
        lone_cr = text.count("\r") - crlf
        if crlf and not lone_cr:
            ending = "\r\n"
        elif lone_cr and not crlf:
            ending = "\r"
        elif crlf:
            ending = "\r\n"
        else:
            ending = "\n"
        text = re.sub(r"\r+\n", "\n", text)
        text = text.replace("\r", "\n")
        return text, ending

    def load_file_content(self, path):
        # Read and decode before touching any state, so a failed read cannot
        # leave file_path pointing at a file the buffer does not contain.
        try:
            with open(path, "rb") as f:
                raw = f.read()
        except OSError as exc:
            messagebox.showerror("Error", f"Could not read file: {exc}")
            return False

        content, encoding = self._decode(raw)
        content, ending = self._normalise_newlines(content)

        self.file_path = os.path.abspath(path)
        self.filename = os.path.basename(path)
        self.encoding = encoding
        self.newline = ending
        self.encoding_var.set(encoding)
        self.newline_var.set(ending)
        self.detect_language()

        self.text_area.delete("1.0", tk.END)
        self.text_area.insert("1.0", content)
        self.text_area.mark_set(tk.INSERT, "1.0")
        self.text_area.edit_reset()
        self._clear_dirty()
        self._refresh_view()
        return True

    def _encode_for_save(self, text):
        if self.encoding == "utf-8-sig":
            return codecs.BOM_UTF8 + text.encode("utf-8")
        if self.encoding == "utf-16-le":
            return codecs.BOM_UTF16_LE + text.encode("utf-16-le")
        if self.encoding == "utf-16-be":
            return codecs.BOM_UTF16_BE + text.encode("utf-16-be")
        return text.encode(self.encoding)

    def save_file(self):
        if self.file_path is None:
            return self.save_file_as()

        text = self.text_area.get("1.0", "end-1c").replace("\n", self.newline)
        try:
            data = self._encode_for_save(text)
        except UnicodeEncodeError:
            if not messagebox.askyesno(
                    APP_NAME,
                    f"This text cannot be saved as {self.encoding}. Save as UTF-8 instead?"):
                return False
            self.encoding = "utf-8"
            self.encoding_var.set("utf-8")
            data = text.encode("utf-8")

        # Write to a sibling temp file and rename, so an interrupted or failing
        # write cannot leave the original truncated.
        directory = os.path.dirname(self.file_path) or "."
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(dir=directory, prefix=".npmm-", suffix=".tmp")
            with os.fdopen(fd, "wb") as f:
                f.write(data)
            if os.path.exists(self.file_path):
                try:
                    shutil.copymode(self.file_path, tmp_path)
                except OSError:
                    pass
            os.replace(tmp_path, self.file_path)
            tmp_path = None
        except OSError as exc:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass
            messagebox.showerror("Error", f"Could not save file: {exc}")
            return False

        self._clear_dirty()
        self.update_status_bar()
        return True

    def save_file_as(self):
        path = filedialog.asksaveasfilename(
            initialfile=self.filename, defaultextension=".txt",
            filetypes=[("Text Documents", "*.txt"), ("All Files", "*.*")])
        if not path:
            return False
        self.file_path = os.path.abspath(path)
        self.filename = os.path.basename(path)
        self.detect_language()
        saved = self.save_file()
        if saved:
            self._schedule_refresh(0)
        return saved

    def check_save(self):
        if not self.is_dirty:
            return True
        response = messagebox.askyesnocancel(
            APP_NAME, f"Do you want to save changes to {self.filename}?")
        if response is None:
            return False
        if response is False:
            return True
        return self.save_file()

    def on_exit(self):
        if self.check_save():
            self._save_config()
            self.root.destroy()

    # ----------------------------------------------------------------------
    # Printing
    # ----------------------------------------------------------------------
    PS_PRINT_SCRIPT = r"""
param($filePath)
Add-Type -AssemblyName System.Drawing
Add-Type -AssemblyName System.Windows.Forms
$pd = New-Object System.Windows.Forms.PrintDialog
$pd.UseEXDialog = $true
if ($pd.ShowDialog() -eq 'OK') {
    $printDoc = New-Object System.Drawing.Printing.PrintDocument
    $printDoc.PrinterSettings = $pd.PrinterSettings
    $printDoc.DocumentName = "Notepad-- Document"
    $printDoc.PrintController = New-Object System.Drawing.Printing.StandardPrintController
    if (Test-Path $filePath) { $text = [System.IO.File]::ReadAllText($filePath, [System.Text.Encoding]::UTF8) } else { $text = "" }
    $font = New-Object System.Drawing.Font("Consolas", 12)
    $brush = [System.Drawing.Brushes]::Black
    $format = [System.Drawing.StringFormat]::GenericDefault
    $script:currChar = 0
    $printDoc.add_PrintPage({
        param($sender, $e)
        $printArea = New-Object System.Drawing.RectangleF($e.MarginBounds.Left, $e.MarginBounds.Top, $e.MarginBounds.Width, $e.MarginBounds.Height)
        $charsFitted = 0; $linesFilled = 0
        $textToPrint = $text.Substring($script:currChar)
        $e.Graphics.MeasureString($textToPrint, $font, $printArea.Size, $format, [ref]$charsFitted, [ref]$linesFilled)
        $e.Graphics.DrawString($textToPrint, $font, $brush, $printArea, $format)
        if ($charsFitted -le 0) { $e.HasMorePages = $false; return }
        $script:currChar += $charsFitted
        $e.HasMorePages = ($script:currChar -lt $text.Length)
    })
    try { $printDoc.Print() } catch { Write-Error "Printing Failed: $_" }
}
"""

    def print_file(self):
        content = self.text_area.get("1.0", "end-1c")
        if not content.strip():
            messagebox.showinfo(APP_NAME, "There is nothing to print.")
            return
        try:
            # Private 0700 directory instead of a fixed name in the shared temp
            # dir: the old code wrote a predictable path and then executed it,
            # which any other local user could replace between the two steps.
            job_dir = tempfile.mkdtemp(prefix="npmm-print-")
            job_file = os.path.join(job_dir, "document.txt")
            with open(job_file, "w", encoding="utf-8", newline="") as f:
                f.write(content.replace("\n", os.linesep))
        except OSError as exc:
            messagebox.showerror("Print Error", f"Could not prepare print job: {exc}")
            return
        threading.Thread(target=self._run_print_job,
                         args=(job_dir, job_file, self.filename), daemon=True).start()

    def _run_print_job(self, job_dir, job_file, job_name):
        try:
            if sys.platform == "win32":
                script_path = os.path.join(job_dir, "print_logic.ps1")
                with open(script_path, "w", encoding="utf-8") as f:
                    f.write(self.PS_PRINT_SCRIPT)
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                subprocess.run(
                    ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
                     "-File", script_path, "-filePath", job_file],
                    startupinfo=startupinfo, check=True)
            else:
                if shutil.which("lp") is None:
                    raise RuntimeError("'lp' was not found. Install CUPS to print.")
                subprocess.run(["lp", "-t", job_name, job_file], check=True)
        except Exception as exc:
            # exc is unbound once the except block ends, so bind the text now.
            message = str(exc)
            self.root.after(0, lambda: messagebox.showerror(
                "Print Error", f"Print process failed: {message}"))
        finally:
            shutil.rmtree(job_dir, ignore_errors=True)

    # ----------------------------------------------------------------------
    # Editing utilities
    # ----------------------------------------------------------------------
    def undo(self):
        try:
            self.text_area.edit_undo()
        except tk.TclError:
            self.root.bell()
        self._schedule_refresh(0)

    def redo(self):
        try:
            self.text_area.edit_redo()
        except tk.TclError:
            self.root.bell()
        self._schedule_refresh(0)

    def delete_selection(self):
        try:
            self.text_area.delete("sel.first", "sel.last")
        except tk.TclError:
            pass
        self._schedule_refresh(0)

    def select_all(self):
        self.text_area.tag_remove("sel", "1.0", tk.END)
        self.text_area.tag_add("sel", "1.0", "end-1c")  # not "end": that grabs the phantom newline
        self.text_area.mark_set(tk.INSERT, "1.0")
        return "break"

    def insert_time_date(self):
        self.text_area.insert(tk.INSERT, datetime.now().strftime("%I:%M %p %m/%d/%Y"))
        self._schedule_refresh(0)

    # ----------------------------------------------------------------------
    # Find / Replace / Go To
    # ----------------------------------------------------------------------
    def _search(self, target, start, match_case, backwards=False, wrap=True):
        """Return the start index of a match, or None. Wraps once."""
        if not target:
            return None
        kwargs = {"nocase": not match_case, "backwards": backwards}
        stop = "1.0" if backwards else tk.END
        pos = self.text_area.search(target, start, stopindex=stop, **kwargs)
        if not pos and wrap:
            pos = self.text_area.search(target, tk.END if backwards else "1.0",
                                        stopindex=start, **kwargs)
        return pos or None

    def _select_match(self, pos, length):
        end = f"{pos}+{length}c"
        self.text_area.tag_remove("sel", "1.0", tk.END)
        self.text_area.tag_add("sel", pos, end)
        self.text_area.mark_set(tk.INSERT, end)
        self.text_area.see(pos)
        self.text_area.focus_set()
        self._schedule_refresh(10)

    def find_next(self, target, match_case, backwards=False, announce=True):
        if not target:
            return False
        self.search_state["target"] = target
        self.search_state["match_case"] = match_case
        if backwards:
            try:
                start = self.text_area.index("sel.first")
            except tk.TclError:
                start = self.text_area.index(tk.INSERT)
        else:
            start = self.text_area.index(tk.INSERT)
        pos = self._search(target, start, match_case, backwards)
        if not pos:
            if announce:
                messagebox.showinfo(APP_NAME, f'Cannot find "{target}"', parent=self.root)
            return False
        self._select_match(pos, len(target))
        return True

    def find_next_again(self):
        target = self.search_state["target"]
        if not target:
            self.open_find_dialog()
            return
        self.find_next(target, self.search_state["match_case"])

    def find_previous_again(self):
        target = self.search_state["target"]
        if not target:
            self.open_find_dialog()
            return
        self.find_next(target, self.search_state["match_case"], backwards=True)

    def _selection_text(self):
        try:
            selected = self.text_area.get("sel.first", "sel.last")
        except tk.TclError:
            return ""
        return selected if "\n" not in selected else ""

    def _focus_entry(self, window, entry):
        """todo #3: the entry did not reliably take focus because the Toplevel
        was not mapped yet when focus_set() ran."""
        window.deiconify()
        window.lift()
        window.after(0, lambda: (window.focus_force(), entry.focus_set(),
                                 entry.selection_range(0, tk.END)))

    def open_find_dialog(self):
        if getattr(self, "find_window", None) is not None and self.find_window.winfo_exists():
            self.find_entry.delete(0, tk.END)
            self.find_entry.insert(0, self._selection_text() or self.search_state["target"])
            self._focus_entry(self.find_window, self.find_entry)
            return

        self.find_window = tk.Toplevel(self.root)
        self._set_window_icon(self.find_window)
        self.find_window.title("Find")
        self.find_window.resizable(False, False)
        self.find_window.transient(self.root)

        match_case = tk.BooleanVar(value=self.search_state["match_case"])

        tk.Label(self.find_window, text="Find what:").grid(row=0, column=0, padx=6, pady=6, sticky="e")
        self.find_entry = tk.Entry(self.find_window, width=28)
        self.find_entry.grid(row=0, column=1, padx=6, pady=6)
        self.find_entry.insert(0, self._selection_text() or self.search_state["target"])

        tk.Checkbutton(self.find_window, text="Match case", variable=match_case).grid(
            row=1, column=1, sticky="w", padx=4)

        def go(backwards=False):
            self.find_next(self.find_entry.get(), match_case.get(), backwards)

        tk.Button(self.find_window, text="Find Next", width=10,
                  command=lambda: go(False)).grid(row=0, column=2, padx=6, pady=4)
        tk.Button(self.find_window, text="Find Prev", width=10,
                  command=lambda: go(True)).grid(row=1, column=2, padx=6, pady=4)

        self.find_entry.bind("<Return>", lambda e: go(False))
        self.find_entry.bind("<Shift-Return>", lambda e: go(True))
        self.find_window.bind("<Escape>", lambda e: self.find_window.destroy())
        self._style_window(self.find_window)
        self._focus_entry(self.find_window, self.find_entry)

    def open_replace_dialog(self):
        if getattr(self, "replace_window", None) is not None and self.replace_window.winfo_exists():
            self._focus_entry(self.replace_window, self.replace_entry_find)
            return

        self.replace_window = tk.Toplevel(self.root)
        self._set_window_icon(self.replace_window)
        self.replace_window.title("Replace")
        self.replace_window.resizable(False, False)
        self.replace_window.transient(self.root)

        match_case = tk.BooleanVar(value=self.search_state["match_case"])

        tk.Label(self.replace_window, text="Find what:").grid(row=0, column=0, sticky="e", padx=4, pady=4)
        self.replace_entry_find = tk.Entry(self.replace_window, width=24)
        self.replace_entry_find.grid(row=0, column=1, padx=4, pady=4)
        self.replace_entry_find.insert(0, self._selection_text() or self.search_state["target"])

        tk.Label(self.replace_window, text="Replace with:").grid(row=1, column=0, sticky="e", padx=4, pady=4)
        entry_replace = tk.Entry(self.replace_window, width=24)
        entry_replace.grid(row=1, column=1, padx=4, pady=4)
        entry_replace.insert(0, self.search_state["replacement"])

        tk.Checkbutton(self.replace_window, text="Match case", variable=match_case).grid(
            row=2, column=1, sticky="w", padx=2)

        def current_selection_matches(target, case_sensitive):
            try:
                selected = self.text_area.get("sel.first", "sel.last")
            except tk.TclError:
                return False
            return selected == target if case_sensitive else selected.lower() == target.lower()

        def do_find():
            self.find_next(self.replace_entry_find.get(), match_case.get())

        def do_replace():
            """todo #2: 'Find Next' and 'Replace' were wired to the same
            function, so Find Next also replaced. Replace now only replaces the
            match that is currently selected, then advances."""
            target = self.replace_entry_find.get()
            replacement = entry_replace.get()
            self.search_state["replacement"] = replacement
            if not target:
                return
            if current_selection_matches(target, match_case.get()):
                start = self.text_area.index("sel.first")
                self.text_area.edit_separator()
                self.text_area.delete(start, "sel.last")
                self.text_area.insert(start, replacement)
                self.text_area.edit_separator()
                self.text_area.mark_set(tk.INSERT, f"{start}+{len(replacement)}c")
                self._mark_dirty()
                self._schedule_refresh(0)
            self.find_next(target, match_case.get(), announce=False)

        def do_replace_all():
            target = self.replace_entry_find.get()
            replacement = entry_replace.get()
            self.search_state["target"] = target
            self.search_state["replacement"] = replacement
            self.search_state["match_case"] = match_case.get()
            if not target:
                return
            count = 0
            pos = "1.0"
            self.text_area.edit_separator()
            while True:
                pos = self.text_area.search(target, pos, stopindex=tk.END,
                                            nocase=not match_case.get())
                if not pos:
                    break
                self.text_area.delete(pos, f"{pos}+{len(target)}c")
                self.text_area.insert(pos, replacement)
                pos = f"{pos}+{max(len(replacement), 0)}c"
                count += 1
            self.text_area.edit_separator()
            if count:
                self._mark_dirty()
                self._schedule_refresh(0)
            messagebox.showinfo(APP_NAME, f"Replaced {count} occurrence(s).",
                                parent=self.replace_window)

        tk.Button(self.replace_window, text="Find Next", width=11, command=do_find).grid(
            row=0, column=2, padx=6, pady=3)
        tk.Button(self.replace_window, text="Replace", width=11, command=do_replace).grid(
            row=1, column=2, padx=6, pady=3)
        tk.Button(self.replace_window, text="Replace All", width=11, command=do_replace_all).grid(
            row=2, column=2, padx=6, pady=3)

        self.replace_entry_find.bind("<Return>", lambda e: do_find())
        entry_replace.bind("<Return>", lambda e: do_replace())
        self.replace_window.bind("<Escape>", lambda e: self.replace_window.destroy())
        self._style_window(self.replace_window)
        self._focus_entry(self.replace_window, self.replace_entry_find)

    def open_goto_dialog(self):
        window = tk.Toplevel(self.root)
        self._set_window_icon(window)
        window.title("Go To Line")
        window.resizable(False, False)
        window.transient(window.master)

        tk.Label(window, text="Line number:").grid(row=0, column=0, padx=6, pady=8, sticky="e")
        entry = tk.Entry(window, width=10)
        entry.grid(row=0, column=1, padx=6, pady=8)
        entry.insert(0, self.text_area.index(tk.INSERT).split(".")[0])

        def go():
            try:
                line = int(entry.get())
            except ValueError:
                self.root.bell()
                return
            total = int(self.text_area.index("end-1c").split(".")[0])
            line = max(1, min(line, total))
            self.text_area.mark_set(tk.INSERT, f"{line}.0")
            self.text_area.see(f"{line}.0")
            self.text_area.focus_set()
            window.destroy()
            self._schedule_refresh(0)

        tk.Button(window, text="Go", width=8, command=go).grid(row=0, column=2, padx=6)
        entry.bind("<Return>", lambda e: go())
        window.bind("<Escape>", lambda e: window.destroy())
        self._style_window(window)
        self._focus_entry(window, entry)

    # ----------------------------------------------------------------------
    # Fonts, icons, about
    # ----------------------------------------------------------------------
    def apply_font(self):
        self.text_font = font.Font(family=self.current_font_family, size=self.current_font_size)
        self.text_area.configure(font=self.text_font)
        self._schedule_refresh(10)

    def open_font_dialog(self):
        window = tk.Toplevel(self.root)
        self._set_window_icon(window)
        window.title("Font")
        window.geometry("420x320")
        window.transient(self.root)

        frame_family = tk.Frame(window)
        frame_family.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        frame_size = tk.Frame(window)
        frame_size.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)
        tk.Label(frame_family, text="Font:").pack(anchor="w")
        tk.Label(frame_size, text="Size:").pack(anchor="w")

        families = sorted(set(font.families()))
        list_family = tk.Listbox(frame_family, exportselection=False)
        scrollbar_fam = tk.Scrollbar(frame_family, command=list_family.yview)
        list_family.config(yscrollcommand=scrollbar_fam.set)
        scrollbar_fam.pack(side=tk.RIGHT, fill=tk.Y)
        list_family.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        for family in families:
            list_family.insert(tk.END, family)
        if self.current_font_family in families:
            idx = families.index(self.current_font_family)
            list_family.selection_set(idx)
            list_family.see(idx)

        sizes = [8, 9, 10, 11, 12, 14, 16, 18, 20, 22, 24, 26, 28, 36, 48, 72]
        list_size = tk.Listbox(frame_size, width=8, exportselection=False)
        list_size.pack(fill=tk.BOTH, expand=True)
        for size in sizes:
            list_size.insert(tk.END, str(size))
        if self.current_font_size in sizes:
            idx = sizes.index(self.current_font_size)
            list_size.selection_set(idx)
            list_size.see(idx)

        def on_ok():
            selection = list_family.curselection()
            if selection:
                self.current_font_family = list_family.get(selection[0])
            selection = list_size.curselection()
            if selection:
                self.current_font_size = int(list_size.get(selection[0]))
            self.apply_font()
            window.destroy()

        btn_frame = tk.Frame(window)
        btn_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=10)
        tk.Button(btn_frame, text="Cancel", command=window.destroy, width=10).pack(side=tk.RIGHT, padx=10)
        tk.Button(btn_frame, text="OK", command=on_ok, width=10).pack(side=tk.RIGHT, padx=10)
        self._style_window(window)

    def _set_window_icon(self, window):
        try:
            if not self.icon_path or not os.path.exists(self.icon_path):
                return
            if sys.platform.startswith("win"):
                window.iconbitmap(self.icon_path)
            else:
                img = tk.PhotoImage(file=self.icon_path)
                self._icon_images.append(img)   # without a kept reference the
                window.iconphoto(False, img)    # image is collected immediately
        except tk.TclError:
            pass

    def show_about(self):
        window = tk.Toplevel(self.root)
        self._set_window_icon(window)
        window.title(f"About {APP_NAME}")
        window.resizable(False, False)
        window.transient(self.root)

        tk.Label(window, text=f"{APP_NAME} v{APP_VERSION}",
                 font=("Arial", 12, "bold")).pack(padx=30, pady=(15, 5))
        tk.Label(window, text="A recreation of the classic Notepad in Python.").pack(padx=20)

        link_font = font.Font(window, family="Arial", size=10, underline=True)
        link = tk.Label(window, text="View on GitHub", fg="#3794ff", cursor="hand2", font=link_font)
        link.pack(pady=5)
        link.bind("<Button-1>", lambda e: webbrowser.open(REPO_URL))

        tk.Button(window, text="Close", command=window.destroy).pack(pady=10)
        self._style_window(window)
        link.config(fg="#3794ff")


def main():
    root = tk.Tk()
    NotepadMinusMinus(root)
    root.mainloop()


if __name__ == "__main__":
    main()
