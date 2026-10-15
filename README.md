# $Decompile

**$Decompile** is a Python-based executable analysis and decompilation workbench. It identifies how a supported program was built, selects a suitable decompiler, helps you recover and edit source-like files, and provides rebuild workflows where practical.

The application includes a dark desktop GUI and a command-line interface. It is designed primarily for analyzing Windows `.exe` and `.dll` files.

> **Important:** Decompilation is not the same as recovering the original source code. Results can be incomplete or approximate, especially for native machine-code programs and newer Python bytecode. Rebuilt applications may behave differently from the original.

## Features

- **Automatic file analysis** — identifies PE architecture, DLL status, compile timestamp, file size, SHA-256 hash, likely executable type, and possible UPX packing.
- **Multiple decompilation backends** — chooses a backend for .NET assemblies, PyInstaller-packaged Python programs, or native executables.
- **Tool discovery** — scans common locations for existing tools and can perform a slower, deeper scan of local drives.
- **On-demand tool installation** — downloads required tools into a `$Decompile` data directory instead of requiring every dependency to be installed globally.
- **PyInstaller archive extraction** — extracts bundled files and bytecode, then attempts to decompile selected Python modules.
- **Source editing** — browse the recovered project, open text files, edit and save them, and check Python syntax in the built-in editor.
- **Rebuild workflows** — rebuild Python projects with PyInstaller, .NET projects with `dotnet build`, and attempt native C builds using Zig.
- **Progress and logs** — displays operation output, reports progress, saves a log file, and supports cancelling active operations.
- **Settings and diagnostics** — remembers tool locations, scan preferences, Python recovery scope, and parallel decompilation settings.

## Supported targets and tools

| Target type | Detection / backend | Expected result | Rebuild support |
|---|---|---|---|
| .NET executable or assembly | ILSpy (`ilspycmd`) and the .NET SDK | A C# project and recovered `.cs` files | Yes, with `dotnet build` |
| PyInstaller-packaged Python executable | Built-in PyInstaller archive reader plus `pycdc`, `decompyle3`, or `uncompyle6`, depending on the bytecode version | Extracted files and attempted `.py` recovery | Yes, with PyInstaller |
| Native executable | Ghidra headless decompiler, with a Java JDK | C pseudocode and per-function output | Best-effort only; generated pseudocode usually needs manual repair |
| UPX-packed executable | Optional UPX utility before decompilation | Attempts to unpack the file before analysis | Depends on the underlying target type |

The program selects its backend from its analysis of the input. Installing every backend is not always necessary; use the **Tools** page or install only the tool needed for your file.

### Known limitations

- Recovered code can lack original comments, variable names, project structure, or other source-level information.
- Native decompilation produces pseudocode, not the original C or C++ source.
- Python bytecode compatibility depends on the decompiler. The program warns that support for some newer Python versions is incomplete; inspect recovered files carefully.
- External imports and non-code resources may need to be restored or supplied separately when rebuilding.
- Rebuilt Python executables use the Python runtime on the current computer and may not match the original runtime or environment.
- The built-in editor does not load files larger than 8 MiB; use an external editor for those files.
- Large tool installations, particularly Ghidra and its JDK, require additional disk space and an internet connection.

## Requirements

- **Python 3.10 or newer**.
- **Tkinter** for the desktop GUI. It is normally included with standard Python installers, but may need to be installed separately on some Linux distributions.
- An internet connection to download missing tools.
- Enough free disk space for any toolchains you install and the extracted project files.

The Python application itself uses only the Python standard library. The decompilers, compilers, SDKs, and rebuild tools are separate dependencies and are installed or discovered as needed.

## Getting started

1. Install Python 3.10 or newer. Make sure Tkinter is included if you want to use the GUI.
2. Save the program as `main.py` in a folder of your choice.
3. Open Command Prompt, PowerShell, or a terminal in that folder.
4. Start the desktop application:

   ```bash
   python main.py
   ```

5. Open **Tools** or run a tool scan to find dependencies already installed on your computer. Choose **Install** for the backend you need, or use **Install all missing** if you understand that this may download several large packages.
6. Open **Decompile**, select an `.exe` or `.dll`, review the file analysis, choose a Python recovery scope if applicable, and start decompilation.
7. Review the recovered files in **Rebuild**. Make edits, save them, check Python syntax when applicable, and try rebuilding if the target type supports it.

### Starting from a terminal when the GUI is unavailable

If Python reports that Tkinter is unavailable, install the Tk/Tcl component for your Python distribution or use the command-line interface below. On Debian/Ubuntu, the package is commonly available as `python3-tk`.

## Command-line usage

All commands are run from the folder containing `main.py`.

### Show installed tools

```bash
python main.py tools
```

### Scan for existing tools

```bash
python main.py scan
```

To search every local drive (this can be slow):

```bash
python main.py scan --deep
```

### Install tools

Install every missing tool:

```bash
python main.py install all
```

Install a particular tool by its key, for example:

```bash
python main.py install ilspycmd
python main.py install pycdc
python main.py install ghidra
```

Valid tool keys depend on the platform. The `tools` command lists the tools and their installation status.

### Analyze a file without decompiling it

```bash
python main.py analyze "C:\Path\To\app.exe"
```

Analysis reports the detected file type and identifies missing tools. It does not run the target application.

### Decompile a file

```bash
python main.py decompile "C:\Path\To\app.exe" -o "C:\Path\To\app_src"
```

If `-o` is omitted, the default output folder is named after the input file with `_src` appended.

For PyInstaller Python programs, `--scope` controls how much bytecode the program attempts to recover:

- `entry` — main/entry scripts only (default).
- `app` — entry scripts plus modules identified as belonging to the application.
- `all` — all recoverable bundled modules, including libraries.

Example:

```bash
python main.py decompile "C:\Path\To\app.exe" -o "app_src" --scope all
```

### Rebuild a recovered project

```bash
python main.py rebuild "app_src"
```

For Python projects, specify the entry script when needed, create a windowed executable, or install extra Python packages for the build:

```bash
python main.py rebuild "app_src" --entry main.py
python main.py rebuild "app_src" --entry main.py --windowed
python main.py rebuild "app_src" --entry main.py --pip requests pillow
```

The entry path is relative to the project's `source` folder. `--windowed` is relevant to PyInstaller builds and suppresses the console window. Additional options:

```text
--help       Show the command list or help for a command
--entry      Select the Python entry script for a rebuild
--pip        Install extra Python packages for a Python rebuild
```

For full option details, run:

```bash
python main.py --help
python main.py decompile --help
python main.py rebuild --help
```

## Output layout

A typical output directory resembles:

```text
app_src/
├── report.json       # Analysis and decompilation metadata
├── source/           # Recovered source or pseudocode files
├── extracted/        # Extracted PyInstaller contents, when applicable
├── _unpacked/        # Temporary copy used if UPX unpacking is attempted
├── .build/           # Intermediate rebuild files, when applicable
└── rebuilt/          # Rebuilt executable, assembly, or build output
```

Not every target creates every folder. `report.json` records details about the input and the decompilation operation. For PyInstaller targets, the original extracted `.pyc` files are retained in `extracted` to help with review when the decompiler output is incomplete.

## Tool storage and logs

`$Decompile` keeps its configuration, downloaded tools, temporary work files, and logs in its application data directory. The exact location depends on the operating system and Python installation. Use **Settings → Open data folder** or **About → Open data folder** in the GUI to open it.

The application log is named `dollardecompile.log` inside the data directory's `logs` folder. The GUI's **Logs** page can open or clear the displayed log.

## Safety and responsible use

- Analyze only software you own or are explicitly authorized to inspect.
- The application is designed to analyze the target rather than launch it, but that does **not** make an unknown executable or malformed archive risk-free.
- For files from an untrusted source, use an isolated virtual machine or disposable analysis environment. Do not run the target application just to test whether decompilation worked.
- Review decompiled code before compiling or executing it. Decompiled output may be incomplete, misleading, or contain unsafe behavior inherited from the original program.
- Downloaded third-party tools remain subject to their own licenses and terms.

## Troubleshooting

**The GUI does not open**

Check that you are using Python 3.10+ and that Tkinter is available. You can still use the CLI if Tkinter is missing.

**A required backend is missing**

Run `python main.py tools`, scan with `python main.py scan`, or install the needed dependency with `python main.py install <tool-key>`.

**A decompilation fails or looks incomplete**

Check the operation log and the tool's compatibility with the target format and bytecode version. Retry with a different Python recovery scope if appropriate, and compare output with the extracted bytecode or other available evidence.

**Rebuild fails**

Fix reported syntax or compiler errors first. For Python projects, choose the correct entry script and add missing third-party dependencies with `--pip` when required. Native C output usually needs substantial manual work and may not rebuild into a functionally equivalent executable.

**The tool scan takes too long**

The deep scan examines local drives and can be slow. Start with the normal scan unless you specifically need a deeper search.

## License

No license information is declared in the supplied source file. Add a `LICENSE` file and update this section before distributing the project if you intend to grant reuse or redistribution rights.
