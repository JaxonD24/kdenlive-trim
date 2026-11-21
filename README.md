# kdenlive-trim

Trims each video in a Kdenlive project to the frames the timeline uses, rewrites the timeline to match, and gathers everything into a self-contained archive. Cuts are frame-exact and verified, with no re-encoding, and speed-changed clips are handled. Run it from the control dashboard in a terminal window, which also predicts the space saved, or straight from the command line.

The original project and media are never changed or deleted.

This tool uses AI-generated code.

## What it does

For each video on the timeline it:

1. Creates a copy of the project file.
2. Works out exactly which source frames are used, including speed-changed (timewarp) and reversed clips.
3. Cuts a new file holding only that range. Video is stream-copied, so there is no quality loss.
4. Checks the cut against the original, frame by frame.
5. Updates the clip's in/out points, effects, markers, zones and proxy in the new project file.

Audio, images, titles, wipes, slideshows and videos that are not worth trimming are copied unchanged.

By default, a video is only trimmed if that removes at least 10% of it; otherwise it is copied whole. Change this with **Minimum saving** (at 0, anything that saves at least one frame is trimmed).

If the project has been moved since it was last saved (the folder it was saved in no longer exists), the script looks for its files next to the project file, the same way Kdenlive does.

## Requirements

- Kdenlive projects. Tested with Kdenlive 26.08.0.
- Python 3.7 or newer. Standard library only, nothing to install with pip.
- ffmpeg and ffprobe, either on your `PATH` or set with **ffmpeg program** and **ffprobe program** in the control dashboard.
- Write access to the output folder.
- Free space for the trimmed videos plus everything copied unchanged.
- The control dashboard uses Python's built-in curses, included on macOS and Linux, so there is nothing extra to install. The command line works without it.

## Quick start

1. Open the control dashboard:

   ```bash
   python3 kdenlive-trim.py
   ```

2. Press Enter on **Project** and choose your `.kdenlive` file. The output goes to `Archive` next to the project unless you choose another folder.
3. Set any options, then press `s` to scan. This writes nothing and predicts the space you'll save. Press `w` to see what each option would change.
4. Press `r` to run. The progress dashboard follows the run. When it finishes, check that the summary says **Self-contained** and lists no failures.
5. Open the new project in Kdenlive (it's at `Archive/My Project.kdenlive`, next to the original) and play through the timeline.
6. Check for any mistakes or issues, and once happy, delete or move the original media.

Prefer the command line? Preview the plan (this writes nothing), then run it:

```bash
python3 kdenlive-trim.py "My Project.kdenlive" --report
python3 kdenlive-trim.py "My Project.kdenlive"
```

See [Command line options](#command-line-options) for everything else.

## Control dashboard

Run with no project, or with `--gui`, and `kdenlive-trim.py` opens the control dashboard in the terminal. It lets you browse for the project and output folder, set every option, save your defaults, predict the saving before running, and then run the trim with the progress dashboard.

```bash
python3 kdenlive-trim.py
python3 kdenlive-trim.py --gui "My Project.kdenlive"
python3 kdenlive-trim.py --gui "My Project.kdenlive" --handles 1
```

Options given with `--gui` are set for that session only, in place of your saved defaults; Save defaults keeps them. `--gui` takes only a project, `--out-dir` and the control dashboard's own options. Others, such as `--report` or `--complete`, are refused with a message saying so.

The control dashboard has Project and Output at the top and the Savings prediction at the bottom. In between, Options are on the left with Actions underneath, and About is on the right. In a smaller window, Options and Actions sit side by side.

- **Project and Output:** press Enter to browse. In the browser, `~` goes home, `v` goes to `/Volumes` (network shares), `g` types a path and `/` filters by name.
- **Options:** every switch from the [Command line options](#command-line-options) table. The Left and Right arrows change the highlighted one, and Enter types a value for numbers. Options marked `*` differ from the script's defaults.
- **About:** explains the highlighted option or action, with its pros and cons and, after a scan, what changing it would do.
- **Actions:** everything the control dashboard can do. Choose one with the arrows and Enter, or press its key from anywhere on the control dashboard.
- **Savings prediction:** after a scan, the size of the original files and of the result, the saving, how many files are trimmed and copied, and how much data the run will read and write.

| Key | Action | What it does |
| --- | --- | --- |
| `s` | Scan | Reads a little of each video and writes nothing, then predicts the saving with your options. Over a network share this can take a few minutes. |
| `w` | What-if | A table of every other value of each option with its predicted saving and data to move. Enter on a row applies that change. |
| `f` | Files | What will happen to each file (trimmed, copied or left where it is), with its size before and after. |
| `r` | Run | Runs the trim with the progress dashboard, then comes back to the control dashboard. Ctrl-C stops it cleanly. If the output folder already has an archive of this project, Run offers to complete it instead, adding only the files that are missing. |
| `c` | Command | Shows the command line for your choices, to keep or run yourself. It can be copied to the clipboard. |
| `d` | Save defaults | Saves the current options as your defaults, loaded every time the control dashboard starts. |
| `b` | Reset options | Puts every option back to the script's built-in defaults. |
| `?` | Help | Keys, the browser, and how the prediction works. |
| `q` | Quit | Leaves the control dashboard. The last project is remembered for next time. |

The prediction updates instantly as you change options. Changing Handles or Cut search window after a scan only estimates their effect, so scan again for exact figures. Data to read and write is what sets the run time, especially over a network share, and is a rougher estimate.

Questions, errors and results open in a box in the middle of the window: use the arrows or `y` and `n` to answer, Enter to confirm and Esc to cancel.

Your defaults are saved in `kdenlive-trim.json`, next to `kdenlive-trim.py`, so each copy of the program keeps its own settings.

When the control dashboard starts, the bar at the bottom says where your settings came from: loaded from `kdenlive-trim.json` (with how many options differ from the built-in defaults, marked `*`), no saved settings yet, or that the file could not be read. In that last case the built-in defaults are used and the file is left as it is until you choose Save defaults. The bar also says if `--gui` set any options. The note goes away at the next key.

Text size is set by the terminal app. In macOS Terminal, Cmd + makes it bigger, Cmd - smaller and Cmd 0 resets it. Both dashboards fit themselves to the window.

## Progress dashboard

While a run is going, the terminal shows the progress dashboard. The same detail is written to `Archive/kdenlive_trim.log`. On a Mac the computer is kept awake until the run ends.

- **Overall:** total progress, elapsed time and time left, plus counts of files trimmed, copied, problems and space saved so far.
- **Now:** the file being worked on. For a trim, a bar shows which part of the clip is kept (solid) and dropped (dots).
- **Step:** what is happening to that file: Cutting, Checking frames (or Checking samples when **Checking** is set to quick), Trimming proxy, or Copying.
- **Recent:** the last few results, marked OK, COPY, SKIP, NOTE or FAIL.

When it finishes, a summary is printed:

- **Trimmed / Copied:** how many files and how much space was saved.
- **Total:** everything the archive replaces (original media, proxies, images, other files and the project file) against the size of the archive folder, with the space saved in GB and as a percentage.
- **note:** something worth knowing about a file, such as a start that could not be trimmed, an effect or marker adjusted to fit, or a proxy you need to rebuild.
- **not included:** a file that could not be trimmed or copied. The new project still points at the original.
- **Self-contained** or **NOT self-contained:** whether the new project uses anything outside the archive folder. If not, the outside files are listed.
- **Original folders:** each source folder marked NOT USED (the new project no longer needs it) or STILL USED.

## Command line options

The only required argument is the project file. With no options it trims, checks every frame, and copies everything into `Archive`.

| Option | Default | What it does |
| --- | --- | --- |
| `--report` | off | Analyses the project and prints the plan for each file. Writes nothing. |
| `--report-json FILE` | off | Analyses the project like `--report` and writes the results as JSON to FILE. The control dashboard uses this to predict savings; you don't need it yourself. |
| `--complete` | off | Finishes an earlier archive of this project instead of starting again. Brings in only the files its project still uses from outside the archive (for example after a failed copy) and updates that project, after saving a backup of it as `.bak`. Files already in the archive are left as they are. Give the original project as usual, or the archive's own project file. |
| `--gui` | off | Opens the control dashboard instead of running, which is also what happens with no arguments. A project and any of the control dashboard's options (and `--out-dir`) given with it are set in the control dashboard for that session, in place of your saved defaults. Options the control dashboard doesn't have, such as `--report`, are refused. |
| `--out-dir FOLDER` | `Archive` next to the project | Where the archive is written. |
| `-o FILE`, `--output FILE` | Original name, inside the output folder | Path of the new project file. |
| `--handles SECONDS` | 0 | Keeps this much extra footage before and after each used range, so you can still extend clips later. |
| `--min-saving PERCENT` | 10 | A video that would shrink by less than this is copied whole instead of trimmed. A video the timeline uses whole is always copied, even at 0, because trimming it would save nothing. |
| `--long-gop copy` or `skip` | `copy` | For H.264/HEVC and similar. `copy` cuts at the nearest earlier keyframe, keeping a little extra. `skip` never trims these files, it copies them whole. |
| `--audio lossless` or `copy` | `lossless` | `lossless` stores compressed audio (AAC etc.) as PCM so the cut is sample accurate, at the cost of bigger audio. `copy` keeps the original codec, smaller but the start can be off by up to about 21 ms. PCM audio always stays PCM. |
| `--proxies trim` or `drop` | `trim` | `trim` trims or copies proxy clips into `proxy/`. `drop` removes proxy links so you rebuild them in Kdenlive. |
| `--search-seconds SECONDS` | 30 | How far before the used range to look for a cut point that keeps speed-changed clips frame exact. |
| `--no-copy-unchanged` | off | Writes only the trimmed videos. Everything else stays where it is and the new project points back at it, so the result is not self-contained. |
| `--quick-check` | off | Checks each cut's frame count, its first and last 2 seconds and three 1-second samples, instead of every frame. Much less reading over a network share, slightly less certainty. |
| `--allow-drift` | off | For speed-changed or frame-rate-converted clips, accepts a tighter cut where up to 1% of the clip's frames show the neighbouring source frame. Trims more, but those frames are not exact. |
| `--plain` | off | Prints a plain scrolling log instead of the progress dashboard. Used automatically when output is redirected to a file. |
| `--ffmpeg PATH`, `--ffprobe PATH` | found on `PATH` | Use specific ffmpeg and ffprobe programs. |
| `-h`, `--help` | | Shows the built-in help. |

## Examples

```bash
# Preview only, nothing written
python3 kdenlive-trim.py "My Project.kdenlive" --report

# Standard run: trim, full check, copy everything into Archive/
python3 kdenlive-trim.py "My Project.kdenlive"

# On a network share: lighter checking to cut down on reading
python3 kdenlive-trim.py "My Project.kdenlive" --quick-check

# Keep 1 second of spare footage either side of each clip
python3 kdenlive-trim.py "My Project.kdenlive" --handles 1

# Write the archive to another drive
python3 kdenlive-trim.py "My Project.kdenlive" --out-dir "/Volumes/Backup/My Project Archive"

# Skip proxies and rebuild them in Kdenlive afterwards
python3 kdenlive-trim.py "My Project.kdenlive" --proxies drop

# Smallest output, accepting the trade-offs described under Command line options
python3 kdenlive-trim.py "My Project.kdenlive" --audio copy --allow-drift

# Finish an earlier archive after a failed copy, once the cause is fixed
python3 kdenlive-trim.py "My Project.kdenlive" --complete

# Open the control dashboard with a project and an option already set
python3 kdenlive-trim.py --gui "My Project.kdenlive" --handles 1
```

## What is archived

Everything goes into one folder, `Archive` next to the project file by default, laid out like a Kdenlive project archive. Folders are only created when something goes in them.

| In `Archive` | Holds |
| --- | --- |
| `<project name>.kdenlive` | The new project, pointing only at files in this folder |
| `videos/` | Trimmed videos, plus videos copied unchanged |
| `sounds/` | Audio files such as music and voice-over |
| `images/` | Still images, including images used inside titles |
| `proxy/` | Proxy clips, trimmed to match their videos |
| `slideshows/` | Image sequences |
| `texts/` | Title templates |
| `lumas/` | Custom wipe files |
| `others/` | Anything else the project uses, such as LUT or effect files |
| `kdenlive_trim.log` | Full log of the run |

Paths inside the new project are relative, so you can move or rename the whole folder. Files keep their original names, except that an MP4 whose audio is converted to PCM is saved as `.mov`.

## Safety and troubleshooting

The script only reads the original project and media. It never changes or deletes them.

- **Ctrl-C** stops the run cleanly. Partial files are removed and no new project is written. Files that were already finished stay in `Archive`, so delete that folder before running again.
- **A cut that fails its check** is thrown away and the original video is copied whole instead. You lose the saving for that file, not the footage.
- **Every copy is checked** against the original: its size, and its first and last megabyte. A copy that doesn't match is tried once more. If it fails again, the file is left out, the new project keeps using the original, and the summary says NOT self-contained.
- **If the log can't be written** partway through (for example the network share drops out), the run carries on and the summary says the log is incomplete. Keep that summary.
- **Before deleting originals**, open the new project in Kdenlive and play it through. The script checks the files, but it can't open Kdenlive for you.

| You see | Why | What to do |
| --- | --- | --- |
| The output folder already has files from an earlier run | `Archive` is left over from a previous or interrupted run | Delete or move it, or choose another output folder |
| Cannot write to ... | No write permission, or the share is mounted read-only | Fix the share permissions for your user, or choose another output folder |
| Cannot find ffmpeg / ffprobe | Not installed or not on `PATH` | Install ffmpeg, or set **ffmpeg program** and **ffprobe program** in the control dashboard |
| Nothing to trim or copy: N file(s) used by the project were not found | The media is not where the project says it is, for example a network share that is not mounted | Check the path shown. Mount the share, or put the media back where the project expects it |
| Refusing to overwrite the original project file | The output folder is the project's own folder, so the new project would replace the original | Choose a different output folder |
| SKIP: only N% would be saved | Below **Minimum saving** | Nothing, the file is copied whole. Lower **Minimum saving** to trim it anyway |
| SKIP: the timeline uses the whole file | Every frame of the video is used, so a trim would save nothing | Nothing, the file is copied whole |
| SKIP: no video stream | Audio-only file | Nothing, audio is copied whole into `sounds/` |
| note: start not trimmed, no cut point lines up exactly | A speed-changed clip has no frame-exact cut point near its start | Accept it (the end is still trimmed), raise **Cut search window**, or set **Allow drift** to yes |
| note: proxy link removed, rebuild it in Kdenlive | The proxy was missing or could not be trimmed | Regenerate that clip's proxy in Kdenlive |
| FAIL on a trim | The cut did not pass its check | Nothing, the original is copied whole instead |
| FAIL ... copy failed: copy does not match the original, twice | The copy read back differently from the original, usually a network share or disk problem | Check the share or disk, then Run again and choose **Complete it** to bring that file in. Keep the original until then |
| NOT self-contained | A file could not be copied, or **Copy other files** was set to no | Check the listed files before removing any originals |
| `--complete` finishes an archive made by this script, and there is none at ... | No archive of this project was found in the output folder | Use the same `--out-dir` as the first run, or give the archive's own project file. To start again instead, run without `--complete` |
| The log file could not be written | The share or disk failed while the log was being written | Nothing for the run, it carries on. Keep the printed summary and check the share or disk |
| The control dashboard needs a terminal window | `kdenlive-trim.py` was started with no project from something that is not a terminal, such as a script or a scheduled task | Give a project and options to run without the control dashboard |
| `--report` can't be used with `--gui` | `--gui` takes only a project, `--out-dir` and the control dashboard's own options | Leave out `--gui` to use those options, or use Scan and Run in the control dashboard |
| Could not read `kdenlive-trim.json` | The settings file is damaged or can't be read | The control dashboard uses the built-in defaults and leaves the file alone. Save defaults (`d`) replaces it |
