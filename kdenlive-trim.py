#!/usr/bin/env python3
"""
kdenlive-trim.py - final archive for a Kdenlive project: trims every video to the parts the
timeline uses and gathers everything else the project needs into one self-contained folder.

For every video file used on the project's timeline(s) it:
  1. works out exactly which source frames are used, including speed-changed
     (timewarp) and reversed clips, using the same frame maths as MLT,
  2. cuts a new file holding only that range with ffmpeg (video is stream-copied,
     so there is no generational loss; audio is stored as PCM so the cut is
     sample accurate),
  3. verifies the cut packet-by-packet against the original (every used frame by
     default; --quick-check compares the frame count, the first and last 2 seconds
     and three 1-second samples instead),
  4. updates clip in/out points, effect ranges, markers, zones, file hashes and proxies.
Everything it does not trim (other videos, audio, images, slideshows, images inside
titles, title templates, wipes, effect files and proxies) is copied unchanged.

Output, laid out like a Kdenlive project archive:
  <project folder>/Archive/<project>.kdenlive
                          /videos  /sounds  /images  /proxy  (+ slideshows, texts, lumas, others)
                          /kdenlive_trim.log
Paths inside the new project are relative, so the folder can be moved or renamed.
While it runs, the progress dashboard shows how it is going (use --plain for a plain log).

The original project file and the original media are never modified or deleted.

Examples:
  python3 kdenlive-trim.py "Day 046.kdenlive" --report          # analyse only, no files written
  python3 kdenlive-trim.py "Day 046.kdenlive"                   # trim + archive into "Archive/"
  python3 kdenlive-trim.py "Day 046.kdenlive" --handles 1       # keep 1 s of spare footage either side

With no arguments, or with --gui, it opens the control dashboard in the terminal instead: browse for the
project and output folder, set every option (with what each one does and its pros and cons), save your defaults,
predict the saving from a quick scan (--report-json), and run the trim with the progress dashboard.
  python3 kdenlive-trim.py                                 # open the control dashboard
  python3 kdenlive-trim.py --gui "Day 046.kdenlive"        # ...with a project selected
  python3 kdenlive-trim.py --gui "Day 046.kdenlive" --quick-check --handles 1   # ...and these options set

Requires Python 3.7+ and ffmpeg + ffprobe (on PATH, or pass --ffmpeg / --ffprobe). The control dashboard
also needs Python's curses module, which macOS and Linux include; the command line works without it.
"""

import argparse
import errno
import hashlib
import json
import locale
import math
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
import xml.etree.ElementTree as ET
from collections import deque

try:
    import curses  # only the control dashboard needs it, so the command line also works on a Python without it
except ImportError:
    curses = None

AV_SERVICES = {"avformat", "avformat-novalidate"}  # MLT producers that play audio/video files
BIN_PLAYLIST_ID = "main_bin"  # Kdenlive's project bin (clip list), not a timeline track
COPY_CONTAINERS = {".mov", ".mp4", ".m4v", ".mkv"}  # cuts are written in these containers; anything else becomes .mov
MP4_LIKE = {".mp4", ".m4v"}  # PCM audio is unreliable in these, so cuts with PCM audio become .mov
BIN_POSITION_PROPS = ("kdenlive:monitorPosition", "kdenlive:thumbnailFrame")  # bin clip positions shifted with the trim
PREROLL_US = 500000  # audio decoder warm-up before the cut point
LONG_GOP_TAIL_US = 500000  # extra video read past the cut end for long-GOP sources


class TrimError(Exception):
    """Expected failure for one file (ffmpeg/ffprobe error, failed check). Callers catch it so that file is skipped
    or copied whole instead of the whole run stopping."""
    pass


UI = None  # live dashboard while a run is in progress (see Dashboard)


def log(msg=""):
    """Send a message to the dashboard and log file while a run is active, otherwise print it. One entry point, so
    messages work the same in --report, --plain and live mode."""
    if UI is not None:
        UI.log(msg)
    else:
        print(msg, flush=True)


# --------------------------------------------------------------------------- MLT time strings
# These mirror mlt_property.c so that values round-trip exactly as MLT reads them.

def mlt_time_to_frames(value, fps):
    """MLT time value (frame number, HH:MM:SS.mmm clock or SMPTE timecode) to a frame count at fps. Mirrors MLT's
    own parser so in/out points are read exactly as MLT reads them: a one-frame rounding difference would shift a
    cut."""
    v = (value or "").strip()
    if not v:
        return 0
    if ":" in v and fps > 0:
        if "." in v or "," in v:  # clock: HH:MM:SS.mmm
            parts = v.replace(",", ".").split(":")
            secs = float(parts[-1])
            mins = int(parts[-2]) if len(parts) >= 2 else 0
            hours = int(parts[-3]) if len(parts) >= 3 else 0
            return math.floor(fps * hours * 3600) + math.floor(fps * mins * 60) + int(round(fps * secs))
        # SMPTE timecode: HH:MM:SS:FF or HH:MM:SS;FF
        parts = re.split(r"[:;]", v)
        nums = [int(x or 0) for x in parts]
        frames = nums[-1]
        secs = nums[-2] if len(nums) >= 2 else 0
        mins = nums[-3] if len(nums) >= 3 else 0
        hours = nums[-4] if len(nums) >= 4 else 0
        return math.floor(fps * hours * 3600) + math.floor(fps * mins * 60) + math.ceil(fps * secs) + frames
    m = re.match(r"\s*[-+]?\d+", v)
    return int(m.group()) if m else 0


def mlt_frames_to_clock(frames, fps, decimal="."):
    """Frame count to an MLT clock string (HH:MM:SS.mmm), the format Kdenlive writes. Mirrors MLT's formatter so
    values written back round-trip to the same frame. decimal is the separator the project already uses ('.' or
    ',', depending on the locale Kdenlive ran in)."""
    save = frames
    hours = int(max(0, min(frames / (fps * 3600), 999999)))
    frames -= math.floor(hours * 3600 * fps)
    mins = int(max(0, min(frames / (fps * 60), 60)))
    if mins == 60:
        hours += 1
        frames = save - math.floor(hours * 3600 * fps)
        mins = 0
    save = frames
    frames -= math.floor(mins * 60 * fps)
    secs = max(0.0, min(frames / fps, 60.0))
    if secs >= 60.0:
        mins += 1
        frames = save - math.floor(mins * 60 * fps)
        secs = frames / fps
    s = "%02d:%02d:%06.3f" % (hours, mins, secs)
    return s.replace(".", decimal) if decimal != "." else s


def fmt_secs(seconds):
    """Seconds as M:SS.mmm for the report and dashboard (display only, never written to the project)."""
    sign = "-" if seconds < 0 else ""
    seconds = abs(seconds)
    m, s = divmod(seconds, 60)
    return "%s%d:%06.3f" % (sign, int(m), s)


def qround(x):
    """Qt's qRound for doubles (round half away from zero). Kdenlive uses it to size timewarp clips, so lengths
    calculated here match the ones Kdenlive writes."""
    return int(math.floor(x + 0.5)) if x >= 0 else int(math.ceil(x - 0.5))


# --------------------------------------------------------------------------- XML helpers

def props_of(elem):
    """{name: <property> element} for an MLT element. Not currently used; kept as a helper."""
    return {p.get("name"): p for p in elem.findall("property")}


def get_prop(elem, name, default=None):
    """Text of the named <property> child, or default if missing (an empty property gives ''). MLT keeps nearly
    every setting in <property name=...> children, so this is how the project is read."""
    for p in elem.findall("property"):
        if p.get("name") == name:
            return p.text if p.text is not None else ""
    return default


def set_prop(elem, name, value):
    """Set a <property> value, adding it if missing. New properties go after the existing ones and before any
    <filter>/<link> children, the order MLT and Kdenlive write."""
    for p in elem.findall("property"):
        if p.get("name") == name:
            p.text = value
            return
    p = ET.Element("property", {"name": name})
    p.text = value
    # keep properties grouped before child filters/links
    idx = 0
    for i, child in enumerate(list(elem)):
        if child.tag == "property":
            idx = i + 1
    p.tail = "\n  "
    elem.insert(idx, p)


def del_prop(elem, name):
    """Remove every <property> with this name. Used to drop links (e.g. a proxy) to files that will not be in the
    archive, so Kdenlive does not look for them."""
    for p in list(elem.findall("property")):
        if p.get("name") == name:
            elem.remove(p)


# --------------------------------------------------------------------------- ffmpeg helpers

class Tools:
    """Runs ffmpeg and ffprobe. Keeps their paths (--ffmpeg/--ffprobe) in one place and turns their failures into
    TrimError."""
    def __init__(self, ffmpeg, ffprobe):
        """Remember which ffmpeg and ffprobe executables to run."""
        self.ffmpeg = ffmpeg
        self.ffprobe = ffprobe

    def probe_json(self, args):
        """Run ffprobe with JSON output and return the parsed result. Raises TrimError with ffprobe's message, so a
        bad file is reported instead of crashing the run."""
        cmd = [self.ffprobe, "-v", "error", "-of", "json"] + args
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            raise TrimError("ffprobe failed: %s\n%s" % (" ".join(cmd), r.stderr.strip()))
        return json.loads(r.stdout or "{}")

    def probe_file(self, path):
        """Container and stream details (codecs, frame rate, time base, duration, tags) for a file. Almost every
        later step relies on these."""
        return self.probe_json(["-show_format", "-show_streams", path])

    def probe_packets(self, path, stream_index, interval=None, hashes=False, progress=None, expect=0):
        """Video packets of one stream as dicts: pts, dts, keyframe flag, duration and, with hashes, an MD5 of the
        packet data. interval limits reading to a time range (-read_intervals), so on a network share only a few
        seconds are read instead of the whole file. Output is read line by line so progress(fraction) can update
        during long reads; expect is the packet count that counts as 100%."""
        cmd = [self.ffprobe, "-v", "error", "-of", "compact=nk=0", "-select_streams", str(stream_index),
               "-show_entries", "packet=pts,dts,duration,flags" + (",data_hash" if hashes else "")]
        if hashes:
            cmd += ["-show_data_hash", "MD5"]
        if interval:
            cmd += ["-read_intervals", interval]
        cmd.append(path)
        out = []
        with tempfile.TemporaryFile() as err:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=err, text=True)
            for line in proc.stdout:
                if not line.startswith("packet|"):
                    continue
                f = dict(kv.split("=", 1) for kv in line.strip().split("|")[1:] if "=" in kv)
                num = lambda k: int(f[k]) if f.get(k, "N/A").lstrip("-").isdigit() else None
                pts, dts = num("pts"), num("dts")
                ts = pts if pts is not None else dts
                if ts is None:
                    continue
                out.append({"pts": ts, "dts": dts if dts is not None else ts, "key": "K" in f.get("flags", ""),
                            "dur": num("duration"), "hash": f.get("data_hash")})
                if progress and expect and len(out) % 8 == 0:
                    progress(min(1.0, len(out) / expect))
            proc.wait()
            if proc.returncode != 0:
                err.seek(0)
                raise TrimError("ffprobe failed: %s\n%s" % (" ".join(cmd), err.read().decode(errors="replace").strip()))
        return out

    def run_ffmpeg(self, args, total_us=None, progress=None):
        """Run ffmpeg, calling progress(fraction) from its -progress output when the expected output length
        total_us is known. stderr goes to a temp file, so an error message can be shown without a full pipe
        stalling ffmpeg."""
        cmd = [self.ffmpeg, "-nostdin", "-hide_banner", "-loglevel", "error", "-y", "-progress", "pipe:1", "-nostats"] + args
        with tempfile.TemporaryFile() as err:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=err, text=True)
            for line in proc.stdout:
                if progress and total_us and line.startswith("out_time_us="):
                    v = line.split("=", 1)[1].strip()
                    if v.lstrip("-").isdigit():
                        progress(max(0.0, min(1.0, int(v) / total_us)))
            proc.wait()
            if proc.returncode != 0:
                err.seek(0)
                raise TrimError("ffmpeg failed: %s\n%s" % (" ".join(cmd), err.read().decode(errors="replace").strip()))

    def decoded_frames_md5(self, path, stream_index, seek_us, count):
        """MD5 of each decoded picture, for count frames from seek_us. Used on long-GOP (H.264/HEVC) cuts, where
        identical packets alone do not prove identical pictures: a missing reference frame changes the decode.
        Returns [] if ffmpeg fails, which then fails the check."""
        args = [self.ffmpeg, "-nostdin", "-hide_banner", "-loglevel", "error"]
        if seek_us > 0:
            args += ["-ss", "%d.%06d" % divmod(seek_us, 1000000)]
        args += ["-i", path, "-map", "0:%d" % stream_index, "-frames:v", str(count), "-f", "framemd5", "-"]
        r = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        return [l.split(",")[-1].strip() for l in r.stdout.splitlines() if l and not l.startswith("#")]


def parse_rational(s):
    """'num/den' string (how ffprobe reports frame rates and time bases) to a (num, den) tuple, or None if missing,
    malformed or zero."""
    try:
        n, d = s.split("/")
        n, d = int(n), int(d)
        return (n, d) if n > 0 and d > 0 else None
    except (ValueError, AttributeError):
        return None


def guess_fps(stream):
    """Approximation of av_guess_frame_rate() + MLT guess_frame_rate(): the frame rate MLT will use for this file,
    so the source-frame maths here agrees with what Kdenlive plays. Falls back to the average rate when the
    reported rate is implausibly high, as some phone and variable-rate files report."""
    fr = parse_rational(stream.get("r_frame_rate"))
    avg = parse_rational(stream.get("avg_frame_rate"))
    if fr and avg and avg[0] / avg[1] < 70 and fr[0] / fr[1] > 210:
        fr = avg
    if fr and fr[0] / fr[1] >= 1000 and avg:
        fr = avg
    return fr


def us_from_str(s):
    """ffprobe time string (seconds, exactly 6 decimals) to whole microseconds, without going through a float so no
    rounding error creeps in. None for missing values."""
    if s in (None, "N/A"):
        return None
    neg = s.startswith("-")
    s = s.lstrip("-")
    whole, _, frac = s.partition(".")
    v = int(whole or 0) * 1000000 + int((frac + "000000")[:6] or 0)
    return -v if neg else v


def kdenlive_file_hash(path):
    """Same as ProjectClip::calculateHash() in Kdenlive: MD5 of the first and last 1 MB (the whole file if 2 MB or
    less), plus the size. Kdenlive stores this hash in the project and names proxies after it, so it is
    recalculated for every new file. Also a cheap check that a copy matches its original."""
    size = os.path.getsize(path)
    md5 = hashlib.md5()
    with open(path, "rb") as f:
        if size > 2000000:
            md5.update(f.read(1000000))
            f.seek(size - 1000000)
            md5.update(f.read())
        else:
            md5.update(f.read())
    return md5.hexdigest(), size


# --------------------------------------------------------------------------- timecode

def shift_timecode(tc, add_frames, fps):
    """Timecode tc moved forward by add_frames, or None if it cannot be parsed. A trimmed file starts later in the
    recording, so its embedded timecode is advanced to stay correct. Handles drop-frame timecode (29.97/59.94) and
    wraps at 24 hours."""
    try:
        nominal = int(round(fps))
        drop = (";" in tc or tc.count(".") == 1 and len(tc.split(".")[-1]) == 2) and abs(fps * 1.001 - nominal) < 0.01
        h, m, s, f = [int(x) for x in re.split(r"[:;.]", tc)]
        if drop:
            dpm = nominal // 15
            total_min = 60 * h + m
            n = ((h * 3600 + m * 60 + s) * nominal + f) - dpm * (total_min - total_min // 10)
        else:
            n = (h * 3600 + m * 60 + s) * nominal + f
        n += add_frames
        if drop:
            dpm = nominal // 15
            per10 = nominal * 600 - dpm * 9
            d, r = divmod(n, per10)
            if r > dpm:
                n += dpm * 9 * d + dpm * ((r - dpm) // (nominal * 60 - dpm))
            else:
                n += dpm * 9 * d
        f = n % nominal
        s = (n // nominal) % 60
        m = (n // (nominal * 60)) % 60
        h = (n // (nominal * 3600)) % 24
        return "%02d:%02d:%02d%s%02d" % (h, m, s, ";" if drop else ":", f)
    except (ValueError, ZeroDivisionError):
        return None


# --------------------------------------------------------------------------- project model

class Media:
    """One MLT producer/chain element that plays a file. A file can have several (bin clip, timeline copies,
    speed-changed versions), each with its own speed and in/out, so they are kept separately and grouped by file
    later (Source)."""

    def __init__(self, doc, elem):
        """Read what matters for trimming: the file played (including timewarp's 'speed:path' form), speed and
        direction, proxy and original paths, Time Remap, in/out and length."""
        self.doc = doc
        self.elem = elem
        self.id = elem.get("id")
        self.service = get_prop(elem, "mlt_service", "")
        self.is_warp = self.service == "timewarp"
        self.speed = 1.0
        resource = get_prop(elem, "resource", "") or ""
        if self.is_warp:
            self.speed = float(get_prop(elem, "warp_speed") or resource.split(":", 1)[0] or 1.0)
            self.warp_prefix = resource.split(":", 1)[0] if ":" in resource else repr(self.speed)
            res = get_prop(elem, "warp_resource") or (resource.split(":", 1)[1] if ":" in resource else resource)
        else:
            res = resource
        self.resource = doc.abspath(res)
        self.kid = get_prop(elem, "kdenlive:id")
        orig = get_prop(elem, "kdenlive:originalurl")
        self.original = doc.abspath(orig) if orig else None
        proxy = get_prop(elem, "kdenlive:proxy")
        self.proxy = doc.abspath(proxy) if proxy and len(proxy) > 1 else None
        self.has_remap = any(get_prop(l, "mlt_service") == "timeremap" for l in elem.iter("link"))
        self.in_ = doc.t(elem.get("in")) if elem.get("in") else 0
        length = get_prop(elem, "length")
        self.length = doc.t(length) if length else None
        self.out = doc.t(elem.get("out")) if elem.get("out") else (self.length - 1 if self.length else None)
        self.is_bin = False
        self.key = None  # filled by Doc

    def prod_fps(self):
        """fps of the clip producer that does the seeking (MLT timewarp builds a scaled profile). Timewarp maps
        positions through this rate, and the integer truncation must match MLT's to land on the same source frame."""
        num, den = self.doc.fps_num, self.doc.fps_den
        if not self.is_warp:
            return num / den
        if num < 1000:
            num *= 1000
            den *= 1000
        scaled = num / abs(self.speed)
        if scaled > 2147483647:
            den = int(den * abs(self.speed))
        else:
            num = int(scaled)
        return num / den

    def src_frame(self, p, sfps, out_override=None):
        """Source frame index MLT shows for position p of this producer. Reversed clips count back from the out
        point. out_override tests a planned cut with the producer's new out point before anything is changed."""
        if self.is_warp and self.speed < 0:
            out = self.out if out_override is None else out_override
            cp = out - p + self.in_
        else:
            cp = p + (self.in_ if self.is_warp else 0)
        return int(cp / self.prod_fps() * sfps + 0.5)

    def src_span(self, a, b, sfps):
        """(lo, hi) source frames needed for positions a..b, including the audio of the last frame: the part of the
        file that must survive the cut for the clip to look and sound the same."""
        r = sfps / self.prod_fps()
        if self.is_warp and self.speed < 0:
            c0, c1 = self.out - b + self.in_, self.out - a + self.in_
        else:
            off = self.in_ if self.is_warp else 0
            c0, c1 = a + off, b + off
        lo = min(self.src_frame(a, sfps), self.src_frame(b, sfps), int(math.floor(c0 * r)))
        hi = max(self.src_frame(a, sfps), self.src_frame(b, sfps), int(math.ceil((c1 + 1) * r)) - 1)
        return lo, hi


class Use:
    """One place a Media is used: a timeline entry (or tractor track) covering positions a..b of that producer.
    holder is the XML element whose in/out is shifted after the cut; where and tl_pos are only for the report."""
    def __init__(self, media, holder, a, b, where, tl_pos):
        """Store the use as found in the project; nothing is calculated here."""
        self.media = media
        self.holder = holder  # <entry> or <track>
        self.a = a
        self.b = b
        self.where = where
        self.tl_pos = tl_pos


class Doc:
    """The Kdenlive project: the parsed XML plus what is worked out from it (frame rate, media elements, where each
    is used). All edits are made to this tree in memory and written once by save(), so a failed run never leaves a
    half-edited project."""
    def __init__(self, path):
        """Parse the project and collect its media and uses. Also notes the decimal separator the project uses, so
        rewritten times look like the originals."""
        self.path = os.path.abspath(path)
        self.tree = ET.parse(path)
        self.root = self.tree.getroot()
        prof = self.root.find("profile")
        if prof is None:
            raise TrimError("No <profile> in project")
        self.fps_num = int(prof.get("frame_rate_num"))
        self.fps_den = int(prof.get("frame_rate_den"))
        self.fps = self.fps_num / self.fps_den
        # Same rule as Kdenlive's DocumentChecker: relative paths are relative to the project's saved "root"
        # folder if it still exists. If it does not (the project folder was moved or copied elsewhere), or is
        # "$CURRENTPATH" (an extracted Kdenlive archive), the project file's own folder is used instead, and
        # absolute paths under the old root are looked for under the new one.
        root_attr = self.root.get("root") or ""
        self.old_root = None
        if root_attr and root_attr != "$CURRENTPATH" and os.path.isdir(root_attr):
            self.root_dir = root_attr
        else:
            self.root_dir = os.path.dirname(self.path)
            if root_attr and root_attr != "$CURRENTPATH":
                self.old_root = os.path.normpath(root_attr)
        sample = re.search(r'(?:in|out)="\d+:\d+:\d+([.,])\d', open(path, encoding="utf-8").read())
        self.decimal = sample.group(1) if sample else "."
        self.by_id = {}
        for e in self.root.iter():
            if e.tag in ("producer", "chain", "playlist", "tractor") and e.get("id"):
                self.by_id[e.get("id")] = e
        self.media = {}
        for e in self.root.iter():
            if e.tag in ("producer", "chain") and e.get("id"):
                svc = get_prop(e, "mlt_service", "")
                if svc in AV_SERVICES or svc == "timewarp":
                    self.media[e.get("id")] = Media(self, e)
        self._resolve_originals()
        self.track_names = self._track_names()
        self.uses = []
        self.bin_entries = []
        self._collect_uses()

    def t(self, s):
        """Project time string to frames at the project frame rate (shorthand used throughout)."""
        return mlt_time_to_frames(s, self.fps)

    def fmt_like(self, old, frames):
        """Frames formatted in the same style as old (clock string or plain frame number), so edited values match
        how Kdenlive wrote the rest of the file."""
        if old is not None and ":" in old:
            return mlt_frames_to_clock(frames, self.fps, self.decimal)
        return str(frames)

    def abspath(self, p):
        """Absolute path for a path from the project. Relative paths are relative to the project's root folder, as
        in Kdenlive; Windows drive paths count as absolute. If the project was moved, a missing absolute path under
        the old root is looked for in the same place under the new one, as Kdenlive does."""
        if not p:
            return p
        if p.startswith("$CURRENTPATH"):
            p = os.path.dirname(self.path) + p[len("$CURRENTPATH"):]
        if os.path.isabs(p) or re.match(r"^[A-Za-z]:[\\/]", p):
            a = os.path.normpath(p)
            if self.old_root and inside(a, self.old_root) and not os.path.exists(a):
                moved = os.path.join(self.root_dir, os.path.relpath(a, self.old_root))
                if os.path.exists(moved):
                    return moved
            return a
        return os.path.normpath(os.path.join(self.root_dir, p))

    def relpath_for_xml(self, p):
        """Paths are kept absolute while editing; save() makes them relative to the new project. Kept as a hook so
        the path policy lives in one place."""
        return p

    def _resolve_originals(self):
        """Work out the real source file behind each media element (m.key). With proxies on, an element may point
        at the proxy while only another element of the same clip records the original, so originals and proxies are
        shared by kdenlive:id. This makes the original, not the proxy, the file that gets trimmed."""
        by_kid = {}
        for m in self.media.values():
            if m.original and m.kid:
                by_kid.setdefault(m.kid, (m.original, m.proxy))
        for m in self.media.values():
            orig = m.original
            if not orig and m.kid in by_kid:
                o, prox = by_kid[m.kid]
                if m.resource in (prox, o):
                    orig = o
                    m.proxy = m.proxy or prox
            m.key = orig or m.resource

    def _track_names(self):
        """{playlist id: Kdenlive track name}, used to label uses in the report (e.g. 'V1', 'Music')."""
        names = {}
        for tr in self.root.iter("tractor"):
            name = get_prop(tr, "kdenlive:track_name")
            for t in tr.findall("track"):
                if name is not None:
                    names[t.get("producer")] = name or tr.get("id")
        return names

    def _collect_uses(self):
        """Walk every playlist and record where each media element is used and over which frames (blanks advance
        the timeline position). Bin playlist entries are kept separately: they span the whole clip and are not a
        use, so they must not stop a file being trimmed. Media placed directly on tractor tracks count as uses too."""
        for pl in self.root.iter("playlist"):
            is_bin = pl.get("id") == BIN_PLAYLIST_ID
            pos = 0
            for child in pl:
                if child.tag == "blank":
                    pos += self.t(child.get("length"))
                elif child.tag == "entry":
                    pid = child.get("producer")
                    target = self.by_id.get(pid)
                    m = self.media.get(pid)
                    if target is None:
                        continue
                    if m is not None:
                        a = self.t(child.get("in")) if child.get("in") is not None else m.in_
                        b = self.t(child.get("out")) if child.get("out") is not None else m.out
                    else:
                        a = self.t(child.get("in")) if child.get("in") is not None else 0
                        b = self.t(child.get("out")) if child.get("out") is not None else -1
                    if m is not None:
                        if is_bin:
                            m.is_bin = True
                            self.bin_entries.append((m, child))
                        else:
                            where = self.track_names.get(pl.get("id"), pl.get("id"))
                            self.uses.append(Use(m, child, a, b, where, pos))
                    pos += max(0, b - a + 1)
        for tr in self.root.iter("tractor"):
            for t in tr.iter("track"):
                m = self.media.get(t.get("producer"))
                if m is not None:
                    a = self.t(t.get("in")) if t.get("in") else m.in_
                    b = self.t(t.get("out")) if t.get("out") else m.out
                    self.uses.append(Use(m, t, a, b, "tractor %s" % tr.get("id"), 0))

    def save(self, path):
        """Write the project at path. Every file reference becomes relative to the new project's folder
        when it is inside it (like a Kdenlive archive) and absolute otherwise; 'root' is dropped so the
        folder keeps working if it is moved or renamed."""
        base = os.path.dirname(os.path.abspath(path))
        for el in self.root.iter():
            if el.tag not in ("producer", "chain"):
                continue
            svc = get_prop(el, "mlt_service", "")
            for prop in el.findall("property"):
                name, v = prop.get("name"), (prop.text or "").strip()
                if name not in CLIP_PATH_PROPS or not v or v == "-":
                    continue
                prefix = ""
                if name == "resource" and svc == "timewarp" and ":" in v:
                    head, v = v.split(":", 1)
                    prefix = head + ":"
                a = self.abspath(v)
                if not ("/" in v or os.path.exists(a)):
                    continue  # not a file (e.g. "black", "qtext")
                if inside(a, base):  # MLT resolves relative paths after a timewarp "speed:" prefix too
                    prop.text = prefix + os.path.relpath(a, base)
                elif prefix:
                    prop.text = prefix + a
                elif inside(a, base):
                    prop.text = os.path.relpath(a, base)
                else:
                    prop.text = a
        self.root.attrib.pop("root", None)
        self.tree.write(path, encoding="utf-8", xml_declaration=True)


# --------------------------------------------------------------------------- per-source planning

class Source:
    """Everything about one source file: every media element that plays it, all their uses, and the plan and
    results of trimming it. The unit of work: one file, one cut, one line in the summary."""
    def __init__(self, key, medias, uses):
        """Start with nothing known; plan_source, trim_one and the copy steps fill the fields in as the run goes."""
        self.key = key
        self.medias = medias
        self.uses = uses
        self.skip = None
        self.notes = []
        self.probe = None
        self.vstream = None
        self.sfps = None
        self.n_frames = None
        self.need = None
        self.plan = None
        self.out_path = None
        self.new_proxy = None
        self.proxy_ok = False
        self.size = None
        self.new_size = None
        self.in_media_dir = False
        self.copied_to = None

    @property
    def name(self):
        """File name without the folder, for display."""
        return os.path.basename(self.key)


def element_offsets(src, S, new_bin_len, to_end=False):
    """Per-media (D, new_len, new_out) for a cut starting at source frame S. D is how many producer frames that
    element's positions move back by. Each element needs its own values because timewarp clips count frames at
    their own speed and reversed clips are measured from the end.
    to_end: the cut keeps the end of the file, so producers keep any length they had past the last video frame
    (Kdenlive measures length from the longest stream, often audio)."""
    doc_fps = src.medias[0].doc.fps
    res = {}
    for m in src.medias:
        if not m.is_warp:
            D = int(round(S * doc_fps / src.sfps))
            nl = new_bin_len
            if to_end and m.length:
                nl = max(nl, m.length - D)
            res[m.id] = (D, nl, nl - 1)
            continue
        r = src.sfps / m.prod_fps()
        W = int(round(S / r))
        nl = qround(new_bin_len / abs(m.speed))
        if to_end and m.length and m.speed > 0:
            nl = max(nl, m.length - W)
        new_out = nl - 1
        if m.speed < 0:
            D = m.out - W - new_out
        else:
            D = W
        res[m.id] = (D, nl, new_out)
    return res


def check_plan(src, S, E, offsets):
    """Number of used positions whose source frame changes after the cut (0 = exact). None if a clip would fall
    outside the new file or any frame drifts by more than 1. Every candidate cut is tested against every use before
    anything is written, so the timeline shows the same frames afterwards (unless --allow-drift accepts a small,
    counted drift). Run again after cutting, with the real file length, as a final check."""
    K = E - S + 1
    drift = 0
    # if the cut keeps the end of the file, positions past the end show the last frame in both versions
    tail_kept = src.n_frames is not None and E >= src.n_frames - 1
    for u in src.uses:
        m = u.media
        D, nl, new_out = offsets[m.id]
        if u.a - D < 0 or u.b - D > nl - 1:
            return None
        if not m.is_warp and abs(src.sfps - m.doc.fps) < 1e-9:
            continue  # identity mapping, always exact
        for p in range(u.a, u.b + 1):
            old = m.src_frame(p, src.sfps)
            new = m.src_frame(p - D, src.sfps, out_override=new_out) if m.speed < 0 else m.src_frame(p - D, src.sfps)
            if tail_kept:
                old, new = min(old, src.n_frames - 1), min(new, K - 1)
            if new < 0 or new > K - 1:
                return None
            err = abs(new - (old - S))
            if err > 1:
                return None
            drift += err
    return drift


def compute_need(src):
    """Set src.need to the first and last source frame any use of this file needs, clamped to the file. Everything
    outside that range is what trimming can remove."""
    lo, hi = None, None
    for u in src.uses:
        a, b = u.media.src_span(u.a, u.b, src.sfps)
        lo = a if lo is None else min(lo, a)
        hi = b if hi is None else max(hi, b)
    lo = max(lo, 0)
    if src.n_frames:
        hi = min(hi, src.n_frames - 1)
    src.need = (lo, hi)


def plan_source(src, tools, args, doc):
    """Decide whether and where to cut one source file. Skips files that cannot be trimmed safely (Time Remap,
    non-zero producer in point, missing file, no video, unknown frame rate). Otherwise finds the latest start S and
    earliest end E around the used range where every use still shows exactly the same frames, reading only small
    parts of the file (packets near the cut points), then skips the file if the saving is below --min-saving.
    Result in src.plan, or the reason in src.skip."""
    m0 = src.medias[0]
    path = src.key
    if inside(path, args.media_dir_abs):
        src.skip = "already in the archive"
        src.in_media_dir = True
        return
    if any(m.has_remap for m in src.medias):
        src.skip = "uses Time Remap (keyframed speed), not supported"
        return
    if any(m.in_ != 0 for m in src.medias):
        src.skip = "a producer has a non-zero in point, not supported"
        return
    if not src.uses:
        src.skip = "not used on any timeline"
        return
    # provisional frame rate from the project (lets --report work without the media)
    meta = next(((get_prop(m.elem, "meta.media.frame_rate_num"), get_prop(m.elem, "meta.media.frame_rate_den"))
                 for m in src.medias if get_prop(m.elem, "meta.media.frame_rate_num")), (None, None))
    if meta[0] and meta[1] and int(meta[1]) > 0:
        src.sfps = int(meta[0]) / int(meta[1])
    bin_m = next((m for m in src.medias if m.is_bin), m0)
    if src.sfps and bin_m.length:
        src.n_frames = int(round(bin_m.length / doc.fps * src.sfps))
    if src.sfps:
        compute_need(src)
    if not os.path.isfile(path):
        src.skip = "file not found: %s" % path
        return
    src.size = os.path.getsize(path)
    src.probe = tools.probe_file(path)
    streams = src.probe.get("streams", [])
    vidx = None
    xml_vidx = get_prop(m0.elem, "video_index")
    for s in streams:
        if s.get("codec_type") == "video" and not s.get("disposition", {}).get("attached_pic"):
            if xml_vidx is not None and str(s.get("index")) == xml_vidx:
                vidx = s["index"]
                break
            if vidx is None:
                vidx = s["index"]
    if vidx is None:
        src.skip = "no video stream (audio-only files are left as they are)"
        return
    src.vstream = streams[vidx]
    # the project's meta.media values describe the proxy when proxies are on, so probe the original
    fr = guess_fps(src.vstream)
    if not fr:
        src.skip = "could not determine frame rate"
        return
    src.fr = fr
    src.sfps = fr[0] / fr[1]
    tb = parse_rational(src.vstream.get("time_base"))
    src.tb = tb[0] / tb[1]
    src.tbr = tb
    fmt = src.probe.get("format", {})
    src.start_us = us_from_str(fmt.get("start_time")) or 0
    nb = src.vstream.get("nb_frames")
    vdur = src.vstream.get("duration")
    if nb and str(nb).isdigit() and int(nb) > 0:
        src.n_frames = int(nb)
    elif vdur not in (None, "N/A"):
        src.n_frames = int(round(float(vdur) * src.sfps))
    else:
        dur_us = us_from_str(fmt.get("duration"))
        src.n_frames = int(round(dur_us / 1e6 * src.sfps)) if dur_us else None
    compute_need(src)
    lo, hi = src.need
    # --handles widens the range to keep. S_max is the latest start allowed, E_min the earliest end.
    H = int(round(args.handles * src.sfps))
    S_max = max(0, lo - H)
    E_min = hi + H if src.n_frames is None else min(src.n_frames - 1, hi + H)

    # first keyframe pts = MLT's first_pts (only a few packets are read)
    head = tools.probe_packets(path, vidx, "%+#8")
    if not any(p["key"] for p in head):
        head = tools.probe_packets(path, vidx, "%+#300")
    first_key = next((p for p in head if p["key"]), None)
    if first_key is None:
        src.skip = "no keyframe found at start of file"
        return
    src.first_pts = 0 if first_key["dts"] < 0 else first_key["pts"]
    src.pkts = {}

    def t_of(idx):
        """Presentation time in seconds of source frame idx."""
        return src.first_pts * src.tb + idx / src.sfps

    def interval(i0, i1, pad0=0.1, pad1=0.2):
        """-read_intervals string for frames i0..i1 with some padding, so ffprobe reads only that part of the file."""
        t0, t1 = t_of(i0) - pad0, t_of(i1) + pad1
        return ("%.6f%%%.6f" % (t0, t1)) if t0 > 0 else ("%%%.6f" % t1)

    def add_packets(pk):
        """Index probed packets by source frame number in src.pkts (first one wins) and return them."""
        for p in pk:
            p["idx"] = int((p["pts"] - src.first_pts) * src.tb * src.sfps + 0.5)
            if p["idx"] >= 0:
                src.pkts.setdefault(p["idx"], p)
        return pk

    add_packets(head)
    # intra-frame test on a short window at the cut point (avoids reading GBs of ProRes)
    sample = add_packets(tools.probe_packets(path, vidx, interval(S_max, S_max + 12)))
    src.intra = len(sample) >= 6 and all(p["key"] for p in sample)
    if not src.intra and args.long_gop == "skip":
        src.skip = "long-GOP video (%s) and --long-gop skip" % src.vstream.get("codec_name")
        return
    search = int(args.search_seconds * src.sfps)
    if src.intra:
        # intra-frame (ProRes, DNxHR...): any frame can start a stream copy, so try every frame back from S_max
        cands = list(range(S_max, max(-1, S_max - search - 1), -1))
    else:
        # long-GOP (H.264/HEVC): a stream copy must start on a keyframe, so only keyframes are candidates
        add_packets(tools.probe_packets(path, vidx, interval(max(0, S_max - search), S_max, 2.0, 0.1)))
        cands = sorted((i for i, p in src.pkts.items() if p["key"] and S_max - search <= i <= S_max), reverse=True)
    # the start of the file always works as a last resort (nothing trimmed at the front)
    if 0 not in cands:
        cands.append(0)

    # take the latest start (biggest saving) that keeps every use exact; for each start, try the first few ends
    exact, drifts = None, []
    for S in cands:
        for E in range(E_min, E_min + 5):
            if src.n_frames and E > src.n_frames - 1:
                break
            to_end = src.n_frames is not None and E >= src.n_frames - 1
            offs = element_offsets(src, S, int(round((E - S + 1) / src.sfps * doc.fps)), to_end)
            drift = check_plan(src, S, E, offs)
            if drift is None:
                continue
            if drift == 0:
                exact = (S, E)
            else:
                drifts.append((S, E, drift))
            break
        if exact:
            break
    # --allow-drift: latest cut whose drift is at most 1% of the used frames; otherwise stay exact
    best = None
    used = sum(u.b - u.a + 1 for u in src.uses)
    ok = [d for d in drifts if d[2] <= max(1, used // 100)]
    if ok:
        best = max(ok, key=lambda d: d[0])
        if exact and best[0] <= exact[0]:
            best = None
    # both alternatives are kept for --report-json, so the front end can predict --allow-drift without a rescan
    src.alts = {"exact": exact, "drift": best}
    src.start_limited = bool(exact and exact[0] == 0 and S_max > 0 and src.need[0] > 0)
    chosen_drift = 0
    if exact and (exact[0] > 0 or not args.allow_drift or best is None):
        chosen = exact
        if exact[0] == 0 and S_max > 0 and src.need[0] > 0:
            src.notes.append("start not trimmed: no %scut point lines up exactly with the speed/fps conversion"
                             % ("keyframe " if not src.intra else ""))
    elif best and args.allow_drift:
        chosen = best[:2]
        chosen_drift = best[2]
        src.notes.append("%d timeline frame(s) now show a source frame 1 frame away from before (--allow-drift)" % best[2])
    else:
        src.skip = "could not find a cut that keeps every frame identical"
        return
    S, E = chosen
    K = E - S + 1
    # cut_file needs the exact timestamps of the packets at both cut points
    if S not in src.pkts or (E + 1 not in src.pkts and E not in src.pkts):
        add_packets(tools.probe_packets(path, vidx, interval(S, S + 1)))
        add_packets(tools.probe_packets(path, vidx, interval(E, E + 1)))
    if S not in src.pkts or E not in src.pkts:
        src.skip = "frame %d not found in packet list (variable frame rate?)" % S
        return
    # saving estimated by frame count; long-GOP cuts keep a little extra at the end (see cut_file)
    total = src.n_frames or (E + 1)
    kept = K if src.intra else min(total - S, K + int(math.ceil(LONG_GOP_TAIL_US / 1e6 * src.sfps)))
    saving = 1 - kept / total
    src.plan = {"S": S, "E": E, "K": K, "saving": saving, "drift": chosen_drift}
    # a cut that keeps every frame saves nothing (whatever --min-saving says): copy the file instead. Not in
    # --report-json, where predict() makes this call per option set (an --allow-drift cut may still trim).
    if saving <= 0 and not getattr(args, "report_json", None):
        src.skip = WHOLE_FILE
    elif saving * 100 < args.min_saving:
        src.skip = "only %.0f%% would be saved (--min-saving %g)" % (saving * 100, args.min_saving)


# --------------------------------------------------------------------------- cutting

WHOLE_FILE = "the timeline uses the whole file, so trimming would save nothing"


def audio_codec_for(stream, mode):
    """Codec for one audio stream in the cut. PCM sources keep their codec. Compressed audio (AAC etc.) is decoded
    and stored as PCM in the decoder's own sample format, so the trimmed file holds exactly the samples MLT would
    have decoded (float stays float, so overshoots above 0 dBFS are not clipped). mode 'copy' (--audio copy) keeps
    compressed audio as it is."""
    name = stream.get("codec_name", "")
    if name.startswith("pcm_"):
        return name
    if mode == "copy":
        return "copy"
    fmt = stream.get("sample_fmt", "")
    if fmt.startswith(("flt", "dbl")):
        return "pcm_f32le"
    if fmt.startswith("s32"):
        return "pcm_s24le" if str(stream.get("bits_per_raw_sample")) == "24" else "pcm_s32le"
    return "pcm_s16le"


def cut_file(tools, path, out_path, S, E, first_pts, tb, tbr, sfps, start_us, vidx, probe, intra, audio_mode, pkts,
             to_end=False, progress=None):
    """Write out_path holding source frames S..E of path. Video is stream-copied (no re-encode, no quality loss)
    from an exact timestamp; compressed audio is decoded and trimmed to the sample (see audio_codec_for); metadata
    is kept and the timecode is shifted to the new start. Returns the {old: new} stream index mapping and (expected
    audio length, tolerance) in microseconds for verify_cut."""
    streams = probe.get("streams", [])
    ext = os.path.splitext(out_path)[1].lower()
    # only audio and video are kept; data, subtitle and cover-art streams are dropped (see remap_streams)
    keep = [s for s in streams if s.get("codec_type") in ("video", "audio")
            and not s.get("disposition", {}).get("attached_pic")]
    keep_idx = [s["index"] for s in keep]
    if vidx not in keep_idx:
        raise TrimError("video stream %d not kept" % vidx)
    # timestamps of the first kept frame and of the frame after the last one
    pS = pkts[S]["pts"]
    if E + 1 in pkts:
        pEnd = pkts[E + 1]["pts"]
    else:
        last = pkts[E]
        pEnd = last["pts"] + (last["dur"] or int(round(1 / (sfps * tb))))
    target_us = -(-(pS * tbr[0] * 1000000) // tbr[1])  # ceil to microseconds
    ss_us = target_us - start_us
    dur_us = (pEnd - pS) * tbr[0] * 1000000 // tbr[1]
    # Input 0 supplies the stream-copied video. Compressed audio is decoded from a second input that
    # starts PREROLL earlier, so codecs that need the previous packet (AAC) are fully warmed up at the
    # cut; the pre-roll is then removed sample-exactly with atrim.
    acodec = {s["index"]: audio_codec_for(s, audio_mode) for s in keep if s["codec_type"] == "audio"}
    reencode = {i for i, c in acodec.items() if c != "copy"}
    tfmt = lambda us: "%d.%06d" % divmod(us, 1000000)
    args = []
    if ss_us > 0:
        args += ["-ss", tfmt(ss_us)]
    # intra: stop just before frame E+1; long-GOP: read a little further so trailing reference
    # frames needed by the last B-frames are kept (extra frames are harmless)
    v_t = dur_us - 1 if intra else dur_us + LONG_GOP_TAIL_US
    args += ["-t", tfmt(v_t), "-i", path]
    pre_us = 0
    if reencode:
        a_ss = max(0, ss_us - PREROLL_US)
        pre_us = ss_us - a_ss
        if a_ss > 0:
            args += ["-ss", tfmt(a_ss)]
        if not to_end:
            args += ["-t", tfmt(pre_us + dur_us + PREROLL_US)]
        args += ["-i", path]
    # video and copied audio come from input 0, re-encoded audio from the pre-rolled input 1
    for s in keep:
        src_in = 1 if s["index"] in reencode else 0
        args += ["-map", "%d:%d" % (src_in, s["index"])]
    for o, s in enumerate(keep):
        if s["codec_type"] == "video":
            args += ["-c:%d" % o, "copy"]
            # keep the original codec tag (e.g. 'apch' ProRes HQ, 'hvc1' HEVC) so players treat the file the same
            tag = s.get("codec_tag_string", "")
            if ext in (".mov", ".mp4", ".m4v") and re.fullmatch(r"[A-Za-z0-9]{4}", tag or ""):
                args += ["-tag:%d" % o, tag]
        else:
            args += ["-c:%d" % o, acodec[s["index"]]]
            if s["index"] in reencode:
                sr = int(s.get("sample_rate") or 48000)
                a0 = int(round(pre_us * sr / 1e6))
                n = int(round(dur_us * sr / 1e6))
                end = "" if to_end else ":end_sample=%d" % (a0 + n)
                args += ["-filter:%d" % o, "atrim=start_sample=%d%s,asetpts=PTS-STARTPTS" % (a0, end)]
    # keep file metadata (creation date, camera tags); chapters would point at the wrong times
    args += ["-map_metadata", "0", "-map_chapters", "-1"]
    if ext in (".mov", ".mp4", ".m4v"):
        args += ["-movflags", "+use_metadata_tags"]
        vtags = streams[vidx].get("tags", {}) or {}
        tc = vtags.get("timecode") or (probe.get("format", {}).get("tags", {}) or {}).get("timecode")
        new_tc = shift_timecode(tc, S, sfps) if tc else None
        if new_tc:
            args += ["-timecode", new_tc]
        else:
            # no source timecode, so don't let ffmpeg add a timecode track
            args += ["-write_tmcd", "0"]
    args.append(out_path)
    # removed automatically if the run is interrupted mid-write
    CLEANUP.add(out_path)
    tools.run_ffmpeg(args, dur_us, progress)
    # stream index in the original -> index in the cut
    mapping = {old: new for new, old in enumerate(keep_idx)}
    # audio we can expect in the cut (less if the original's audio stops before its video)
    expect, tol = dur_us, 2000
    for st in keep:
        if st["codec_type"] == "audio":
            a_start, a_dur = us_from_str(st.get("start_time")), us_from_str(st.get("duration"))
            if a_start is not None and a_dur is not None:
                avail = a_start + a_dur - target_us
                if st["index"] in reencode:
                    # atrim counts samples from the first one decoded, so audio that starts after the second
                    # input does (segmented clips often start their audio a few ms after the video) gives the
                    # cut that much less
                    avail -= max(0, a_start - (a_ss + start_us))
                expect = min(expect, avail)
            if to_end and not st.get("codec_name", "").startswith("pcm_"):
                # a compressed stream's listed duration can include up to one block of encoder
                # padding that never decodes, which only matters when the cut runs to the end
                sr = int(st.get("sample_rate") or 48000)
                tol = max(tol, 2000 + int(1024 * 1e6 / sr))
    return mapping, (max(0, expect), tol)


QUICK_EDGE_SECONDS = 2.0     # --quick-check: frames compared at the start and end of each cut
QUICK_SAMPLES = 3            # ... plus this many samples spread through the middle
QUICK_SAMPLE_SECONDS = 1.0


def quick_windows(lo, hi, sfps):
    """Frame ranges (original numbering) compared by --quick-check: the start, the end and a few samples in the
    middle. Overlapping windows are merged, so on short cuts they cover the whole range and quick reads as much as
    the full check."""
    edge = max(1, int(round(QUICK_EDGE_SECONDS * sfps)))
    samp = max(1, int(round(QUICK_SAMPLE_SECONDS * sfps)))
    wins = [(lo, min(hi, lo + edge - 1)), (max(lo, hi - edge + 1), hi)]
    span = hi - lo + 1
    for k in range(1, QUICK_SAMPLES + 1):
        c = lo + span * k // (QUICK_SAMPLES + 1) - samp // 2
        wins.append((max(lo, c), min(hi, c + samp - 1)))
    merged = []
    for a, b in sorted(wins):
        if merged and a <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else:
            merged.append((a, b))
    return merged


def check_share(src, quick):
    """Bytes read while checking a cut, as a multiple of the cut's size (the cut itself counts as 1). Weights the
    progress bar and time-left estimate: the full check reads the range twice more (2), the quick check only its
    sample windows."""
    if not quick:
        return 2.0
    lo, hi = src.need
    lo, hi = max(lo, src.plan["S"]), min(hi, src.plan["E"])
    frames = sum(b - a + 1 for a, b in quick_windows(lo, hi, src.sfps))
    return min(2.0, 2.0 * frames / max(1, src.plan["K"]))


def interval_for(first_pts, tb, i0, i1, sfps, pad=0.1):
    """-read_intervals string for frames i0..i1 of a file whose first frame is at first_pts, with a little padding,
    so the check reads only the frames it compares."""
    t0 = first_pts * tb + i0 / sfps - pad
    t1 = first_pts * tb + (i1 + 1) / sfps + pad
    return "%.6f%%%.6f" % (t0, t1) if t0 > 0 else "%%%.6f" % t1


def compare_hashes(a, b, first_pts, tb, ofirst, otb, sfps, S, i0, i1):
    """Raise TrimError unless every original frame i0..i1 has the same packet MD5 as frame (index - S) of the cut,
    each file numbered from its own first frame. Identical packet data means the video was copied bit for bit."""
    amap = {int((p["pts"] - first_pts) * tb * sfps + 0.5): p["hash"] for p in a}
    bmap = {int((p["pts"] - ofirst) * otb * sfps + 0.5): p["hash"] for p in b}
    for idx in range(i0, i1 + 1):
        if idx not in amap:
            raise TrimError("original frame %d not found while verifying" % idx)
        if bmap.get(idx - S) != amap[idx]:
            raise TrimError("frame %d of the original does not match frame %d of the cut" % (idx, idx - S))


def verify_cut(tools, orig, out_path, vidx_old, vidx_new, S, lo, hi, first_pts, tb, sfps, intra, audio_expect=None,
               orig_start_us=0, progress=None, quick=False, expect_frames=None):
    """Check the cut against the original. A cut is only used if this passes; otherwise the original file is used
    instead.
    Full (default): packet hashes of every used frame lo..hi must match frames lo-S..hi-S of the cut.
    Quick: frame count from the file header, plus hashes for the first and last seconds and a few samples in
    between.
    Both also check audio length and frame rate, and decode the ends of long-GOP (H.264/HEVC) cuts."""
    out_probe = tools.probe_file(out_path)
    ost = next(st for st in out_probe["streams"] if st["index"] == vidx_new)
    otb = parse_rational(ost["time_base"])
    otb = otb[0] / otb[1]
    if quick:
        head = tools.probe_packets(out_path, vidx_new, "%+#8")
        fk = next((p for p in head if p["key"]), None)
        if fk is None:
            raise TrimError("output has no keyframe")
        ofirst = 0 if fk["dts"] < 0 else fk["pts"]
        nb = str(ost.get("nb_frames") or "")
        if expect_frames and nb.isdigit():
            if (intra and int(nb) != expect_frames) or (not intra and int(nb) < expect_frames):
                raise TrimError("cut has %s frames, expected %d" % (nb, expect_frames))
        seen = list(head)
        windows = quick_windows(lo, hi, sfps)
        for w, (i0, i1) in enumerate(windows):
            a = tools.probe_packets(orig, vidx_old, interval_for(first_pts, tb, i0, i1, sfps), hashes=True)
            back = int(4 * sfps) if (not intra and i1 == hi) else 0  # keyframes for the decode check below
            b = tools.probe_packets(out_path, vidx_new, interval_for(ofirst, otb, i0 - S - back, i1 - S, sfps),
                                    hashes=True)
            compare_hashes(a, b, first_pts, tb, ofirst, otb, sfps, S, i0, i1)
            seen += b
            if progress:
                progress((w + 1) / len(windows))
    else:
        t0 = first_pts * tb + lo / sfps - 0.5
        t1 = first_pts * tb + (hi + 1) / sfps + 0.5
        interval = "%.6f%%%.6f" % (max(0.0, t0), t1) if t0 > 0 else "%%%.6f" % t1
        n = hi - lo + 1 + int(sfps)
        a = tools.probe_packets(orig, vidx_old, interval, hashes=True, expect=n,
                                progress=(lambda f: progress(0.5 * f)) if progress else None)
        b = tools.probe_packets(out_path, vidx_new, None, hashes=True, expect=n,
                                progress=(lambda f: progress(0.5 + 0.5 * f)) if progress else None)
        if not b:
            raise TrimError("output has no video packets")
        fk = next((p for p in b if p["key"]), None)
        if fk is None:
            raise TrimError("output has no keyframe")
        ofirst = 0 if fk["dts"] < 0 else fk["pts"]
        compare_hashes(a, b, first_pts, tb, ofirst, otb, sfps, S, lo, hi)
        seen = b
    if audio_expect:
        expect_us, tol_us = audio_expect
        for st in out_probe["streams"]:
            if st.get("codec_type") == "audio" and st.get("duration") not in (None, "N/A"):
                # where the audio ends: copied audio can keep a late start, which is not missing audio
                end = float(st["duration"]) + max(0.0, float(us_from_str(st.get("start_time")) or 0) / 1e6)
                if end * 1e6 < expect_us - tol_us:
                    raise TrimError("audio stream %d is %.3f s, expected %.3f s"
                                    % (st["index"], end, expect_us / 1e6))
    ofps = guess_fps(ost)
    if ofps and abs(ofps[0] / ofps[1] - sfps) > 1e-6:
        raise TrimError("cut file reports a different frame rate (%s)" % ost.get("r_frame_rate"))
    if not intra:
        # long-GOP: also prove the first and last used frames decode identically (catches missing
        # reference frames, which packet hashes alone cannot). Decoding starts two keyframes earlier
        # and runs forward, because seeking straight into open-GOP leading frames is unreliable.
        ostart = us_from_str(out_probe["format"].get("start_time")) or 0
        okeys = sorted({int((p["pts"] - ofirst) * otb * sfps + 0.5) for p in seen if p["key"]})
        for i0, n in ((lo, min(2, hi - lo + 1)), (max(lo, hi - 3), hi - max(lo, hi - 3) + 1)):
            ks = [k for k in okeys if 0 <= k <= i0 - S]
            k = ks[-2] if len(ks) >= 2 else 0
            count = (i0 - S - k) + n
            o_us = int(math.floor((first_pts * tb + (k + S) / sfps) * 1e6)) - orig_start_us
            n_us = int(math.floor((ofirst * otb + k / sfps) * 1e6)) - ostart
            h1 = tools.decoded_frames_md5(orig, vidx_old, max(0, o_us), count)[-n:]
            h2 = tools.decoded_frames_md5(out_path, vidx_new, max(0, n_us), count)[-n:]
            if len(h1) != n or h1 != h2:
                raise TrimError("decoded frames %d-%d differ after cutting" % (i0, i0 + n - 1))
    return out_probe


# --------------------------------------------------------------------------- XML rewrite

def shift_attr(doc, el, attr, D, lo=0, hi=None, notes=None):
    """Move a frame attribute of el back by D, clamped to lo..hi, noting any clamp. Not currently used; kept as a
    helper."""
    v = el.get(attr)
    if v is None:
        return
    n = doc.t(v) - D
    if n < lo or (hi is not None and n > hi):
        if notes is not None:
            notes.append("clamped %s %s on %s" % (attr, v, el.get("id") or el.tag))
        n = max(lo, n if hi is None else min(hi, n))
    el.set(attr, doc.fmt_like(v, n))


def shift_filters(doc, holder, D, notes):
    """Shift the in/out of every effect on holder by D, so timed and keyframed effects stay on the same frames of
    the picture after the trim. Effects with no range (in = out = 0) cover the whole clip and are left alone."""
    for f in holder.findall("filter"):
        fin, fout = f.get("in"), f.get("out")
        a = doc.t(fin) if fin else 0
        b = doc.t(fout) if fout else 0
        if a == 0 and b == 0:
            continue  # unbounded filter
        if a - D < 0:
            notes.append("effect %s started before the trimmed range and was clamped" % f.get("id"))
        if fin is not None or a - D != a:
            f.set("in", doc.fmt_like(fin if fin is not None else fout, max(0, a - D)))
        if fout is not None:
            f.set("out", doc.fmt_like(fout, max(0, b - D)))


def shift_bin_props(doc, el, D, new_len, notes):
    """Shift a bin clip's positions by D and clamp them to the new length: zone in/out, monitor and thumbnail
    positions, clip markers and subclips. Markers outside the kept range are dropped (and noted) because they would
    point past the end of the new file."""
    for name in ("kdenlive:zone_in", "kdenlive:zone_out") + BIN_POSITION_PROPS:
        v = get_prop(el, name)
        if v is not None and v != "":
            n = min(max(0, doc.t(v) - D), new_len - 1)
            set_prop(el, name, doc.fmt_like(v, n))
    mk = get_prop(el, "kdenlive:markers")
    if mk:
        try:
            arr = json.loads(mk)
            kept = []
            for item in arr:
                pos = int(item.get("pos", 0)) - D
                if 0 <= pos <= new_len - 1:
                    item["pos"] = pos
                    kept.append(item)
                else:
                    notes.append("dropped marker '%s' (outside the kept range)" % item.get("comment", ""))
            set_prop(el, "kdenlive:markers", json.dumps(kept, indent=4))
        except (ValueError, TypeError):
            notes.append("could not parse clip markers, left unchanged")
    zones = get_prop(el, "kdenlive:clipzones")
    if zones:
        try:
            arr = json.loads(zones)
            for z in arr:
                zi = min(max(0, int(z.get("in", 0)) - D), new_len - 1)
                zo = min(max(0, int(z.get("out", 0)) - D), new_len - 1)
                if zi != int(z.get("in", 0)) - D or zo != int(z.get("out", 0)) - D:
                    notes.append("subclip '%s' was clamped to the kept range" % z.get("name", ""))
                z["in"], z["out"] = zi, zo
            set_prop(el, "kdenlive:clipzones", json.dumps(arr, indent=4))
        except (ValueError, TypeError):
            notes.append("could not parse subclips, left unchanged")


def remap_streams(el, mapping, nb):
    """Renumber stream indexes on a media element when the cut dropped streams (e.g. data or timecode tracks):
    audio_index, video_index and the meta.media.N.* properties. Without this Kdenlive could pick the wrong stream.
    Returns False when nothing needed changing."""
    if all(k == v for k, v in mapping.items()) and len(mapping) == max(mapping) + 1:
        return False
    for name in ("audio_index", "video_index"):
        v = get_prop(el, name)
        if v is not None and v.lstrip("-").isdigit() and int(v) >= 0 and int(v) in mapping:
            set_prop(el, name, str(mapping[int(v)]))
    for p in list(el.findall("property")):
        m = re.match(r"^meta\.(media|attr)\.(\d+)\.(.*)$", p.get("name") or "")
        if m:
            old = int(m.group(2))
            if old in mapping:
                p.set("name", "meta.%s.%d.%s" % (m.group(1), mapping[old], m.group(3)))
            else:
                el.remove(p)
    if get_prop(el, "meta.media.nb_streams") is not None:
        set_prop(el, "meta.media.nb_streams", str(nb))
    return True


def rewrite_source(doc, src, offsets, new_hash, new_size, mapping):
    """Point every element of a trimmed source at the new file and shift its frames: resource (and timewarp's
    'speed:path' form), original and proxy links, file hash and size, length and in/out, stream indexes, bin
    markers and zones, effect ranges, and the in/out of every timeline use and bin entry, each by its element's
    offset D."""
    notes = src.notes
    new_orig_xml = doc.relpath_for_xml(src.out_path)
    new_proxy_xml = doc.relpath_for_xml(src.new_proxy) if src.proxy_ok else None
    for m in src.medias:
        el = m.elem
        D, nl, new_out = offsets[m.id]
        uses_proxy = m.proxy is not None and m.resource == m.proxy
        if uses_proxy and src.proxy_ok:
            res = new_proxy_xml
        else:
            res = new_orig_xml
        if m.is_warp:
            res_abs = src.new_proxy if (uses_proxy and src.proxy_ok) else src.out_path
            set_prop(el, "resource", "%s:%s" % (m.warp_prefix, res_abs))
            set_prop(el, "warp_resource", res)
        else:
            set_prop(el, "resource", res)
        repoint_original(doc, el, new_orig_xml)
        if m.proxy is not None:
            if src.proxy_ok:
                set_prop(el, "kdenlive:proxy", new_proxy_xml)
            else:
                del_prop(el, "kdenlive:proxy")
        if get_prop(el, "kdenlive:file_hash") is not None:
            set_prop(el, "kdenlive:file_hash", new_hash)
        if get_prop(el, "kdenlive:file_size") is not None:
            set_prop(el, "kdenlive:file_size", str(new_size))
        old_len = get_prop(el, "length")
        if old_len is not None:
            set_prop(el, "length", doc.fmt_like(old_len, nl))
        if el.get("in") is not None:
            el.set("in", doc.fmt_like(el.get("in"), 0))
        if el.get("out") is not None:
            el.set("out", doc.fmt_like(el.get("out"), new_out))
        dur = get_prop(el, "kdenlive:duration")
        if dur:
            set_prop(el, "kdenlive:duration", doc.fmt_like(dur, nl))
        if mapping is not None and remap_streams(el, mapping, len(mapping)):
            notes.append("stream indexes renumbered on %s (non audio/video streams were dropped)" % m.id)
        if not m.is_warp:
            shift_bin_props(doc, el, D, nl, notes)
        shift_filters(doc, el, D, notes)
    # timeline uses: same frames, positions moved back by the element's offset
    for u in src.uses:
        D, nl, new_out = offsets[u.media.id]
        h = u.holder
        if h.get("in") is not None:
            h.set("in", doc.fmt_like(h.get("in"), u.a - D))
        if h.get("out") is not None:
            h.set("out", doc.fmt_like(h.get("out"), u.b - D))
        shift_filters(doc, h, D, notes)
    # bin entries span the whole new file
    for m, entry in doc.bin_entries:
        if m in src.medias:
            D, nl, new_out = offsets[m.id]
            if entry.get("in") is not None:
                entry.set("in", doc.fmt_like(entry.get("in"), 0))
            if entry.get("out") is not None:
                entry.set("out", doc.fmt_like(entry.get("out"), new_out))


# --------------------------------------------------------------------------- report

def print_report(doc, sources):
    """Print what was found for each source: length, each use (track, timeline position, source range, speed), the
    used range, the planned cut and saving, notes and skip reasons. This is all of --report's output and the start
    of every log."""
    log("Project fps: %d/%d (%.3f)" % (doc.fps_num, doc.fps_den, doc.fps))
    if doc.old_root:
        log("Project was moved: its saved folder %s no longer exists, so its files are looked for in %s "
            "(as Kdenlive does)" % (doc.old_root, doc.root_dir))
    for src in sources:
        log("")
        log("== %s" % src.name)
        log("   path: %s" % src.key)
        if src.n_frames:
            log("   length: %s (%d frames)%s" % (fmt_secs(src.n_frames / src.sfps), src.n_frames,
                                               ", %.0f MB" % (src.size / 1e6) if src.size else ""))
        for u in sorted(src.uses, key=lambda u: (u.where, u.tl_pos)):
            m = u.media
            sp = "" if not m.is_warp else "  speed %g%s" % (m.speed, " (reverse)" if m.speed < 0 else "")
            sfps = src.sfps or doc.fps
            lo, hi = (m.src_frame(u.a, sfps), m.src_frame(u.b, sfps)) if src.sfps else (u.a, u.b)
            lo, hi = min(lo, hi), max(lo, hi)
            log("   - %-12s at %s  source %s -> %s  (%s of source, %s on timeline)%s" % (
                u.where, fmt_secs(u.tl_pos / doc.fps), fmt_secs(lo / sfps), fmt_secs((hi + 1) / sfps),
                fmt_secs((hi - lo + 1) / sfps), fmt_secs((u.b - u.a + 1) / doc.fps), sp))
        if src.need:
            lo, hi = src.need
            log("   used range: %s -> %s (%s)" % (fmt_secs(lo / src.sfps), fmt_secs((hi + 1) / src.sfps),
                                                 fmt_secs((hi - lo + 1) / src.sfps)))
        if src.plan:
            p = src.plan
            log("   cut: frames %d-%d = %s -> %s, keeps %s, saves ~%.0f%%%s" % (
                p["S"], p["E"], fmt_secs(p["S"] / src.sfps), fmt_secs((p["E"] + 1) / src.sfps),
                fmt_secs(p["K"] / src.sfps), p["saving"] * 100,
                " (start snapped to keyframe)" if not src.intra else ""))
        for n in src.notes:
            log("   note: %s" % n)
        if src.skip:
            log("   SKIP: %s" % src.skip)


# --------------------------------------------------------------------------- live dashboard

def fmt_dur(sec):
    """Seconds as H:MM:SS for the dashboard's elapsed and remaining time."""
    sec = int(max(0, sec))
    return "%d:%02d:%02d" % (sec // 3600, sec // 60 % 60, sec % 60)


class Dashboard:
    """Full-screen progress display in the terminal (plain log lines when not a terminal), so a long run can be
    followed at a glance. Everything is also written to a log file in the output folder."""

    STYLES = {"b": "1", "dim": "2", "ok": "32", "warn": "33", "bad": "31", "acc": "36"}

    def __init__(self, title, out_dir, log_path, live):
        """Open the log file (appending, with a header per run). In live mode, switch the terminal to its alternate
        screen and hide the cursor, so the display redraws in place and the terminal is restored on exit."""
        self.title, self.out_dir, self.live = title, out_dir, live
        self.color = live and "NO_COLOR" not in os.environ
        self.logf = open(log_path, "a", encoding="utf-8") if log_path else None
        self.log_error = None  # set if writing the log fails (e.g. a network share drops); the run carries on
        self.write_log("\n===== kdenlive_trim run %s =====\n" % time.strftime("%Y-%m-%d %H:%M:%S"))
        self.t0 = time.time()
        self.phase, self.phase_total, self.phase_done = "Starting", 0, 0
        self.work_total = self.work_done = 0.0
        self.work_t0 = None
        self.job_weight = self.job_frac = 0.0
        self.span = (0.0, 1.0)
        self.counts = dict(trim_total=0, trim_done=0, copy_total=0, copy_done=0, problems=0, saved=0)
        self.task = self.step = None
        self.step_t0 = time.time()
        self.recent = deque(maxlen=8)
        self.last_draw = 0.0
        if live:
            sys.stdout.write("\x1b[?1049h\x1b[?25l")
            sys.stdout.flush()
            self.draw(True)

    # ---- state
    def write_log(self, text):
        """Append to the log file. If that fails (the share dropped, the disk is full) the log is given up for the
        rest of the run instead of stopping it; the summary then says so."""
        if not self.logf:
            return
        try:
            self.logf.write(text)
            self.logf.flush()
        except OSError as e:
            self.log_error = "%s (%s)" % (e.strerror or e, self.logf.name)
            try:
                self.logf.close()
            except OSError:
                pass
            self.logf = None

    def log(self, msg):
        """Write a line to the log file; in plain mode also print it (in live mode the screen shows the dashboard
        instead)."""
        self.write_log(msg + "\n")
        if not self.live:
            print(msg, flush=True)

    def set_phase(self, name, total=0):
        """Start a named phase (Analysing, Processing, Writing project); total is the file count for the phase bar."""
        self.phase, self.phase_total, self.phase_done = name, total, 0
        self.task = self.step = None
        self.draw(True)

    def tick(self, name=""):
        """One more file done in the current phase; name is shown as the file being worked on."""
        self.phase_done += 1
        self.task = {"action": self.phase, "name": name} if name else self.task
        self.draw()

    def start_work(self, total):
        """Start the overall progress bar. total is the estimated work for the whole run (bytes read and written),
        which the time-left estimate is based on."""
        self.work_total, self.work_done, self.work_t0 = max(total, 1.0), 0.0, time.time()

    def begin(self, action, name, size=None, info="", clip=None, weight=0.0):
        """Start one file (a trim or a copy). weight is its share of the total work; clip = (S, E, frames) draws
        the bar showing which part of the file is kept."""
        self.task = dict(action=action, name=name, size=size, info=info, clip=clip)
        self.job_weight, self.job_frac, self.step = weight, 0.0, None
        if not self.live:
            self.log("\n-> %s %s%s" % (action, name, "  " + info if info else ""))
        self.draw(True)

    def set_step(self, name, span=(0.0, 1.0)):
        """Start a step within the current file. span is the part of the file's work this step covers, so the steps
        add up smoothly in the overall bar."""
        self.step = {"name": name, "frac": None, "rate": None}
        self.span, self.step_t0 = span, time.time()
        self.job_frac = span[0]
        self.draw(True)

    def step_progress(self, frac, bytes_done=None):
        """Progress (0..1) of the current step, called from the ffmpeg/ffprobe readers and the copy thread.
        bytes_done adds a MB/s figure."""
        if self.step is None:
            return
        self.step["frac"] = frac
        if bytes_done:
            self.step["rate"] = bytes_done / max(0.1, time.time() - self.step_t0)
        self.job_frac = self.span[0] + (self.span[1] - self.span[0]) * frac
        self.draw()

    def end(self, status, text):
        """Finish the current file with a status (OK, COPY, SKIP, NOTE, FAIL): add its weight to the work done,
        count problems, and add it to the Recent list and the log."""
        self.work_done += self.job_weight
        self.job_weight = self.job_frac = 0.0
        self.task = self.step = None
        if status in ("FAIL",):
            self.counts["problems"] += 1
        self.recent.appendleft((status, text))
        if not self.live:
            self.log("   %s: %s" % (status.lower(), text))
        else:
            self.write_log("   %s: %s\n" % (status.lower(), text))
        self.draw(True)

    # ---- drawing
    def _s(self, text, style=None):
        """Wrap text in an ANSI style code, unless colour is off (NO_COLOR set, or not a terminal)."""
        if not self.color or not style:
            return text
        return "\x1b[%sm%s\x1b[0m" % (self.STYLES[style], text)

    def _bar(self, frac, width):
        """Text progress bar: solid for done, shaded for remaining."""
        n = int(round(max(0.0, min(1.0, frac)) * width))
        return "\u2588" * n + "\u2591" * (width - n)

    def _line(self, parts, width):
        """parts: list of (text, style). Truncates to the terminal width by visible length, so long paths never
        wrap and break the layout."""
        out, used = [], 0
        for text, style in parts:
            room = width - used
            if room <= 0:
                break
            if len(text) > room:
                text = text[:max(0, room - 1)] + "\u2026"
            out.append(self._s(text, style))
            used += len(text)
        return "".join(out)

    def draw(self, force=False):
        """Redraw the whole screen from the current state. At most 4 times a second unless forced, because progress
        callbacks arrive far more often than that."""
        if not self.live:
            return
        now = time.time()
        if not force and now - self.last_draw < 0.25:
            return
        self.last_draw = now
        width = max(40, shutil.get_terminal_size((100, 30)).columns - 1)
        barw = max(10, min(40, width - 40))
        L = []
        L.append(self._line([("  Kdenlive trim + archive   ", "b"), (self.title, "acc")], width))
        L.append(self._line([("  Output    ", "dim"), (self.out_dir, None)], width))
        elapsed = now - self.t0
        left = ""
        if self.work_t0 and self.work_done + self.job_weight * self.job_frac > 0:
            done = self.work_done + self.job_weight * self.job_frac
            rate = done / max(1.0, now - self.work_t0)
            left = "   Remaining  ~%s" % fmt_dur((self.work_total - done) / max(rate, 1e-9))
        L.append(self._line([("  Elapsed   ", "dim"), (fmt_dur(elapsed) + left, None)], width))
        L.append("")
        if self.work_t0:
            frac = min(1.0, (self.work_done + self.job_weight * self.job_frac) / self.work_total)
            L.append(self._line([("  Overall   ", "b"), (self._bar(frac, barw), "acc"), ("  %3d%%" % (frac * 100), "b")], width))
        else:
            frac = self.phase_done / self.phase_total if self.phase_total else 0
            L.append(self._line([("  %-9s " % self.phase, "b"), (self._bar(frac, barw), "acc"),
                                 ("  %d of %d files" % (self.phase_done, self.phase_total), None)], width))
        c = self.counts
        L.append(self._line([("  Trimmed ", "dim"), ("%d/%d" % (c["trim_done"], c["trim_total"]), "b"),
                             ("    Copied ", "dim"), ("%d/%d" % (c["copy_done"], c["copy_total"]), "b"),
                             ("    Problems ", "dim"), (str(c["problems"]), "bad" if c["problems"] else "b"),
                             ("    Saved ", "dim"), ("%.1f GB" % (max(0, c["saved"]) / 1e9), "ok")], width))
        L.append("")
        t = self.task
        if t:
            size = "  (%s)" % fmt_size(t["size"]) if t.get("size") else ""
            L.append(self._line([("  Now       ", "b"), (t["action"] + "  ", "acc"), (t["name"], None), (size, "dim")], width))
            if t.get("info"):
                L.append(self._line([("            ", None), (t["info"], "dim")], width))
            if t.get("clip"):
                lo, hi, n = t["clip"]
                w = max(10, min(60, width - 14))
                a, b = int(lo / max(n, 1) * w), max(int(lo / max(n, 1) * w) + 1, int(round((hi + 1) / max(n, 1) * w)))
                L.append(self._line([("  source    |", "dim"), ("\u00b7" * a, "dim"), ("\u2588" * (b - a), "ok"),
                                     ("\u00b7" * (w - b), "dim"), ("|", "dim")], width))
            st = self.step
            if st:
                if st["frac"] is None:
                    spin = "|/-\\"[int(now * 4) % 4]
                    L.append(self._line([("  step      ", "dim"), (st["name"], None),
                                         ("  %s  %ds" % (spin, now - self.step_t0), "dim")], width))
                else:
                    rate = "   %.0f MB/s" % (st["rate"] / 1e6) if st.get("rate") else ""
                    L.append(self._line([("  step      ", "dim"), ("%-18s" % st["name"], None),
                                         (self._bar(st["frac"], max(10, barw - 10)), "acc"),
                                         ("  %3d%%%s" % (st["frac"] * 100, rate), None)], width))
        else:
            L.append(self._line([("  Now       ", "b"), (self.phase, "dim")], width))
        L.append("")
        if self.recent:
            L.append(self._line([("  Recent", "b")], width))
            style = {"OK": "ok", "COPY": "ok", "SKIP": "warn", "NOTE": "warn", "FAIL": "bad"}
            for status, text in self.recent:
                L.append(self._line([("    %-5s " % status, style.get(status)), (text, None)], width))
        sys.stdout.write("\x1b[H\x1b[J" + "\n".join(L) + "\n")
        sys.stdout.flush()

    def close(self):
        """Restore the normal screen and cursor and close the log file. Always called at the end, also after Ctrl-C
        or an error, so the terminal is never left in the alternate screen."""
        if self.live:
            sys.stdout.write("\x1b[?25h\x1b[?1049l")
            sys.stdout.flush()
            self.live = False
        if self.logf:
            try:
                self.logf.close()
            except OSError:
                pass
            self.logf = None


def fmt_size(n):
    """Bytes as KB/MB/GB (decimal units, as Finder shows them) for display."""
    return "%.1f GB" % (n / 1e9) if n >= 1e9 else "%.0f MB" % (n / 1e6) if n >= 1e6 else "%.0f KB" % (n / 1e3)


def keep_awake():
    """On macOS, stop the Mac sleeping (and dropping network shares) until this process exits."""
    if sys.platform == "darwin" and shutil.which("caffeinate"):
        try:
            subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except OSError:
            pass


# --------------------------------------------------------------------------- main

def inside(path, folder):
    """True if path is inside folder at any depth. Compares normalised paths with a trailing separator, so '/a/bc'
    does not count as inside '/a/b'."""
    return os.path.normpath(path).startswith(os.path.normpath(folder) + os.sep)


REF_PROPS = ("resource", "warp_resource", "kdenlive:originalurl", "kdenlive:original.resource", "kdenlive:proxy",
             "luma", "av.file", "filename")
CLIP_PATH_PROPS = ("resource", "warp_resource", "kdenlive:originalurl", "kdenlive:original.resource", "kdenlive:proxy")


def referenced_files(doc):
    """Absolute paths of every file the project refers to (media, proxies, title images, LUTs, wipes). Used after
    saving to prove the new project is self-contained and to report which original folders it still uses."""
    out = set()
    for el in doc.root.iter():
        if el.tag not in ("producer", "chain", "filter", "transition", "link"):
            continue
        svc = get_prop(el, "mlt_service", "")
        for p in el.findall("property"):
            name, v = p.get("name"), (p.text or "").strip()
            if not v:
                continue
            if name == "xmldata":
                out.update(doc.abspath(u) for u in re.findall(r'url="([^"]+)"', v))
                continue
            if v == "-":
                continue
            if name not in REF_PROPS:
                if el.tag in ("filter", "transition", "link") and "/" in v and os.path.isfile(doc.abspath(v)):
                    out.add(doc.abspath(v))
                continue
            if name == "resource" and svc == "timewarp" and ":" in v:
                v = v.split(":", 1)[1]
            a = doc.abspath(v)
            if "/" in v or os.path.exists(a):
                out.add(a)
    return out


IMAGE_SERVICES = ("qimage", "pixbuf")
SUBDIRS = {"video": "videos", "audio": "sounds", "image": "images", "proxy": "proxy",  # Kdenlive archive names
           "slideshow": "slideshows", "text": "texts", "luma": "lumas", "other": "others"}
CLEANUP = set()  # partial files to remove if the run is interrupted


def copy_with_progress(src, dst):
    """shutil.copyfile (which keeps the OS's fast copy paths) with the destination size polled for the UI. The copy
    runs in a background thread so the dashboard can update; any error is re-raised here."""
    total = os.path.getsize(src) or 1
    box = {}

    def run():
        """Do the copy, keeping any error for the calling thread to raise."""
        try:
            shutil.copyfile(src, dst)
        except BaseException as e:  # noqa: B902 - re-raised in the caller's thread
            box["err"] = e
    t = threading.Thread(target=run, daemon=True)
    t.start()
    while t.is_alive():
        t.join(0.25)
        if UI is not None:
            try:
                UI.step_progress(os.path.getsize(dst) / total, bytes_done=os.path.getsize(dst))
            except OSError:
                pass
    if box.get("err") is not None:
        raise box["err"]


# errors that another try won't fix (disk full, permissions, file gone); anything else during a copy, such as the
# EIO or EINVAL a network share returns while it reconnects, gets one more try
COPY_FATAL = {errno.ENOSPC, errno.EDQUOT, errno.EROFS, errno.EACCES, errno.EPERM, errno.ENOENT, errno.ENAMETOOLONG}
COPY_RETRY_WAIT = 10  # seconds before the second try, to give a share time to recover


class Archive:
    """Output folder laid out like a Kdenlive project archive. Hands out unique file names and remembers proxies
    already copied, so a file used by several clips is copied once."""

    def __init__(self, out_dir):
        """Empty bookkeeping; folders are only created when something is written to them."""
        self.out_dir = out_dir
        self.taken = set()
        self.proxy_map = {}  # original proxy path -> copied proxy path (or None)

    def dir(self, kind):
        """Path of the subfolder for a kind of file (videos, sounds, images...)."""
        return os.path.join(self.out_dir, SUBDIRS[kind])

    def copy(self, path, kind, sub=None):
        """Copy path into the folder for kind, verified. Returns the new path or raises. The copy is written to a
        .part file and only renamed into place once its size and Kdenlive hash match the original, so an
        interrupted or bad copy never looks finished. A copy that does not match, or that hits a read or write error,
        is tried once more after a pause (a one-off network glitch), and the error says what went wrong. The
        original's modification time is kept."""
        dest = self.dir(kind) if sub is None else os.path.join(self.dir(kind), sub)
        os.makedirs(dest, exist_ok=True)
        final = unique_path(os.path.join(dest, os.path.basename(path)), self.taken)
        tmp = final + ".part" + os.path.splitext(final)[1]
        CLEANUP.add(tmp)
        try:
            for attempt in (1, 2):
                error = None
                try:
                    copy_with_progress(path, tmp)
                    problem = copy_mismatch(path, tmp)
                except OSError as e:
                    if e.errno in COPY_FATAL:
                        raise
                    error = problem = "%s: %s" % (errno.errorcode.get(e.errno, "error"), e.strerror or e)
                if not problem:
                    break
                log("   copy of %s %s (%s)%s" % (
                    os.path.basename(path), "failed" if error else "does not match the original", problem,
                    ", trying once more in %d s" % COPY_RETRY_WAIT if attempt == 1 else ""))
                if attempt == 1:
                    time.sleep(COPY_RETRY_WAIT)
            if error:
                raise TrimError("read or write error, twice (%s)" % error)
            if problem:
                raise TrimError("copy does not match the original, twice (%s)" % problem)
            os.replace(tmp, final)
            st = os.stat(path)
            os.utime(final, (st.st_atime, st.st_mtime))
            return final
        except (OSError, TrimError):
            if os.path.exists(tmp):
                os.remove(tmp)
            raise

    def copy_proxy(self, proxy):
        """Copy a proxy into proxy/ once, however many clips use it, and return the new path. None if the proxy is
        missing or the copy failed, so the caller drops the link instead."""
        if proxy not in self.proxy_map:
            new = None
            if os.path.isfile(proxy):
                try:
                    new = self.copy(proxy, "proxy")
                except (OSError, TrimError):
                    new = None
            self.proxy_map[proxy] = new
        return self.proxy_map[proxy]


def copy_mismatch(src, dst):
    """None if dst matches src (same size, same first and last 1 MB), otherwise what differs. A mismatch means the
    bytes written were not the bytes read: usually the network share or a disk, not the file itself."""
    a, b = os.path.getsize(src), os.path.getsize(dst)
    if a != b:
        return "the copy is %s bytes, the original %s bytes" % (format(b, ","), format(a, ","))
    if kdenlive_file_hash(dst) != kdenlive_file_hash(src):
        return "same size, but the start or end of the file differs"
    return None


def repoint_original(doc, el, path):
    """Point the element's original-file properties (kdenlive:originalurl, kdenlive:original.resource) at path, if
    present. Kdenlive uses these when proxies are on, so they must point at the archived file, not the old folder."""
    for name in ("kdenlive:originalurl", "kdenlive:original.resource"):
        if get_prop(el, name) is not None:
            set_prop(el, name, path)


def copy_source(doc, src, archive, kind, proxies):
    """Copy an untrimmed audio/video file (and its proxy) into the archive and point the project at it. Used for
    files not worth trimming and for trims that failed."""
    final = archive.copy(src.key, kind)
    proxy = next((m.proxy for m in src.medias if m.proxy), None)
    new_proxy = archive.copy_proxy(proxy) if (proxy and proxies == "trim") else None
    for m in src.medias:
        el = m.elem
        uses_proxy = m.proxy is not None and m.resource == m.proxy
        res = new_proxy if (uses_proxy and new_proxy) else final
        if m.is_warp:
            set_prop(el, "resource", "%s:%s" % (m.warp_prefix, res))
            set_prop(el, "warp_resource", res)
        else:
            set_prop(el, "resource", res)
        repoint_original(doc, el, final)
        if m.proxy is not None:
            if new_proxy:
                set_prop(el, "kdenlive:proxy", new_proxy)
            else:
                del_prop(el, "kdenlive:proxy")
    src.copied_to = final
    src.new_proxy = new_proxy
    if proxy and not new_proxy:
        src.notes.append("proxy %s; proxy link removed, rebuild it in Kdenlive"
                         % ("not kept (--proxies drop)" if proxies != "trim" else "file missing or could not be copied"))


def image_groups(doc):
    """{absolute image path: [producer elements]} for still-image clips (slideshows excluded). Grouped by file so
    an image used by several clips is copied once."""
    groups = {}
    for el in doc.root.iter("producer"):
        if get_prop(el, "mlt_service", "") not in IMAGE_SERVICES:
            continue
        orig = (get_prop(el, "kdenlive:originalurl") or get_prop(el, "kdenlive:original.resource")
                or get_prop(el, "resource") or "")
        if not orig or re.search(r"%\d*d|\.all\.", orig):
            continue
        groups.setdefault(doc.abspath(orig), []).append(el)
    return groups


def copy_image(doc, path, els, archive, proxies):
    """Copy one still image (and its proxy, if any) into images/ and point every clip that uses it at the copy."""
    final = archive.copy(path, "image")
    for el in els:
        res = get_prop(el, "resource")
        proxy = get_prop(el, "kdenlive:proxy")
        has_proxy = bool(proxy) and len(proxy) > 1
        proxy_abs = doc.abspath(proxy) if has_proxy else None
        uses_proxy = has_proxy and res and doc.abspath(res) == proxy_abs
        new_proxy = archive.copy_proxy(proxy_abs) if (has_proxy and proxies == "trim") else None
        if has_proxy:
            if new_proxy:
                set_prop(el, "kdenlive:proxy", new_proxy)
            else:
                del_prop(el, "kdenlive:proxy")
        set_prop(el, "resource", new_proxy if (uses_proxy and new_proxy) else final)
        repoint_original(doc, el, final)
    return final


def xml_attr_escape(v):
    """Escape text for an XML attribute. Needed when writing paths into a title's XML, which is stored as text
    inside the project."""
    return v.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def xml_attr_unescape(v):
    """Reverse of xml_attr_escape, for reading paths found in a title's XML."""
    return v.replace("&quot;", '"').replace("&lt;", "<").replace("&gt;", ">").replace("&amp;", "&")


def slideshow_files(pattern):
    """Files matched by a Kdenlive slideshow resource (folder/.all.jpg or folder/img_%04d.png), so the whole image
    sequence is copied."""
    d, base = os.path.split(pattern.split("?", 1)[0])
    if not os.path.isdir(d):
        return []
    names = sorted(os.listdir(d))
    if base.startswith(".all."):
        ext = "." + base[5:].lower()
        return [os.path.join(d, n) for n in names if n.lower().endswith(ext) and os.path.isfile(os.path.join(d, n))]
    m = re.search(r"%0?\d*d", base)
    if m:
        rx = re.escape(base[:m.start()]) + r"\d+" + re.escape(base[m.end():])
        return [os.path.join(d, n) for n in names if re.fullmatch(rx, n)]
    return []


def is_slideshow(resource):
    """True if a resource is a Kdenlive image-sequence pattern rather than a single file."""
    base = os.path.basename((resource or "").split("?", 1)[0])
    return base.startswith(".all.") or bool(re.search(r"%0?\d*d", base))


def other_assets(doc, out_dir, handled_ids):
    """Every remaining file the project refers to, as jobs: (kind, path, apply_fn(new_path), label).
    Covers slideshows, images inside titles, title templates, wipe (luma) files and files used by effects. Each job
    carries the functions that update the project once the file's new path is known."""
    jobs, seen = [], {}

    def add(kind, path, label, apply):
        """Queue a file once (files already in the archive are skipped); further users of the same file only add
        their update function."""
        if not path or inside(path, out_dir):
            return
        if path in seen:
            seen[path][2].append(apply)
            return
        job = [kind, path, [apply], label]
        seen[path] = job
        jobs.append(job)

    for el in doc.root.iter():
        if el.tag not in ("producer", "chain", "filter", "transition", "link"):
            continue
        svc = get_prop(el, "mlt_service", "")
        props = el.findall("property")
        # slideshows
        if el.tag == "producer" and svc in IMAGE_SERVICES:
            orig = get_prop(el, "kdenlive:originalurl") or get_prop(el, "resource") or ""
            if is_slideshow(orig) and slideshow_files(doc.abspath(orig)):
                # default arguments bind this loop's element; a plain closure would see the last one
                def apply_slide(new_dir, el=el, orig=orig):
                    """Point the slideshow's resource properties at the copied folder."""
                    base = os.path.basename(orig)
                    for name in ("resource", "kdenlive:originalurl", "kdenlive:original.resource"):
                        v = get_prop(el, name)
                        if v and os.path.basename(v) == base:
                            set_prop(el, name, os.path.join(new_dir, base))
                add("slideshow", doc.abspath(orig), os.path.basename(os.path.dirname(doc.abspath(orig))), apply_slide)
            continue
        if svc == "kdenlivetitle":
            for prop in props:
                if prop.get("name") == "xmldata" and prop.text:
                    for raw in set(re.findall(r'url="([^"]+)"', prop.text)):
                        path = doc.abspath(xml_attr_unescape(raw))
                        if os.path.isfile(path):
                            def apply_title(new, prop=prop, raw=raw):
                                """Replace this image's path inside the title's XML."""
                                prop.text = prop.text.replace('url="%s"' % raw, 'url="%s"' % xml_attr_escape(new))
                            add("image", path, os.path.basename(path), apply_title)
                elif prop.get("name") == "resource" and prop.text and os.path.isfile(doc.abspath(prop.text)):
                    def apply_text(new, prop=prop):
                        """Point the title clip at its copied template file."""
                        prop.text = new
                    add("text", doc.abspath(prop.text), os.path.basename(prop.text), apply_text)
            continue
        if el.tag in ("producer", "chain"):
            if el.get("id") in handled_ids:
                continue
            res = get_prop(el, "resource")
            if res and os.path.isfile(doc.abspath(res)):  # e.g. animations, nested .mlt playlists
                def apply_res(new, el=el):
                    """Point the producer (and its original-file properties) at the copied file."""
                    set_prop(el, "resource", new)
                    repoint_original(doc, el, new)
                add("other", doc.abspath(res), os.path.basename(res), apply_res)
            continue
        # effects, transitions, links: any property that names an existing file
        for prop in props:
            v = (prop.text or "").strip()
            if "/" not in v or prop.get("name") == "xmldata":
                continue
            path = doc.abspath(v)
            if os.path.isfile(path):
                name = prop.get("name") or ""
                kind = "luma" if (el.tag == "transition" and ("luma" in name or name == "resource")) else "other"
                def apply_prop(new, prop=prop):
                    """Point this effect or transition property at the copied file."""
                    prop.text = new
                add(kind, path, os.path.basename(path), apply_prop)
    return jobs


def has_video_stream(src, tools):
    """True if the file has a real video stream (cover art excluded). Decides whether an untrimmed file goes in
    videos/ or sounds/. Probes the file only if planning did not already."""
    if src.probe is None:
        if not os.path.isfile(src.key):
            return False
        try:
            src.probe = tools.probe_file(src.key)
        except TrimError:
            return False
    return any(st.get("codec_type") == "video" and not st.get("disposition", {}).get("attached_pic")
               for st in src.probe.get("streams", []))


def copy_plan(doc, sources, tools, out_dir, todo):
    """Everything else the project uses, so the archive is complete: untrimmed videos, audio, images. Returns
    ([(source, 'video' or 'audio')], [(image path, elements)])."""
    av = [(s, "video" if has_video_stream(s, tools) else "audio") for s in sources
          if s not in todo and not s.in_media_dir and os.path.isfile(s.key)]
    images = [(path, els) for path, els in sorted(image_groups(doc).items())
              if os.path.isfile(path) and not inside(path, out_dir)]
    return av, images


def write_problem(folder):
    """None if we can create files in folder (created if missing, then removed again), else the error. Run before
    any work, so permission problems (common on network shares) show up at once instead of after an hour."""
    created = []
    try:
        d = folder
        while not os.path.isdir(d):
            created.append(d)
            d = os.path.dirname(d)
        for c in reversed(created):
            os.mkdir(c)
        probe = os.path.join(folder, ".kdenlive_trim_write_test")
        with open(probe, "w") as f:
            f.write("x")
        os.remove(probe)
        return None
    except OSError as e:
        return "%s (%s)" % (e.strerror or e, e.filename or folder)
    finally:
        for c in created:
            try:
                os.rmdir(c)
            except OSError:
                pass


def unique_path(path, taken):
    """path, or path with _2, _3... added, so two source files with the same name never overwrite each other in the
    archive. Names handed out are remembered in taken."""
    base, ext = os.path.splitext(path)
    n = 2
    while path in taken or os.path.exists(path):
        path = "%s_%d%s" % (base, n, ext)
        n += 1
    taken.add(path)
    return path


def trim_one(src, args, doc, tools, archive):
    """Cut one source, verify it, trim its proxy and rewrite the project. Returns an error string or None. Files
    are written as .part and only renamed into place once checked, so a failure leaves nothing half-made; the
    original is then copied whole instead (unless --no-copy-unchanged)."""
    S, E = src.plan["S"], src.plan["E"]
    ext = os.path.splitext(src.key)[1].lower()
    if ext not in COPY_CONTAINERS:
        ext = ".mov"
    if ext in MP4_LIKE and any(audio_codec_for(st, args.audio).startswith("pcm_")
                               for st in src.probe["streams"] if st.get("codec_type") == "audio"):
        ext = ".mov"  # PCM audio is not reliably supported in MP4
    os.makedirs(archive.dir("video"), exist_ok=True)
    final = unique_path(os.path.join(archive.dir("video"), os.path.splitext(src.name)[0] + ext), archive.taken)
    tmp = final + ".part" + ext
    lo, hi = src.need
    to_end = src.n_frames is not None and E >= src.n_frames - 1
    try:
        # split this file's progress between cutting and checking by how much each reads
        cut_share = 1 / (1 + check_share(src, args.quick_check))
        UI.set_step("Cutting", (0.0, cut_share))
        mapping, cut_us = cut_file(tools, src.key, tmp, S, E, src.first_pts, src.tb, src.tbr, src.sfps, src.start_us,
                                   src.vstream["index"], src.probe, src.intra, args.audio, src.pkts, to_end,
                                   progress=UI.step_progress)
        UI.set_step("Checking samples" if args.quick_check else "Checking frames", (cut_share, 1.0))
        out_probe = verify_cut(tools, src.key, tmp, src.vstream["index"], mapping[src.vstream["index"]], S,
                               max(lo, S), min(hi, E), src.first_pts, src.tb, src.sfps, src.intra, cut_us,
                               src.start_us, progress=UI.step_progress, quick=args.quick_check,
                               expect_frames=E - S + 1)
        os.replace(tmp, final)
        st = os.stat(src.key)
        os.utime(final, (st.st_atime, st.st_mtime))
    except (TrimError, OSError) as e:
        if os.path.exists(tmp):
            os.remove(tmp)
        return "cut failed, original kept: %s" % e
    src.out_path = final
    # new clip length in project frames, from the cut's real duration (as Kdenlive will measure it)
    new_bin_len = int(round(us_from_str(out_probe["format"].get("duration")) * doc.fps / 1e6))
    offsets = element_offsets(src, S, new_bin_len, to_end)
    # recheck the frame mapping with the real file length; if it differs from the plan, the cut is not used
    if check_plan(src, S, E, offsets) != src.plan["drift"]:
        os.remove(final)
        return "cut failed, original kept: frame mapping check failed after cutting"
    new_hash, new_size = kdenlive_file_hash(final)
    src.new_size = new_size

    proxy = next((m.proxy for m in src.medias if m.proxy), None)
    if proxy:
        os.makedirs(archive.dir("proxy"), exist_ok=True)
        # Kdenlive names proxies after the clip's file hash, so the new proxy takes the new file's hash
        src.new_proxy = os.path.join(archive.dir("proxy"), new_hash + os.path.splitext(proxy)[1])
        if args.proxies == "trim" and os.path.isfile(proxy):
            UI.set_step("Trimming proxy", (1.0, 1.0))
            ptmp = src.new_proxy + ".part" + os.path.splitext(proxy)[1]
            try:
                pprobe = tools.probe_file(proxy)
                pv = next(s for s in pprobe["streams"] if s.get("codec_type") == "video")
                pfr = guess_fps(pv)
                if not pfr or abs(pfr[0] / pfr[1] - src.sfps) > 1e-6:
                    raise TrimError("proxy frame rate differs from the original")
                ptb = parse_rational(pv["time_base"])
                pk = next(p for p in tools.probe_packets(proxy, pv["index"], "%+#60") if p["key"])
                pfirst = 0 if pk["dts"] < 0 else pk["pts"]
                ppk = tools.probe_packets(proxy, pv["index"])
                for p in ppk:
                    p["idx"] = int((p["pts"] - pfirst) * ptb[0] / ptb[1] * src.sfps + 0.5)
                ppk = {p["idx"]: p for p in ppk}
                # the proxy is cut at the same frames, which needs every proxy frame to be a keyframe
                pwin = [ppk[i] for i in range(S, E + 1) if i in ppk]
                if len(pwin) != E - S + 1 or not all(p["key"] for p in pwin):
                    raise TrimError("proxy is not intra-frame or is missing frames")
                pmap, pcut_us = cut_file(tools, proxy, ptmp, S, E, pfirst, ptb[0] / ptb[1], ptb, src.sfps,
                                         us_from_str(pprobe["format"].get("start_time")) or 0, pv["index"], pprobe,
                                         True, args.audio, ppk, to_end, progress=UI.step_progress)
                verify_cut(tools, proxy, ptmp, pv["index"], pmap[pv["index"]], S, max(lo, S), min(hi, E),
                           pfirst, ptb[0] / ptb[1], src.sfps, True, pcut_us, quick=args.quick_check,
                           expect_frames=E - S + 1)
                os.replace(ptmp, src.new_proxy)
                src.proxy_ok = True
            except (TrimError, StopIteration, OSError) as e:
                if os.path.exists(ptmp):
                    os.remove(ptmp)
                src.notes.append("proxy not trimmed (%s); proxy link removed, rebuild it in Kdenlive" % e)
        elif args.proxies == "trim":
            src.notes.append("proxy file missing; proxy link removed, rebuild it in Kdenlive")
        else:
            src.notes.append("proxy link removed (--proxies drop), rebuild it in Kdenlive")
    # renumber stream indexes only if the cut dropped or reordered streams
    remap = mapping if any(k != v for k, v in mapping.items()) or len(src.probe["streams"]) != len(mapping) else None
    rewrite_source(doc, src, offsets, new_hash, new_size, remap)
    return None


# --------------------------------------------------------------------------- scan and prediction (front end)

def scan_progress(line):
    """Progress line on stderr during --report-json, read by the control dashboard to show a progress bar."""
    sys.stderr.write(line + "\n")
    sys.stderr.flush()


def _audio_streams(probe):
    """The audio stream fields predict() needs, from an ffprobe result."""
    keys = ("index", "codec_name", "sample_rate", "channels", "sample_fmt", "bits_per_raw_sample", "bit_rate",
            "duration")
    return [{k: st.get(k) for k in keys} for st in (probe or {}).get("streams", []) if st.get("codec_type") == "audio"]


def scan_data(doc, sources, tools, args, out_dir, images, others):
    """Everything predict() needs, as plain data: for each source its size, frames, both cut alternatives (exact
    and drift), audio streams and proxy, plus the images and other files that would be copied. Written by
    --report-json, so the front end can predict any combination of options without scanning again (only --handles
    and --search-seconds change the cuts themselves)."""
    items = []
    proxied = [s for s in sources if any(m.proxy for m in s.medias)]
    for s in sources:
        exists = os.path.isfile(s.key)
        d = {"name": s.name, "path": s.key, "exists": exists, "size": os.path.getsize(s.key) if exists else 0,
             "skip": s.skip, "in_media_dir": s.in_media_dir, "used": bool(s.uses)}
        if exists:
            d["has_video"] = has_video_stream(s, tools)
            d["audio"] = _audio_streams(s.probe)
            fmt = (s.probe or {}).get("format", {})
            d["duration"] = float(fmt["duration"]) if fmt.get("duration") not in (None, "N/A") else None
        if s.vstream is not None and s.sfps and s.n_frames and s.need:
            d.update(sfps=s.sfps, n_frames=s.n_frames, intra=getattr(s, "intra", None),
                     vcodec=s.vstream.get("codec_name"), need=list(s.need),
                     start_limited=getattr(s, "start_limited", False))
            alts = getattr(s, "alts", None) or {}
            if alts.get("exact"):
                S, E = alts["exact"][:2]
                d["exact"] = {"S": S, "E": E}
            if alts.get("drift"):
                S, E, n = alts["drift"]
                d["drift"] = {"S": S, "E": E, "frames": n}
        proxy = next((m.proxy for m in s.medias if m.proxy), None)
        if proxy:
            p = {"path": proxy, "exists": os.path.isfile(proxy)}
            if p["exists"]:
                scan_progress("STATUS Checking proxies %d/%d" % (proxied.index(s) + 1, len(proxied)))
                p["size"] = os.path.getsize(proxy)
                try:
                    pr = tools.probe_file(proxy)
                    p["audio"] = _audio_streams(pr)
                    pv = next((st for st in pr["streams"] if st.get("codec_type") == "video"), None)
                    head = tools.probe_packets(proxy, pv["index"], "%+#12") if pv else []
                    p["intra"] = len(head) >= 2 and all(pk["key"] for pk in head)  # only all-intra proxies are trimmed
                except (TrimError, KeyError):
                    p["intra"] = False
            d["proxy"] = p
        items.append(d)
    other_items = []
    for kind, path, _applies, label in others:
        files = slideshow_files(path) if kind == "slideshow" else [path]
        other_items.append({"kind": kind, "path": path, "label": label,
                            "size": sum(os.path.getsize(f) for f in files if os.path.isfile(f))})
    return {"version": 1,
            "project": {"path": doc.path, "size": os.path.getsize(doc.path), "fps": doc.fps, "moved_from": doc.old_root},
            "out_dir": out_dir, "handles": args.handles, "search_seconds": args.search_seconds, "sources": items,
            "images": [{"path": p, "size": os.path.getsize(p)} for p, _els in images],
            "others": other_items}


PREDICT_DEFAULTS = dict(quick_check=False, handles=0.0, min_saving=10.0, long_gop="copy", audio="lossless",
                        proxies="trim", copy_unchanged=True, allow_drift=False)


def _pcm_rate(codec, st):
    """Bytes per second of a PCM stream (e.g. pcm_f32le = 4 bytes per sample per channel)."""
    m = re.match(r"pcm_[a-z]*(\d+)", codec or "")
    bits = int(m.group(1)) if m else 16
    return int(st.get("sample_rate") or 48000) * int(st.get("channels") or 2) * bits / 8.0


def _audio_rate_in(st):
    """Bytes per second of an audio stream as it is in the source."""
    if st.get("bit_rate") not in (None, "N/A"):
        return float(st["bit_rate"]) / 8
    if (st.get("codec_name") or "").startswith("pcm_"):
        return _pcm_rate(st["codec_name"], st)
    return 24000.0  # unknown compressed rate: assume 192 kbit/s


def _audio_rate_out(streams, mode):
    """Bytes per second of all audio streams after a cut with --audio mode (see audio_codec_for)."""
    total = 0.0
    for st in streams or []:
        codec = audio_codec_for(st, mode)
        total += _audio_rate_in(st) if codec == "copy" else _pcm_rate(codec, st)
    return total


def _audio_bytes_in(streams, dur):
    """Approximate bytes of all audio streams in a file, so the rest can be counted as video."""
    total = 0.0
    for st in streams or []:
        d = float(st["duration"]) if st.get("duration") not in (None, "N/A") else (dur or 0)
        total += _audio_rate_in(st) * d
    return total


def _choose_plan(s, o):
    """The cut trim_one would make for this source with these options, as {"S", "E"(, "frames")}, or None.
    Mirrors plan_source: drift is only used when --allow-drift is on and no exact cut trims the start."""
    if "n_frames" not in s:
        return None
    if s.get("skip") and not s["skip"].startswith("could not find a cut"):
        return None
    ex, dr = s.get("exact"), s.get("drift")
    if o["allow_drift"] and dr and (not ex or ex["S"] == 0):
        return dict(dr, drift=True)
    return ex


def predict(data, opts=None):
    """Predict the result of a run with opts (any of PREDICT_DEFAULTS) from a --report-json scan.
    Sizes are estimates: video is assumed to be spread evenly over its frames, and audio is sized from its bit rate
    (or its PCM rate after a lossless cut). Returns totals in bytes (before, archive, external = files the new project
    still uses outside the archive, after = archive + external, saved), data read and written, counts, and a
    per-file list. approx is True when the handles differ from the scan's, which only estimates how the cuts move."""
    o = dict(PREDICT_DEFAULTS)
    o.update(opts or {})
    r = dict(before=0.0, archive=0.0, external=0.0, read=0.0, written=0.0, trims=0, copies=0, missing=0,
             drift_frames=0, approx=False, files=[])
    psize = data["project"]["size"]
    r["before"] += psize
    r["archive"] += psize
    dh = float(o["handles"]) - float(data.get("handles", 0))
    r["approx"] = abs(dh) > 1e-9

    def copy(name, size, kind, note=""):
        r["before"] += size
        if o["copy_unchanged"]:
            r["archive"] += size
            r["read"] += size
            r["written"] += size
        else:
            r["external"] += size
        r["copies"] += 1
        r["files"].append({"name": name, "kind": kind, "action": "copy" if o["copy_unchanged"] else "keep",
                           "before": size, "after": size, "note": note})

    for s in data["sources"]:
        if s.get("in_media_dir"):
            continue
        if not s["exists"]:
            r["missing"] += 1
            r["files"].append({"name": s["name"], "kind": "missing", "action": "missing", "before": 0, "after": 0,
                               "note": "file not found"})
            continue
        size = s["size"]
        px = s.get("proxy") or {}
        prox = px.get("size", 0) if px.get("exists") else 0
        plan = _choose_plan(s, o)
        note = s.get("skip") or ""
        if not s.get("has_video"):
            note = "audio file"
        elif not s.get("used"):
            note = "only in the bin, not on the timeline"
        if plan and not s["intra"] and o["long_gop"] == "skip":
            plan, note = None, "H.264/HEVC file, --long-gop skip"
        if plan:
            n, sfps = s["n_frames"], s["sfps"]
            S, E = plan["S"], plan["E"]
            if r["approx"]:
                d = int(round(dh * sfps))
                S, E = max(0, S - d), min(n - 1, max(s["need"][1], E + d))
            K = E - S + 1
            kept = K if s["intra"] else min(n - S, K + int(math.ceil(LONG_GOP_TAIL_US / 1e6 * sfps)))
            saving = 1 - kept / n
            if saving <= 0:
                plan, note = None, WHOLE_FILE
            elif saving * 100 < o["min_saving"]:
                plan, note = None, "saving %.0f%% is below the %g%% minimum" % (saving * 100, o["min_saving"])
        if not plan:
            kind = "video" if s.get("has_video") else "audio"
            copy(s["name"], size, kind, note)
            if prox:
                if o["copy_unchanged"] and o["proxies"] == "trim":
                    r["before"] += prox
                    r["archive"] += prox
                    r["read"] += prox
                    r["written"] += prox
                elif o["copy_unchanged"]:
                    r["before"] += prox  # proxy link dropped, the proxy is not needed any more
                else:
                    r["before"] += prox
                    r["external"] += prox
            continue
        dur = n / sfps
        vbpf = max(0.0, size - _audio_bytes_in(s.get("audio"), s.get("duration") or dur)) / n
        after = vbpf * kept + _audio_rate_out(s.get("audio"), o["audio"]) * K / sfps
        rng = size * kept / n  # part of the original the cut reads
        q = 1.0
        if o["quick_check"]:
            lo, hi = max(s["need"][0], S), min(s["need"][1], E)
            q = min(1.0, sum(b - a + 1 for a, b in quick_windows(lo, hi, sfps)) / float(K))
        r["read"] += rng + q * (rng + after)
        r["written"] += after
        pafter = 0.0
        if prox and o["proxies"] == "trim" and px.get("intra"):
            pvb = max(0.0, prox - _audio_bytes_in(px.get("audio"), dur))
            pafter = pvb * K / n + _audio_rate_out(px.get("audio"), o["audio"]) * K / sfps
            prng = prox * K / n
            r["read"] += prox + prng + q * (prng + pafter)  # the whole proxy's packet list is read first
            r["written"] += pafter
        r["before"] += size + prox
        r["archive"] += after + pafter
        r["trims"] += 1
        notes = []
        if plan.get("drift"):
            r["drift_frames"] += plan["frames"]
            notes.append("%d frame(s) drift" % plan["frames"])
        elif s.get("start_limited"):
            notes.append("start not trimmed: no exact cut point")
        if prox and not pafter:
            notes.append("proxy dropped")
        r["files"].append({"name": s["name"], "kind": "video", "action": "trim", "before": size + prox,
                           "after": after + pafter, "note": ", ".join(notes)})
    for im in data["images"]:
        copy(os.path.basename(im["path"]), im["size"], "image")
    for ot in data["others"]:
        copy(ot["label"], ot["size"], ot["kind"])
    r["after"] = r["archive"] + r["external"]
    r["saved"] = r["before"] - r["after"]
    r["saved_pct"] = 100.0 * r["saved"] / r["before"] if r["before"] else 0.0
    return r


def make_parser(menu=False):
    """The command-line options. With menu=True it is the parser for --gui: the project is optional and no option
    has a default, so only the options actually given come back. Those preset the control dashboard for that session;
    everything else comes from the saved defaults."""
    ap = argparse.ArgumentParser(description="Trim a Kdenlive project's media to the parts the timeline uses and "
                                             "gather everything the project needs into one archive folder.")
    ap.add_argument("project", nargs="?" if menu else None)
    ap.add_argument("--report", action="store_true", help="analyse and print the plan, write nothing")
    ap.add_argument("--out-dir", help="output folder, laid out like a Kdenlive archive (videos/, sounds/, images/, "
                                      "proxy/ ...) with the new project inside (default: <project folder>/Archive)")
    # hidden: old name of --out-dir, so older command lines still work
    ap.add_argument("--media-dir", dest="out_dir", help=argparse.SUPPRESS)
    ap.add_argument("-o", "--output", help="new project file (default: the original file name, inside the output folder)")
    ap.add_argument("--handles", type=float, default=0.0, help="extra seconds to keep before/after the used range (default 0)")
    ap.add_argument("--min-saving", type=float, default=10.0,
                    help="copy instead of trimming files that would shrink by less than this %% (default 10)")
    ap.add_argument("--long-gop", choices=["copy", "skip"], default="copy",
                    help="H.264/HEVC etc: 'copy' cuts at the nearest earlier keyframe (default), 'skip' never trims them")
    ap.add_argument("--audio", choices=["lossless", "copy"], default="lossless",
                    help="'lossless' stores compressed audio (AAC etc.) as PCM for a sample-accurate cut (default); "
                         "'copy' stream-copies it instead (smaller, but the start can be off by up to one "
                         "audio packet, about 21 ms). PCM audio is always kept as PCM.")
    ap.add_argument("--proxies", choices=["trim", "drop"], default="trim",
                    help="'trim' trims or copies proxy files into proxy/ (default), 'drop' removes proxy links "
                         "so Kdenlive can rebuild them")
    ap.add_argument("--search-seconds", type=float, default=30.0,
                    help="how far before the used range to look for an exact cut point (default 30)")
    ap.add_argument("--no-copy-unchanged", dest="copy_unchanged", action="store_false",
                    help="only write the trimmed videos. By default every other file the project uses (untrimmed "
                         "videos, audio, images, slideshows, title images, wipes, effect files and proxies) is "
                         "copied into the output folder too, so the new project does not depend on anything outside it.")
    # hidden: the old opt-in flag, now the default
    ap.add_argument("--copy-unchanged", dest="copy_unchanged", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--quick-check", action="store_true",
                    help="check each cut's frame count plus its first and last 2 s and three 1 s samples, instead "
                         "of every frame (much less reading over a network share). The full check is the default.")
    ap.add_argument("--allow-drift", action="store_true",
                    help="for speed-changed or frame-rate-converted clips, allow a later cut that shifts up to 1%% of "
                         "the clip's frames by one source frame (default: keep every frame exact, trim less)")
    ap.add_argument("--plain", action="store_true", help="print a plain log instead of the progress dashboard")
    ap.add_argument("--complete", action="store_true",
                    help="finish an earlier archive of this project: bring in only the files its project still uses "
                         "from outside the archive folder (for example after a failed copy) and update that project "
                         "in place, after saving a backup of it. Give the original project as usual, or the archive's "
                         "own project file.")
    ap.add_argument("--report-json", metavar="FILE",
                    help="analyse only (like --report) and write the results as JSON to FILE, for "
                         "the control dashboard to predict savings")
    ap.add_argument("--gui", action="store_true",
                    help="open the control dashboard instead of running (also what happens with no arguments). A "
                         "project and any of its options given with it are set in the control dashboard for that "
                         "session, in place of your saved defaults")
    ap.add_argument("--ffmpeg", default="ffmpeg")
    ap.add_argument("--ffprobe", default="ffprobe")
    if menu:
        for action in ap._actions:  # noqa: SLF001 - argparse has no public way to drop every default
            action.default = argparse.SUPPRESS
            if action.dest == "project":
                action.help = "project to start with"
            elif action.dest in ("gui",) + tuple(dest for dest, _ in NOT_IN_MENU):
                action.help = argparse.SUPPRESS  # still parsed, so menu_main can say why it is refused
    else:
        ap.set_defaults(copy_unchanged=True)
    return ap


def main():
    """Parse the options and check everything that could stop the run before any work starts (ffmpeg found, output
    folder empty and writable, original project not overwritten). Then run with the dashboard and print the
    summary. The finally block removes partial files and restores the terminal however the run ends, including
    Ctrl-C."""
    global UI
    if not sys.argv[1:] or "--gui" in sys.argv[1:]:
        return menu_main([a for a in sys.argv[1:] if a != "--gui"])
    ap = make_parser()
    args = ap.parse_args()
    if args.report_json:
        # the scan records every alternative; the front end applies these choices itself (see predict)
        args.report, args.long_gop, args.min_saving, args.allow_drift = True, "copy", -1.0, False
        args.copy_unchanged = True

    for tool in (args.ffmpeg, args.ffprobe):
        if shutil.which(tool) is None:
            sys.exit("Cannot find %s. Install ffmpeg or pass --ffmpeg/--ffprobe." % tool)
    tools = Tools(args.ffmpeg, args.ffprobe)
    doc = Doc(args.project)
    out_dir = os.path.abspath(args.out_dir or os.path.join(os.path.dirname(doc.path), "Archive"))
    out_project = os.path.abspath(args.output or os.path.join(out_dir, os.path.basename(doc.path)))
    args.backup = None  # set by run() when --complete saves a copy of the archive's project before rewriting it
    if args.complete:
        # the archive to finish: <output folder>/<project name>, or the given project if it is itself one. An
        # archive made by this script always has its log next to it, so an original project is never edited.
        if os.path.isfile(out_project) and os.path.isfile(os.path.join(os.path.dirname(out_project),
                                                                       "kdenlive_trim.log")):
            target = out_project
        elif os.path.isfile(os.path.join(os.path.dirname(doc.path), "kdenlive_trim.log")):
            target = doc.path
        else:
            sys.exit("--complete finishes an archive made by this script, and there is none at\n  %s\nRun without "
                     "--complete to make one. Nothing has been changed." % out_project)
        if target != doc.path:
            doc = Doc(target)
        out_dir, out_project = os.path.dirname(target), target
    elif out_project == doc.path:
        sys.exit("Refusing to overwrite the original project file. Choose another --out-dir or -o.")
    # sources already inside the output folder are left alone (plan_source)
    args.media_dir_abs = out_dir
    if not args.report and not args.complete and os.path.isdir(out_dir):
        leftovers = [n for n in os.listdir(out_dir) if n not in ("kdenlive_trim.log", ".DS_Store")]
        if leftovers:
            sys.exit("The output folder already has files from an earlier run:\n  %s\nDelete or move it first (or "
                     "choose another --out-dir). Nothing has been changed." % out_dir)
    if not args.report:
        for folder, what in ((out_dir, "--out-dir"), (os.path.dirname(out_project), "-o")):
            err = write_problem(folder)
            if err:
                sys.exit("Cannot write to %s\n  %s\nCheck you have write access there (on a network share: the share's "
                         "permissions for your user, and that it is not mounted read-only), or choose another "
                         "location with %s. Nothing has been changed." % (folder, err, what))

    # live dashboard only in a real terminal; a plain log when output goes to a file, or with --plain
    live = (not args.report and not args.plain and sys.stdout.isatty()
            and os.environ.get("TERM", "dumb") != "dumb")
    log_path = os.path.join(out_dir, "kdenlive_trim.log")
    if not args.report:
        os.makedirs(out_dir, exist_ok=True)
        keep_awake()
    UI = Dashboard(os.path.basename(doc.path), out_dir, None if args.report else log_path, live)
    summary = []
    interrupted = False
    if args.complete:
        log("Completing the archive %s" % out_dir)
    try:
        summary = run(args, doc, tools, out_dir, out_project)
        if args.backup:
            summary.append("The archive's project as it was before this run: %s" % args.backup)
        if not args.report:
            summary.append("Full log: %s" % log_path)
    except KeyboardInterrupt:
        interrupted = True
        summary = ["Interrupted. The original project and media are untouched, partial files were removed "
                   "and no new project was written."]
    finally:
        for f in list(CLEANUP):
            if os.path.exists(f):
                try:
                    os.remove(f)
                except OSError:
                    pass
        was_live = UI.live
        for line in summary:
            UI.log(line)  # to the log file (and the screen in plain mode)
        if UI.log_error:
            note = ("\nThe log file could not be written: %s. The log is incomplete, so keep this summary; check the "
                    "share or disk." % UI.log_error)
            summary.append(note)
            if not was_live:
                print(note, flush=True)
        UI.close()
        UI = None
        if was_live:
            print("\n".join(summary))
    if interrupted:
        sys.exit(130)  # the usual exit code after Ctrl-C, so a front end can tell


def run(args, doc, tools, out_dir, out_project):
    """The whole job: analyse every source and print the plan, then trim, copy everything else, save the new
    project and build the summary (self-contained or not, and which original folders are no longer needed). Returns
    the summary lines; main prints them after the dashboard closes."""
    archive = Archive(out_dir)
    groups = {}
    for m in doc.media.values():
        # one Source per original file, however many clips and speed versions use it
        groups.setdefault(m.key, []).append(m)
    UI.set_phase("Analysing", len(groups))
    sources = []
    for i, (key, medias) in enumerate(sorted(groups.items())):
        UI.tick(os.path.basename(key))
        if args.report_json:
            scan_progress("PROGRESS %d %d %s" % (i, len(groups), os.path.basename(key)))
        src = Source(key, medias, [u for u in doc.uses if u.media in medias])
        try:
            plan_source(src, tools, args, doc)
        except TrimError as e:
            src.skip = str(e)
        sources.append(src)
    if args.complete:
        inside_n = sum(1 for s in sources if s.in_media_dir)
        print_report(doc, [s for s in sources if not s.in_media_dir])
        log("\n%d file(s) are already in the archive and are left as they are." % inside_n)
    else:
        print_report(doc, sources)

    todo = [s for s in sources if s.plan and not s.skip]
    if args.copy_unchanged:
        av, images = copy_plan(doc, sources, tools, out_dir, todo)
        # clips handled above are excluded so other_assets does not copy them twice
        handled = {m.id for m in doc.media.values()} | {el.get("id") for els in image_groups(doc).values() for el in els}
        others = other_assets(doc, out_dir, handled)
    else:
        av, images, others = [], [], []
    rel = lambda p: os.path.relpath(p, out_dir) if inside(p, out_dir) else p
    kinds = {}
    for job in others:
        kinds[job[0]] = kinds.get(job[0], 0) + 1
    log("\nOutput folder: %s" % out_dir)
    log("  project      %s" % rel(out_project))
    log("  videos/      %d trimmed, %d copied unchanged" % (len(todo), sum(1 for _, k in av if k == "video")))
    if args.copy_unchanged:
        log("  sounds/      %d audio file(s)" % sum(1 for _, k in av if k == "audio"))
        log("  images/      %d image(s)%s" % (len(images) + kinds.get("image", 0),
                                              " (%d used inside titles)" % kinds["image"] if kinds.get("image") else ""))
        for k in ("slideshow", "text", "luma", "other"):
            if kinds.get(k):
                log("  %-12s %d" % (SUBDIRS[k] + "/", kinds[k]))
    log("  proxy/       %s" % ("trimmed and copied proxies" if args.proxies == "trim" else "none (--proxies drop)"))
    log("Checking:      %s" % ("quick (frame count, first and last 2 s, three 1 s samples per cut)" if args.quick_check
                               else "full (every used frame of every cut)"))
    if args.report_json:
        data = scan_data(doc, sources, tools, args, out_dir, images, others)
        with open(args.report_json, "w", encoding="utf-8") as f:
            json.dump(data, f)
    if args.report:
        return []
    if not todo and not av and not images and not others:
        if args.complete and not any(s.skip and s.skip.startswith("file not found") for s in sources):
            return ["Nothing to add: the archive already holds every file its project uses."]
        # say why, so the user does not have to dig through the log
        missing = [s for s in sources if s.skip and s.skip.startswith("file not found")]
        if missing:
            return ["Nothing to trim or copy: %d file(s) used by the project were not found, e.g.\n  %s"
                    % (len(missing), missing[0].key)]
        return ["Nothing to trim or copy."]

    # estimated work, in bytes read/written, for the progress bar and time left
    weight = {}
    for s in todo:
        weight[id(s)] = (1 + check_share(s, args.quick_check)) * s.size * s.plan["K"] / max(1, s.n_frames or s.plan["K"])
    for s, _ in av:
        weight[id(s)] = float(os.path.getsize(s.key))
    total = sum(weight.values()) + sum(os.path.getsize(p) for p, _ in images)
    total += sum(sum(os.path.getsize(f) for f in slideshow_files(j[1])) if j[0] == "slideshow" else os.path.getsize(j[1])
                 for j in others)
    UI.counts.update(trim_total=len(todo), copy_total=len(av) + len(images) + len(others))
    UI.set_phase("Processing")
    UI.start_work(total)

    done, copied, copied_images, copied_other = [], [], [], []
    if todo:
        log("\nTrimming %d file(s) into %s" % (len(todo), archive.dir("video")))
    for src in todo:
        S, E = src.plan["S"], src.plan["E"]
        info = "keeping %s to %s of %s" % (fmt_secs(S / src.sfps), fmt_secs((E + 1) / src.sfps),
                                          fmt_secs((src.n_frames or E + 1) / src.sfps))
        UI.begin("Trimming", src.name, src.size, info, (S, E, src.n_frames or E + 1), weight[id(src)])
        err = trim_one(src, args, doc, tools, archive)
        if err:
            src.skip = err
            UI.end("FAIL", "%s  %s" % (src.name, err.split(":")[-1].strip()[:80]))
            continue
        done.append(src)
        UI.counts["trim_done"] += 1
        UI.counts["saved"] += src.size - src.new_size
        UI.end("OK", "%s  %s -> %s%s" % (src.name, fmt_size(src.size), fmt_size(src.new_size),
                                         ", proxy trimmed" if src.proxy_ok else ""))

    if args.copy_unchanged:
        for s in todo:  # a failed trim falls back to a plain copy
            if s not in done and os.path.isfile(s.key):
                av.append((s, "video"))
                # the trim's work is already counted as done; the copy is extra work the estimate did not include
                weight[id(s)] = float(os.path.getsize(s.key))
                UI.work_total += weight[id(s)]
                UI.counts["copy_total"] += 1
    if av or images or others:
        log("\nCopying %d unchanged file(s) into %s" % (len(av) + len(images) + len(others), out_dir))
    for src, kind in av:
        UI.begin("Copying", "%s/%s" % (SUBDIRS[kind], src.name), os.path.getsize(src.key), weight=weight[id(src)])
        UI.set_step("Copying")
        failed_trim = src.skip and src.skip.startswith("cut failed")
        try:
            src.notes = []
            copy_source(doc, src, archive, kind, args.proxies)
            if failed_trim:
                src.notes.insert(0, "%s; copied unchanged instead" % src.skip)
            copied.append(src)
            UI.counts["copy_done"] += 1
            UI.end("COPY", "%s/%s" % (SUBDIRS[kind], src.name))
        except (OSError, TrimError) as e:
            src.notes.append("copy failed, project still uses the original: %s" % e)
            UI.end("FAIL", "%s  copy failed: %s" % (src.name, e))
    for path, els in images:
        UI.begin("Copying", "images/" + os.path.basename(path), os.path.getsize(path), weight=os.path.getsize(path))
        UI.set_step("Copying")
        try:
            copy_image(doc, path, els, archive, args.proxies)
            copied_images.append(path)
            UI.counts["copy_done"] += 1
            UI.end("COPY", "images/" + os.path.basename(path))
        except (OSError, TrimError) as e:
            UI.end("FAIL", "%s  copy failed: %s" % (os.path.basename(path), e))
    for kind, path, applies, label in others:
        files = slideshow_files(path) if kind == "slideshow" else [path]
        size = sum(os.path.getsize(f) for f in files)
        UI.begin("Copying", "%s/%s" % (SUBDIRS[kind], label), size, weight=size)
        UI.set_step("Copying")
        try:
            if kind == "slideshow":
                sub, n = label, 2
                while os.path.exists(os.path.join(archive.dir("slideshow"), sub)):
                    sub, n = "%s_%d" % (label, n), n + 1
                for f in files:
                    archive.copy(f, "slideshow", sub)
                new = os.path.join(archive.dir("slideshow"), sub)
            else:
                new = archive.copy(path, kind)
            for apply in applies:
                apply(new)
            copied_other.append((kind, path, files))
            UI.counts["copy_done"] += 1
            UI.end("COPY", "%s/%s%s" % (SUBDIRS[kind], label, " (%d files)" % len(files) if len(files) > 1 else ""))
        except (OSError, TrimError) as e:
            UI.end("FAIL", "%s  copy failed: %s" % (label, e))

    if not done and not copied and not copied_images and not copied_other:
        return ["Nothing was trimmed or copied, so no project was written."]
    UI.set_phase("Writing project")
    refs = referenced_files(doc)  # absolute paths, before save() makes them relative
    if args.complete:  # keep the archive's project as it was, in case this run's result is not wanted
        args.backup = unique_path(out_project + ".bak", set())
        shutil.copy2(out_project, args.backup)
    doc.save(out_project)
    ET.parse(out_project)  # make sure the written file is valid XML

    out = ["", "Wrote %s" % out_project]
    if done:
        before, after = sum(s.size for s in done), sum(s.new_size for s in done)
        out.append("Trimmed %d file(s): %.2f GB -> %.2f GB (saved %.2f GB)"
                   % (len(done), before / 1e9, after / 1e9, (before - after) / 1e9))
    n_copied = len(copied) + len(copied_images) + len(copied_other)
    if n_copied:
        gb = (sum(os.path.getsize(s.copied_to) for s in copied) + sum(os.path.getsize(p) for p in copied_images)
              + sum(os.path.getsize(f) for _, _, files in copied_other for f in files)) / 1e9
        out.append("Copied %d unchanged file(s): %.2f GB" % (n_copied, gb))
    # whole-run total: every original file the archive now stands in for (media, proxies, images, other assets,
    # the project file) against everything in the archive folder, i.e. the space freed by keeping only the archive
    originals = {s.key for s in done + copied} | set(copied_images) | {doc.path}
    originals |= {f for _, _, files in copied_other for f in files}
    originals |= {p for p, new in archive.proxy_map.items() if new}
    originals |= {m.proxy for s in done for m in s.medias if m.proxy and os.path.isfile(m.proxy)}
    before = sum(os.path.getsize(f) for f in originals if os.path.isfile(f))
    after = sum(os.path.getsize(os.path.join(d, f)) for d, _, files in os.walk(out_dir) for f in files
                if f != "kdenlive_trim.log")
    if before and not args.complete:  # when completing, the archive was mostly made by the earlier run
        out.append("Total: %.2f GB of original files -> %.2f GB archive, saved %.2f GB (%.0f%%)"
                   % (before / 1e9, after / 1e9, (before - after) / 1e9, 100.0 * (before - after) / before))
    for s in sources:
        for n in s.notes:
            out.append("  note [%s]: %s" % (s.name, n))
    # files left out of the archive for a reason worth reporting (small savings and audio-only are expected)
    problems = [s for s in sources if s.skip and s.uses and not s.in_media_dir and s not in copied and s not in done
                and not s.skip.startswith(("only ", "no video stream"))]
    for s in problems:
        out.append("  not included [%s]: %s" % (s.name, s.skip))

    outside = sorted(r for r in refs if not inside(r, out_dir))
    if not outside:
        out.append("\nSelf-contained: every file the new project uses is inside %s" % out_dir)
    else:
        out.append("\nNOT self-contained: the new project still uses %d file(s) outside %s:" % (len(outside), out_dir))
        out += ["  %s" % r for r in outside[:15]]
        if len(outside) > 15:
            out.append("  ... and %d more" % (len(outside) - 15))
    # folders that held files now in the archive: shows which originals the new project no longer needs
    old_files = [s.key for s in done + copied] + copied_images + [f for _, _, files in copied_other for f in files]
    old_files += [p for p, new in archive.proxy_map.items() if new]
    old_files += [m.proxy for s in done for m in s.medias[:1] if m.proxy and os.path.isfile(m.proxy)]
    folders = sorted({os.path.dirname(f) for f in old_files})
    if folders:
        out.append("\nOriginal folders, checked against the new project:")
        for f in folders:
            still = sorted(r for r in refs if inside(r, f))
            # the original project's folder: when completing, the one the archive sits in
            proj_dir = os.path.dirname(out_dir) if args.complete else os.path.dirname(doc.path)
            shared = "" if inside(f, proj_dir) else "  (outside the project folder, other projects may use it)"
            out.append("  STILL USED  %s  (%d file(s), e.g. %s)" % (f, len(still), os.path.basename(still[0]))
                       if still else "  NOT USED    %s%s" % (f, shared))
    out.append("\nOpen the new project in Kdenlive and check it before deleting anything.")
    return out


# =========================================================================== control dashboard
# The control dashboard, opened with no arguments or with --gui: browse for a project and an output folder, set every
# option above (with what each one does and its pros and cons), save defaults (kdenlive-trim.json),
# scan the project and predict the saving with predict(), then run the trim. Scan and Run start this same file as a
# separate process (--report-json for a scan), so the run gets the progress dashboard and the usual Ctrl-C handling.

# the control dashboard's settings live in a file next to this one, so each copy of the program keeps its own
CONFIG_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), "kdenlive-trim.json")
# where the separate front end (kdenlive_trim_tui.py) kept them; read once if there is no settings file here yet
OLD_CONFIG_PATH = os.path.join(os.path.expanduser("~"), ".config", "kdenlive_trim", "tui.json")
MIN_W, MIN_H = 72, 22
BOX_KINDS = ("info", "done", "question", "warn", "error")

# --------------------------------------------------------------------------- options
# Each command-line option: how it is shown, its built-in default (the script's own), how it maps to the
# command line, and what it does with its pros (+) and cons (-) for each value.

OPTIONS = [
    {"key": "quick_check", "label": "Checking", "type": "choice", "default": False,
     "choices": [(False, "full (every frame)"), (True, "quick (samples)")],
     "about": {
         False: ["Every used frame of each cut is compared with the original.",
                 "+ Proves every frame was copied exactly.",
                 "- Reads each kept part twice more (original and cut), the slowest step over a network share."],
         True: ["Checks the frame count, the first and last 2 s and three 1 s samples of each cut.",
                "+ Much less reading on cuts longer than about 10 s.",
                "- Frames between the samples are not compared. Short cuts get checked in full anyway."]}},
    {"key": "handles", "label": "Handles", "type": "number", "default": 0.0, "unit": "s", "min": 0.0, "max": 600.0,
     "step": 0.5, "whatif": [0.0, 0.5, 1.0, 2.0, 5.0],
     "about": ["Extra footage kept before and after each used part of a clip.",
               "+ Lets you extend or slip edits later in the archived project.",
               "- Bigger archive. 0 keeps exactly what the timeline uses.",
               "Changing it after a scan estimates the effect; press s to rescan for exact figures."]},
    {"key": "min_saving", "label": "Minimum saving", "type": "number", "default": 10.0, "unit": "%", "min": 0.0,
     "max": 100.0, "step": 5.0, "whatif": [0.0, 5.0, 10.0, 25.0, 50.0],
     "about": ["Videos that would shrink by less than this are copied whole instead of trimmed.",
               "+ Higher: fewer cuts and a faster run; small savings are skipped.",
               "- Lower: more files trimmed for a little extra space, each needing a cut and a check."]},
    {"key": "long_gop", "label": "H.264/HEVC files", "type": "choice", "default": "copy",
     "choices": [("copy", "trim from keyframe"), ("skip", "copy whole")],
     "about": {
         "copy": ["Phone, drone and action-camera files are trimmed, starting at the keyframe before the used part.",
                  "+ Usually where most of the saving is.",
                  "- Keeps a little extra footage before each cut and 0.5 s after it."],
         "skip": ["H.264/HEVC files are copied whole.",
                  "+ Those files are not re-wrapped at all, so the run is faster.",
                  "- No saving on them."]}},
    {"key": "audio", "label": "Audio", "type": "choice", "default": "lossless",
     "choices": [("lossless", "lossless (PCM)"), ("copy", "keep original")],
     "about": {
         "lossless": ["Compressed audio (AAC etc.) in trimmed files is stored as PCM, so the cut is sample accurate.",
                      "+ The audio is exactly what Kdenlive decoded before.",
                      "- PCM is bigger (stereo is about 23 MB a minute) and trimmed .mp4 files become .mov."],
         "copy": ["Compressed audio is kept as it is.",
                  "+ Smaller trimmed files, and .mp4 stays .mp4.",
                  "- The audio can start up to about 21 ms off (one AAC packet)."]}},
    {"key": "proxies", "label": "Proxies", "type": "choice", "default": "trim",
     "choices": [("trim", "trim and keep"), ("drop", "drop (rebuild later)")],
     "about": {
         "trim": ["Proxy clips are trimmed or copied into the archive's proxy folder.",
                  "+ Proxies work straight away when you open the archive.",
                  "- Takes space and time. Proxies that are not all-intra get dropped anyway."],
         "drop": ["Proxy links are removed from the new project.",
                  "+ Smaller archive and a faster run.",
                  "- Generate the proxies again in Kdenlive before editing the archive."]}},
    {"key": "copy_unchanged", "label": "Copy other files", "type": "choice", "default": True,
     "choices": [(True, "yes (self-contained)"), (False, "no (trimmed only)")],
     "about": {
         True: ["Everything else the project uses (untrimmed videos, audio, images, titles, effects) is copied too.",
                "+ The archive is self-contained: the original folders can be deleted afterwards.",
                "- The run reads and writes all of those files."],
         False: ["Only trimmed videos are written; the new project still uses everything else where it is now.",
                 "+ Much faster when there is a lot to copy.",
                 "- Not self-contained: do not delete the original folders."]}},
    {"key": "allow_drift", "label": "Allow drift", "type": "choice", "default": False,
     "choices": [(False, "no (all exact)"), (True, "yes (up to 1%)")],
     "about": {
         False: ["Every frame on the timeline stays exactly the same.",
                 "+ Nothing changes anywhere in the edit.",
                 "- Some speed-changed clips cannot have their start trimmed."],
         True: ["Speed-changed clips may be cut where up to 1% of their frames show the neighbouring source frame.",
                "+ Trims more of those clips.",
                "- Those frames are one source frame off (rarely visible)."]}},
    {"key": "search_seconds", "label": "Cut search window", "type": "number", "default": 30.0, "unit": "s",
     "min": 1.0, "max": 3600.0, "step": 10.0,
     "about": ["How far before each used part to look for a cut point that keeps speed-changed clips exact.",
               "+ Larger: more chance of trimming the start of those clips.",
               "- Slightly longer scan. Only matters for speed-changed or frame-rate-converted clips."]},
    {"key": "ffmpeg", "label": "ffmpeg program", "type": "text", "default": "ffmpeg",
     "about": ["The ffmpeg program to use. Leave as ffmpeg to use the one on your PATH."]},
    {"key": "ffprobe", "label": "ffprobe program", "type": "text", "default": "ffprobe",
     "about": ["The ffprobe program to use. Leave as ffprobe to use the one on your PATH."]},
]
OPT_BY_KEY = {o["key"]: o for o in OPTIONS}
PREDICTED = ("quick_check", "handles", "min_saving", "long_gop", "audio", "proxies", "copy_unchanged", "allow_drift")

ABOUT_PROJECT = ["The Kdenlive project to archive.",
                 "Enter opens the browser, which lists folders and .kdenlive files with their dates. In it, "
                 "~ goes home, v goes to /Volumes (network shares) and g types a path."]
ABOUT_OUTPUT = ["Where the archive is written. Default: an Archive folder next to the project.",
                "It must be empty or not exist yet. Enter browses, Backspace goes back to the default."]

# The Actions area of the main screen: shortcut key, button label, method, and what it does (shown in About).
# Every action can be chosen from the Actions list or with its key.
ACTIONS = [
    ("s", "Scan", "run_scan",
     ["Reads a little of each video (around the cut points) and writes nothing, then predicts the space saved with "
      "your options and what changing each one would do.",
      "Over a network share this can take a few minutes."]),
    ("w", "What-if", "whatif_screen",
     ["A table of every other value of each option, with its predicted saving and data to move. Enter on a row "
      "applies that change.", "Needs a scan."]),
    ("f", "Files", "files_screen",
     ["What will happen to each file (trimmed, copied or left where it is), with its size before and after.",
      "Needs a scan."]),
    ("r", "Run", "run_job",
     ["Runs the trim with these options and shows the progress dashboard, then comes back here.",
      "The original project and media are never changed. Ctrl-C stops it cleanly.",
      "If the output folder already has an archive of this project, Run offers to complete it instead."]),
    ("c", "Command", "command_screen",
     ["Shows the command line for these choices, to keep or run yourself. It can be copied to the clipboard."]),
    ("d", "Save defaults", "save_defaults",
     ["Saves the current options as your defaults. They are loaded every time this program starts."]),
    ("b", "Reset options", "reset_defaults",
     ["Puts every option back to the script's built-in defaults. Your saved defaults stay as they are until you "
      "save again."]),
    ("?", "Help", "help_screen", ["The keys, the browser, and how the prediction works."]),
    ("q", "Quit", "quit", ["Leaves the program. The last project is remembered for next time."]),
]
ACTION_BY_KEY = {a[0]: a for a in ACTIONS}


def builtin_defaults():
    return {o["key"]: o["default"] for o in OPTIONS}


def fmt_num(v):
    """1.0 -> '1', 1.5 -> '1.5' (for display and the command line)."""
    return ("%g" % v) if v != int(v) else str(int(v))


def fmt_value(opt, v):
    if opt["type"] == "choice":
        return next((label for val, label in opt["choices"] if val == v), str(v))
    if opt["type"] == "number":
        return "%s %s" % (fmt_num(v), opt["unit"])
    return str(v)


def fmt_size_ui(n):
    n = float(n)
    if abs(n) >= 1e9:
        return "%.1f GB" % (n / 1e9)
    if abs(n) >= 1e8:
        return "%.0f MB" % (n / 1e6)
    if abs(n) >= 1e6:
        return "%.1f MB" % (n / 1e6)
    return "%.0f KB" % (n / 1e3)


def fmt_delta(n):
    if abs(n) < 1000:
        return "same"
    return ("+" if n > 0 else "-") + fmt_size_ui(abs(n))


def short_path(p, width):
    """Path cut from the left to fit width, so the file name stays visible."""
    return p if len(p) <= width else "\u2026" + p[-(width - 1):]


def fmt_ago(t):
    s = int(time.time() - t)
    if s < 60:
        return "just now"
    if s < 3600:
        return "%d min ago" % (s // 60)
    return "%d h ago" % (s // 3600)


# --------------------------------------------------------------------------- config and script

def load_config():
    """The saved settings as (settings, problem, source). source is the file they came from: kdenlive-trim.json next
    to this program, or the old front end's file the first time, when there is none here yet (they are saved next to
    this program from then on), or None when there are no saved settings. problem says why a file could not be
    read."""
    source = (CONFIG_PATH if os.path.exists(CONFIG_PATH)
              else OLD_CONFIG_PATH if os.path.isfile(OLD_CONFIG_PATH) else None)
    if source is None:
        return {}, None, None
    try:
        with open(source, encoding="utf-8") as f:
            cfg = json.load(f)
        if not isinstance(cfg, dict):
            return {}, "not a settings file", source
        return cfg, None, source
    except OSError as e:
        return {}, e.strerror or str(e), source
    except ValueError as e:
        return {}, "damaged: %s" % e, source


def config_label(path=CONFIG_PATH):
    """A settings file's path for messages: just the file name for the one next to this program, otherwise the
    full path with the home folder shown as ~."""
    if path == CONFIG_PATH:
        return os.path.basename(CONFIG_PATH)
    home = os.path.expanduser("~")
    return "~" + path[len(home):] if path.startswith(home + os.sep) else path


def config_note(cfg, problem, source, opts, presets, out_dir):
    """The bottom-bar note at start-up: where the settings came from, how many options differ from the built-in
    defaults (so the count matches the options marked *), and anything --gui set for this session."""
    path = config_label(source or CONFIG_PATH)
    if problem:
        note = "Could not read %s (%s): using the built-in defaults." % (path, problem)
    elif source is None:
        note = "No saved settings yet: Save defaults (d) creates %s." % path
    else:
        saved = {k: v for k, v in (cfg.get("defaults") or {}).items() if k in OPT_BY_KEY}
        built_in = builtin_defaults()
        differ = sum(1 for k, v in opts.items() if v != built_in[k])
        if not saved:
            note = "Settings loaded from %s. No defaults saved there yet, so the built-in defaults apply." % path
        elif not differ:
            note = "Settings loaded from %s: every option is at its built-in default." % path
        else:
            note = "Settings loaded from %s: %d option%s differ%s from the built-in defaults (marked *)." % (
                path, differ, "s" if differ != 1 else "", "" if differ != 1 else "s")
        if source != CONFIG_PATH:
            note += " From now on they are saved in %s." % config_label()
    extra = []
    if presets:
        extra.append("%d option%s" % (len(presets), "s" if len(presets) != 1 else ""))
    if out_dir:
        extra.append("the output folder")
    if extra:
        note += " --gui set %s for this session." % " and ".join(extra)
    return note


def save_config(cfg):
    try:
        os.makedirs(os.path.dirname(CONFIG_PATH), exist_ok=True)
        tmp = CONFIG_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cfg, f, indent=2)
        os.replace(tmp, CONFIG_PATH)
        return None
    except OSError as e:
        return str(e)


# --------------------------------------------------------------------------- the program

class App:
    def __init__(self, stdscr, args):
        self.scr = stdscr
        self.cfg, self.cfg_problem, self.cfg_source = load_config()
        self.script, self.core, self.core_err = args.script_path, args.core, None  # checked before start-up
        self.opts = builtin_defaults()
        self.opts.update({k: v for k, v in (self.cfg.get("defaults") or {}).items() if k in OPT_BY_KEY})
        self.opts.update(args.presets)  # options given with --gui, for this session only
        project = args.project or self.cfg.get("last_project")
        self.project = os.path.abspath(project) if project and os.path.isfile(project) else None
        # None = default (Archive next to the project); --out-dir given with --gui sets it for this session
        self.out_dir = os.path.abspath(args.out_dir) if args.out_dir else None
        self.scan = None     # {"data", "time", "project", "search_seconds", "out_dir"}
        self.cursor = 0
        # short note in the bottom bar until the next key; at start-up, where the settings came from
        self.status = config_note(self.cfg, self.cfg_problem, self.cfg_source, self.opts, args.presets, args.out_dir)
        self.stacked = True     # layout of the last draw: Actions under Options (True) or beside them
        self.init_colors()

    # ---- drawing helpers
    def init_colors(self):
        self.c = {"title": curses.A_REVERSE, "dim": curses.A_DIM, "ok": curses.A_BOLD, "warn": curses.A_BOLD,
                  "bad": curses.A_BOLD, "acc": curses.A_BOLD, "sel": curses.A_REVERSE, "b": curses.A_BOLD}
        if curses.has_colors():
            try:
                curses.start_color()
                curses.use_default_colors()
                for i, fg in enumerate((curses.COLOR_GREEN, curses.COLOR_YELLOW, curses.COLOR_RED,
                                        curses.COLOR_CYAN), 1):
                    curses.init_pair(i, fg, -1)
                curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)
                self.c.update(ok=curses.color_pair(1), warn=curses.color_pair(2), bad=curses.color_pair(3),
                              acc=curses.color_pair(4), title=curses.color_pair(5) | curses.A_BOLD)
            except curses.error:
                pass

    def size(self):
        h, w = self.scr.getmaxyx()
        return h, w

    def put(self, y, x, text, attr=0, width=None):
        """Draw text clipped to the screen (curses raises if text touches the bottom-right corner)."""
        h, w = self.size()
        if y < 0 or y >= h or x >= w:
            return
        room = (w - x - 1) if width is None else min(width, w - x - 1)
        if room <= 0:
            return
        text = str(text)
        if len(text) > room:
            text = text[:max(0, room - 1)] + "…"
        try:
            self.scr.addstr(y, x, text, attr)
        except curses.error:
            pass

    def bar(self, y, text, attr=None):
        h, w = self.size()
        self.put(y, 0, (" " + text).ljust(w - 1), self.c["title"] if attr is None else attr)

    def footer(self, items, compact=None):
        """Key hints from the left, as many as fit, always ending with the last two (help, quit). If the full list
        does not fit and a compact list is given, that is used instead."""
        h, w = self.size()
        if compact and len("  ".join(items)) + 2 >= w:
            items = compact
        tail = [it for it in items[-2:] if it]
        out = []
        for it in items[:-2]:
            if len("  ".join(out + [it] + tail)) + 2 < w:
                out.append(it)
            else:
                break
        out += tail
        self.put(h - 1, 0, (" " + "  ".join(out)).ljust(w - 1), self.c["title"])

    def flash(self, text):
        """A short note in the bottom bar until the next key, for small changes you can already see on screen.
        Questions, errors and results use centred boxes instead (popup)."""
        self.status = text

    def box_attr(self, kind):
        return {"info": self.c["acc"], "done": self.c["ok"], "question": self.c["warn"], "warn": self.c["warn"],
                "error": self.c["bad"]}.get(kind, self.c["acc"])

    def draw_box(self, title, paragraphs, kind="info", buttons=(), sel=0, extra_rows=0, width=None):
        """Draw a bordered box in the middle of the screen. paragraphs: strings (or (text, attr) pairs); lines
        starting with + or - are coloured like the About pane. Returns (window, first free row, inner width)."""
        h, w = self.size()
        texts = [p if isinstance(p, tuple) else (p, None) for p in paragraphs]
        longest = max([len(t) for t, _ in texts] + [len(title) + 6, 40])
        bw = max(24, min(w - 4, width or min(78, longest + 6)))
        inner = bw - 4
        lines = []
        for t, a in texts:
            if a is None:
                a = self.c["ok"] if t.startswith("+ ") else (self.c["warn"] if t.startswith("- ") else 0)
            lines += [(line, a) for line in (self.wrap(t, inner) if t else [""])]
        lines = lines[:max(1, h - 6 - extra_rows - (1 if buttons else 0))]
        bh = len(lines) + 4 + extra_rows + (1 if buttons else 0)
        by, bx = max(0, (h - bh) // 2), max(0, (w - bw) // 2)
        win = curses.newwin(bh, bw, by, bx)
        win.keypad(True)
        win.erase()
        battr = self.box_attr(kind) | curses.A_BOLD

        def put(y, x, text, attr=0, clip=True):
            try:
                win.addstr(y, x, text[:bw - x - 1] if clip else text, attr)
            except curses.error:  # writing the bottom-right corner raises, but the character is drawn
                pass
        # Unicode line characters rather than the terminal's line-drawing mode, which some terminals garble
        put(0, 0, "\u250c" + "\u2500" * (bw - 2) + "\u2510", battr, False)
        for yy in range(1, bh - 1):
            put(yy, 0, "\u2502", battr, False)
            put(yy, bw - 1, "\u2502", battr, False)
        put(bh - 1, 0, "\u2514" + "\u2500" * (bw - 2) + "\u2518", battr, False)
        put(0, 2, " %s " % title, battr)
        for i, (line, a) in enumerate(lines):
            put(2 + i, 2, line, a)
        if buttons:
            labels = ["[ %s ]" % b for b in buttons]
            total = sum(len(t) for t in labels) + 3 * (len(labels) - 1)
            x = max(2, (bw - total) // 2)
            for i, t in enumerate(labels):
                put(bh - 2, x, t, (curses.A_REVERSE | curses.A_BOLD) if i == sel else curses.A_BOLD)
                x += len(t) + 3
        return win, 2 + len(lines) + 1, inner

    def popup(self, title, paragraphs, kind="info", buttons=("OK",), default=0):
        """Show a centred box and wait. A one-button box closes on any key and returns 0. With several buttons:
        arrows or Tab choose, Enter confirms, y picks the first button and n the last (as does each button's first
        letter), Esc returns None."""
        if isinstance(paragraphs, str):
            paragraphs = [paragraphs]
        sel = default
        try:
            while True:
                win, _, _ = self.draw_box(title, paragraphs, kind, buttons, sel)
                win.refresh()
                k = self.getkey(win)
                if k == "KEY_RESIZE":
                    self.scr.refresh()
                    continue
                if len(buttons) == 1:
                    return 0
                if k in ("KEY_LEFT", "KEY_UP", "KEY_BTAB"):
                    sel = (sel - 1) % len(buttons)
                elif k in ("KEY_RIGHT", "KEY_DOWN", "\t"):
                    sel = (sel + 1) % len(buttons)
                elif k in ("\n", "\r", "KEY_ENTER", " "):
                    return sel
                elif k in ("\x1b", "\x03"):
                    return None
                elif k in ("y", "Y"):
                    return 0
                elif k in ("n", "N"):
                    return len(buttons) - 1
                else:
                    hit = [i for i, b in enumerate(buttons) if len(k) == 1 and b[:1].lower() == k.lower()]
                    if hit:
                        return hit[0]
        finally:
            self.scr.touchwin()  # repaint what the box covered
            self.scr.refresh()

    def notice(self, title, paragraphs, kind="done"):
        """A result or confirmation: centred box, any key closes it."""
        self.popup(title, paragraphs, kind)

    def error(self, paragraphs, title="Problem"):
        self.popup(title, paragraphs, "error")

    def confirm(self, question, title="Please confirm", yes="Yes", no="No", default=0, kind="question"):
        """Yes/No question in a centred box. True only if the first button is chosen."""
        return self.popup(title, question, kind, (yes, no), default) == 0

    def ask_text(self, title, label, initial="", hint=None):
        """Centred box with a one-line text field. Returns the text, or None on Esc."""
        buf, pos = list(initial), len(initial)
        paragraphs = [label] + ([(hint, self.c["dim"])] if hint else [])
        try:
            curses.curs_set(1)
        except curses.error:
            pass
        try:
            while True:
                win, row, inner = self.draw_box(title, paragraphs, "question", extra_rows=2, width=78)
                start = max(0, pos - inner + 1)
                try:
                    win.addstr(row, 2, "".join(buf[start:start + inner]).ljust(inner), curses.A_REVERSE)
                    win.addstr(row + 1, 2, "Enter OK    Esc cancel    Ctrl-U clear", self.c["dim"])
                    win.move(row, 2 + pos - start)
                except curses.error:
                    pass
                win.refresh()
                k = self.getkey(win)
                if k in ("\n", "\r", "KEY_ENTER"):
                    return "".join(buf)
                if k in ("\x1b", "\x03"):
                    return None
                if k == "KEY_RESIZE":
                    self.scr.refresh()
                elif k in ("KEY_BACKSPACE", "\x7f", "\b"):
                    if pos:
                        del buf[pos - 1]
                        pos -= 1
                elif k == "KEY_DC":
                    if pos < len(buf):
                        del buf[pos]
                elif k == "KEY_LEFT":
                    pos = max(0, pos - 1)
                elif k == "KEY_RIGHT":
                    pos = min(len(buf), pos + 1)
                elif k in ("KEY_HOME", "\x01"):
                    pos = 0
                elif k in ("KEY_END", "\x05"):
                    pos = len(buf)
                elif k == "\x15":
                    buf, pos = [], 0
                elif len(k) == 1 and k.isprintable():
                    buf.insert(pos, k)
                    pos += 1
        finally:
            try:
                curses.curs_set(0)
            except curses.error:
                pass
            self.scr.touchwin()
            self.scr.refresh()

    def too_small(self):
        h, w = self.size()
        if h < MIN_H or w < MIN_W:
            self.scr.erase()
            self.put(0, 0, "Please make the window at least %dx%d (now %dx%d)." % (MIN_W, MIN_H, w, h))
            self.scr.refresh()
            return True
        return False

    def wrap(self, text, width):
        return textwrap.wrap(text, width, break_long_words=True, break_on_hyphens=False) or [""]

    # ---- state helpers
    def default_out(self):
        return os.path.join(os.path.dirname(self.project), "Archive") if self.project else None

    def effective_out(self):
        return self.out_dir or self.default_out()

    def scan_valid(self):
        return bool(self.scan and self.project and self.scan["project"] == self.project)

    def predict(self, opts=None):
        if not self.scan_valid() or not self.core or self.core_err:
            return None
        o = {k: (opts or self.opts)[k] for k in PREDICTED}
        return self.core.predict(self.scan["data"], o)

    def command(self, scan_file=None):
        """The kdenlive_trim command for the current choices (only options that differ from the script's own
        defaults are listed). With scan_file, the scan command instead."""
        o, d = self.opts, builtin_defaults()
        a = [sys.executable, self.script, self.project]
        if self.out_dir:
            a += ["--out-dir", self.out_dir]
        if scan_file:
            a += ["--report-json", scan_file, "--handles", fmt_num(o["handles"]),
                  "--search-seconds", fmt_num(o["search_seconds"])]
        else:
            if o["quick_check"]:
                a.append("--quick-check")
            if o["handles"] != d["handles"]:
                a += ["--handles", fmt_num(o["handles"])]
            if o["min_saving"] != d["min_saving"]:
                a += ["--min-saving", fmt_num(o["min_saving"])]
            if o["long_gop"] != d["long_gop"]:
                a += ["--long-gop", o["long_gop"]]
            if o["audio"] != d["audio"]:
                a += ["--audio", o["audio"]]
            if o["proxies"] != d["proxies"]:
                a += ["--proxies", o["proxies"]]
            if not o["copy_unchanged"]:
                a.append("--no-copy-unchanged")
            if o["allow_drift"]:
                a.append("--allow-drift")
            if o["search_seconds"] != d["search_seconds"]:
                a += ["--search-seconds", fmt_num(o["search_seconds"])]
        if o["ffmpeg"] != d["ffmpeg"]:
            a += ["--ffmpeg", o["ffmpeg"]]
        if o["ffprobe"] != d["ffprobe"]:
            a += ["--ffprobe", o["ffprobe"]]
        return a

    def quoted(self, argv):
        return " ".join(shlex.quote(x) for x in argv)

    # ---- main screen
    def fields(self):
        """Everything the cursor can rest on: project, output, each option, then each action."""
        return ["project", "output"] + [o["key"] for o in OPTIONS] + ["act:%d" % i for i in range(len(ACTIONS))]

    def script_label(self, width):
        """The script's file name, or its whole path when it is not in this program's folder."""
        if not self.script:
            return "script not found"
        if os.path.dirname(self.script) == os.path.dirname(os.path.abspath(__file__)):
            return os.path.basename(self.script)
        return short_path(self.script, width)

    def draw_options(self, top, opt_w, sel):
        for i, o in enumerate(OPTIONS):
            attr = self.c["sel"] if sel == o["key"] else 0
            val = fmt_value(o, self.opts[o["key"]])
            changed = self.opts[o["key"]] != o["default"]
            self.put(top + i, 1, " %-18s" % o["label"], attr)
            self.put(top + i, 20, ("%s%s" % (val, " *" if changed else "")).ljust(opt_w - 19), attr)

    def draw_actions(self, top, x, act_w, sel):
        for i, (key, label, _, _) in enumerate(ACTIONS):
            if sel == "act:%d" % i:
                self.put(top + i, x, (" [%s] %s" % (key, label)).ljust(act_w), self.c["sel"] | curses.A_BOLD)
            else:
                self.put(top + i, x + 1, "[", self.c["dim"])
                self.put(top + i, x + 2, key, self.c["acc"] | curses.A_BOLD)
                self.put(top + i, x + 3, "] " + label)

    def draw_main(self):
        """Project and output on top, the savings prediction at the bottom. In between, when the window is tall
        enough: Options with the Actions list below them, and About on the right. In a shorter window, Options and
        Actions sit side by side, with About to the right or below them."""
        self.scr.erase()
        h, w = self.size()
        script = self.script_label(w // 2)
        self.bar(0, "Kdenlive Trim control dashboard".ljust(max(0, w - len(script) - 4)) + script)
        sel = self.fields()[self.cursor]
        opt_w = 20 + max(len(fmt_value(o, v)) for o in OPTIONS for v in
                         ([c for c, _ in o["choices"]] if o["type"] == "choice" else [self.opts[o["key"]]])) + 2
        act_w = max(len("[%s] %s" % (a[0], a[1])) for a in ACTIONS) + 2
        # stacked: title, project, output, Options heading + list, Actions heading + list, prediction (3), bottom bar
        stacked_rows = 1 + 2 + 1 + len(OPTIONS) + 1 + len(ACTIONS) + 3 + 1
        about_x = 1 + opt_w + 4
        self.stacked = h >= stacked_rows and w - about_x - 1 >= 30
        if self.stacked:
            gaps = dict(acts=0, pred=0, out=0, top=0)
            spare = h - stacked_rows
            for g in ("acts", "pred", "out", "top", "acts", "pred"):  # blank lines, most useful first
                if spare > 0:
                    gaps[g] += 1
                    spare -= 1
        else:
            act_x = 1 + opt_w + 2
            about_x = act_x + act_w + 3
            about_right = w - about_x - 1 >= 30
            n_list = max(len(OPTIONS), len(ACTIONS))
            avail = h - (1 + 2 + 1 + n_list + 3 + 1)
            if about_right:
                gaps = dict(pred=avail >= 1, out=avail >= 2, top=avail >= 3)
                about_h = 0
            else:
                gaps = dict(out=avail >= 9, pred=avail >= 7, top=0)
                about_h = avail - gaps["out"] - gaps["pred"]  # "About" heading plus its text
        y = 1 + gaps["top"]
        for key, label, value, dim in (
                ("project", "Project", self.project or "(none: press Enter to choose one)", not self.project),
                ("output", "Output", self.out_dir or ("%s  (default)" % self.default_out() if self.project
                                                      else "(default: an Archive folder next to the project)"),
                 not self.out_dir)):
            attr = self.c["sel"] if sel == key else 0
            self.put(y, 1, " %-9s" % label, attr | curses.A_BOLD)
            self.put(y, 12, short_path(value, w - 14), self.c["dim"] if dim else 0)
            y += 1
        y += gaps["out"]
        if self.stacked:
            self.put(y, 1, "Options", curses.A_BOLD)
            self.put(y, about_x, "About", curses.A_BOLD)
            top = y + 1
            self.draw_options(top, opt_w, sel)
            y = top + len(OPTIONS) + gaps["acts"]
            self.put(y, 1, "Actions", curses.A_BOLD)
            self.draw_actions(y + 1, 1, act_w, sel)
            y += 1 + len(ACTIONS)
            self.draw_about(sel, top, about_x, w - about_x - 1, y - top)
        else:
            self.put(y, 1, "Options", curses.A_BOLD)
            self.put(y, act_x, "Actions", curses.A_BOLD)
            if about_right:
                self.put(y, about_x, "About", curses.A_BOLD)
            top = y + 1
            self.draw_options(top, opt_w, sel)
            self.draw_actions(top, act_x, act_w, sel)
            y = top + n_list
            if about_right:
                self.draw_about(sel, top, about_x, w - about_x - 1, n_list + gaps["pred"])
            else:
                self.put(y, 1, "About", curses.A_BOLD)
                self.draw_about(sel, y + 1, 3, w - 5, about_h - 1)
                y += about_h
        y += gaps["pred"]
        self.draw_prediction(y)
        if self.status:
            lines = textwrap.wrap(self.status, w - 2)[:3]  # up to three lines, over the ones above until a key
            for i, line in enumerate(lines):
                self.put(h - len(lines) + i, 0, (" " + line).ljust(w - 1), self.c["title"])
        else:
            self.footer(["\u2191\u2193 move", "\u2190\u2192 change", "Enter choose", "Tab next",
                         "letters in [ ] are shortcuts", "? help", "q quit"])
        self.scr.refresh()

    def about_lines(self, key):
        if key == "project":
            return ABOUT_PROJECT
        if key == "output":
            return ABOUT_OUTPUT
        if key.startswith("act:"):
            act = ACTIONS[int(key[4:])]
            lines = list(act[3])
            if act[2] in ("whatif_screen", "files_screen") and not self.scan_valid():
                lines.append("No scan yet: choosing this offers to scan first.")
            if act[2] == "run_job" and self.project and not self.scan_valid():
                lines.append("Tip: scan first to see what it will save.")
            return lines
        o = OPT_BY_KEY[key]
        about = o["about"]
        lines = list(about[self.opts[key]] if isinstance(about, dict) else about)
        extra = self.whatif_lines(key)
        return lines + ([""] + extra if extra else [])

    def whatif_lines(self, key):
        """Predicted effect of the other values of this option, for the About pane (numbers on one line)."""
        o = OPT_BY_KEY[key]
        if key == "search_seconds" and self.scan_valid():
            n = sum(1 for s in self.scan["data"]["sources"] if s.get("start_limited"))
            return ["Last scan: %d clip(s) had their start left untrimmed for lack of an exact cut point." % n]
        if key not in PREDICTED:
            return []
        now = self.predict()
        if not now:
            return ["Scan the project (s) to see what this changes."]
        alts = [(v, self.predict(dict(self.opts, **{key: v}))) for v in self.alternatives(o)]
        if o["type"] == "number":
            return ["If set to: " + ", ".join("%s saves %s" % (fmt_value(o, v), fmt_delta(p["saved"] - now["saved"]))
                                              for v, p in alts)]
        return [self.effect_text(o, v, now, p) for v, p in alts]

    def alternatives(self, o):
        cur = self.opts[o["key"]]
        if o["type"] == "choice":
            return [v for v, _ in o["choices"] if v != cur]
        return [v for v in o.get("whatif", []) if v != cur]

    def effect_text(self, o, v, now, p):
        parts = []
        if o["key"] == "quick_check":
            parts.append("data to move %s" % fmt_delta((p["read"] + p["written"]) - (now["read"] + now["written"])))
        else:
            parts.append("saves %s" % fmt_delta(p["saved"] - now["saved"]))
            if o["key"] == "copy_unchanged":
                parts.append("archive %s" % fmt_delta(p["archive"] - now["archive"]))
            parts.append("data to move %s" % fmt_delta((p["read"] + p["written"]) - (now["read"] + now["written"])))
            if o["key"] == "allow_drift" and v:
                parts.append("%d frame(s) one off" % p["drift_frames"])
        return "If %s: %s" % (fmt_value(o, v), ", ".join(parts))

    def draw_about(self, key, y, x, width, height):
        lines = []
        for t in self.about_lines(key):
            lines += self.wrap(t, width) if t else [""]
        if len(lines) > height:  # short of room: drop the blank separator lines first
            lines = [line for line in lines if line]
        for i, line in enumerate(lines[:height]):
            attr = 0
            if line.startswith("+"):
                attr = self.c["ok"]
            elif line.startswith("-"):
                attr = self.c["warn"]
            elif line.startswith("If "):
                attr = self.c["acc"]
            self.put(y + i, x, line, attr)

    def draw_prediction(self, y):
        """Three lines: the scan state (and anything stale), the predicted result, and the work involved."""
        h, w = self.size()
        self.put(y, 1, "Savings prediction", curses.A_BOLD)
        x = 21
        if self.core_err:
            self.put(y, x, self.core_err, self.c["bad"])
            return
        if not self.project:
            self.put(y, x, "choose a project first", self.c["dim"])
            return
        if not self.scan_valid():
            self.put(y, x, "choose Scan (s): reads a little of each file, writes nothing", self.c["dim"])
            return
        p = self.predict()
        d = self.scan["data"]
        head = "scanned %s, %d source file(s)" % (fmt_ago(self.scan["time"]), len(d["sources"]))
        self.put(y, x, head, self.c["dim"])
        warn = []
        if p["approx"] or self.scan["search_seconds"] != self.opts["search_seconds"]:
            warn.append("cut settings changed, scan again")
        if p["missing"]:
            warn.append("%d file(s) not found (see Files)" % p["missing"])
        if warn:
            self.put(y, x + 2 + len(head), "! " + "; ".join(warn), self.c["warn"])
        line = "Original files %s  \u2192  %s   %s" % (fmt_size_ui(p["before"]), fmt_size_ui(p["after"]),
                                                      self.result_text(p))
        self.put(y + 1, 3, line, self.c["ok"] if p["saved"] > 0 else self.c["warn"])
        line = "Trim %d, copy %d.  Data to read and write: about %s" % (p["trims"], p["copies"],
                                                                         fmt_size_ui(p["read"] + p["written"]))
        if not self.opts["copy_unchanged"]:
            line = "Archive %s + %s left in the original folders.  " % (
                fmt_size_ui(p["archive"]), fmt_size_ui(p["external"])) + line
        self.put(y + 2, 3, line)

    def result_text(self, p):
        if p["saved"] >= 0:
            return "saves %s (%.0f%%)" % (fmt_size_ui(p["saved"]), p["saved_pct"])
        return "GROWS by %s (see w)" % fmt_size_ui(-p["saved"])

    def change(self, key, direction):
        o = OPT_BY_KEY[key]
        v = self.opts[key]
        if o["type"] == "choice":
            vals = [c for c, _ in o["choices"]]
            self.opts[key] = vals[(vals.index(v) + direction) % len(vals)] if v in vals else vals[0]
        elif o["type"] == "number":
            self.opts[key] = min(o["max"], max(o["min"], round(v + direction * o["step"], 3)))

    def edit_field(self, key):
        if key == "project":
            p = self.browse("project")
            if p:
                self.set_project(p)
            return
        if key == "output":
            p = self.browse("folder")
            if p:
                self.out_dir = p
            return
        o = OPT_BY_KEY[key]
        if o["type"] == "choice":
            self.change(key, 1)
        elif o["type"] == "number":
            s = self.ask_text(o["label"], "%s, in %s (%s to %s):" % (o["label"], {"s": "seconds", "%": "percent"}.get(
                o["unit"], o["unit"]), fmt_num(o["min"]), fmt_num(o["max"])), fmt_num(self.opts[key]))
            if s is not None:
                try:
                    v = float(s.strip())
                    if not o["min"] <= v <= o["max"]:
                        raise ValueError
                    self.opts[key] = v
                except ValueError:
                    self.error("%s must be a number from %s to %s." % (o["label"], fmt_num(o["min"]),
                                                                         fmt_num(o["max"])))
        else:
            s = self.ask_text(o["label"], "%s (a program name on your PATH, or its full path):" % o["label"],
                              str(self.opts[key]))
            if s is not None:
                self.opts[key] = s.strip() or o["default"]

    def set_project(self, path):
        self.project = os.path.abspath(path)
        self.out_dir = None
        self.scan = None
        self.cfg["last_dir"] = os.path.dirname(self.project)
        self.flash("Project selected. Choose Scan (s) to see the predicted saving.")

    def move_vertical(self, d):
        """Up/Down through the options column, then on into the actions column (and round again)."""
        self.cursor = (self.cursor + d) % len(self.fields())

    def do_action(self, key):
        """Run the action with this shortcut key. Returns True when the program should quit."""
        name = ACTION_BY_KEY[key][2]
        if name == "quit":
            return self.confirm("Quit Kdenlive Trim?", "Quit", "Quit", "Stay")
        getattr(self, name)()
        return False

    def save_defaults(self):
        self.cfg["defaults"] = dict(self.opts)
        err = save_config(self.cfg)
        if err:
            self.error(["Could not save your defaults:", err], "Defaults not saved")
        else:
            self.cfg_problem = None  # the file is good again, so it is kept up to date on quit as usual
            self.notice("Defaults saved", ["These options are now your defaults; they are loaded every time this "
                                           "program starts.", ("Saved in %s" % CONFIG_PATH, self.c["dim"])])

    def reset_defaults(self):
        if self.confirm("Put every option back to the script's built-in defaults? Your saved defaults stay as they "
                        "are until you choose Save defaults.", "Reset options", "Reset", "Cancel", default=1):
            self.opts = builtin_defaults()
            self.flash("Options reset to the built-in defaults.")

    def main_loop(self):
        while True:
            if self.too_small():
                if self.getkey() in ("q", "\x03"):
                    return
                continue
            self.draw_main()
            k = self.getkey()
            self.status = ""
            key = self.fields()[self.cursor]
            on_action = key.startswith("act:")
            if k in ("\x1b", "\x03"):
                k = "q"
            if k in ("KEY_UP", "k"):
                self.move_vertical(-1)
            elif k in ("KEY_DOWN", "j"):
                self.move_vertical(1)
            elif k == "\t":
                self.cursor = (self.cursor + 1) % len(self.fields())
            elif k == "KEY_BTAB":
                self.cursor = (self.cursor - 1) % len(self.fields())
            elif k == "KEY_LEFT" and on_action and not self.stacked:
                # side-by-side lists: back across to the option on the same row
                self.cursor = 2 + min(int(key[4:]), len(OPTIONS) - 1)
            elif k in ("KEY_LEFT", "KEY_RIGHT") and on_action:
                pass
            elif k in ("KEY_LEFT", "KEY_RIGHT", " ") and key in OPT_BY_KEY:
                self.change(key, -1 if k == "KEY_LEFT" else 1)
            elif k in ("\n", "\r", "KEY_ENTER", " "):
                if on_action:
                    if self.do_action(ACTIONS[int(key[4:])][0]):
                        return
                elif k != " ":
                    self.edit_field(key)
            elif k in ("KEY_BACKSPACE", "\x7f", "\b", "KEY_DC") and key == "output":
                self.out_dir = None
                self.flash("Output set back to the default.")
            elif k == "p":
                self.edit_field("project")
            elif k == "o":
                self.edit_field("output")
            elif k in ACTION_BY_KEY:
                if self.do_action(k):
                    return

    def getkey(self, win=None):
        """One key as a string: a character, or a curses key name such as KEY_UP. Reads from win if given (a box),
        so the cursor stays where that box put it."""
        src = win or self.scr
        while True:
            try:
                k = src.get_wch()
            except curses.error:
                continue
            if k == curses.KEY_RESIZE:
                curses.update_lines_cols()
                self.scr.clear()  # repaint everything at the new size
                return "KEY_RESIZE"
            if isinstance(k, int):
                return curses.keyname(k).decode("ascii", "replace")
            if k == "\x1b":
                return self.escape_sequence(src)
            return k

    def escape_sequence(self, src):
        """Esc on its own, or an arrow/page key that curses did not decode (some terminals send ESC [ B
        where the terminal database expects ESC O B)."""
        seq = ""
        src.nodelay(True)
        try:
            for _ in range(3):
                try:
                    c = src.get_wch()
                except curses.error:
                    break
                seq += c if isinstance(c, str) else ""
                if seq[-1:].isalpha() or seq[-1:] == "~":
                    break
        finally:
            src.nodelay(False)
        keys = {"[A": "KEY_UP", "[B": "KEY_DOWN", "[C": "KEY_RIGHT", "[D": "KEY_LEFT", "OA": "KEY_UP",
                "OB": "KEY_DOWN", "OC": "KEY_RIGHT", "OD": "KEY_LEFT", "[H": "KEY_HOME", "[F": "KEY_END",
                "OH": "KEY_HOME", "OF": "KEY_END", "[5~": "KEY_PPAGE", "[6~": "KEY_NPAGE", "[3~": "KEY_DC",
                "[Z": "KEY_BTAB"}
        return keys.get(seq, "\x1b")

    # ---- text screens
    def pager(self, title, items, footer=("↑↓ scroll", "Esc back")):
        """Scrollable text screen. items: (text, attr) or (text, attr, hang); long lines wrap to the window, with
        continuation lines indented by hang (default: the line's own indent), so tables stay readable."""
        top = 0
        while True:
            if self.too_small():
                if self.getkey() in ("\x1b", "q"):
                    return
                continue
            self.scr.erase()
            h, w = self.size()
            lines = []
            for item in items:
                t, a = item[0], item[1]
                hang = item[2] if len(item) > 2 else len(t) - len(t.lstrip(" "))
                if len(t) <= w - 3:
                    lines.append((t, a))
                else:
                    lines += [(x, a) for x in textwrap.wrap(t, w - 3, subsequent_indent=" " * min(hang, w // 2),
                                                            break_long_words=True, break_on_hyphens=False)]
            self.bar(0, title)
            body = h - 3
            for i, (t, a) in enumerate(lines[top:top + body]):
                self.put(2 + i, 1, t, a)
            self.footer(list(footer))
            self.scr.refresh()
            k = self.getkey()
            if k in ("\x1b", "q", "\n", "\r", "KEY_ENTER", "\x03"):
                return k
            if k == "KEY_UP":
                top = max(0, top - 1)
            elif k == "KEY_DOWN":
                top = max(0, min(len(lines) - body, top + 1))
            elif k == "KEY_PPAGE":
                top = max(0, top - body)
            elif k in ("KEY_NPAGE", " "):
                top = max(0, min(len(lines) - body, top + body))
            elif len(k) == 1:
                return k

    def help_screen(self):
        rows = [
            ("Control dashboard", curses.A_BOLD),
            ("  \u2191 \u2193          move between the project, the output folder, the options and the actions", 0, 15),
            ("  Tab / Shift-Tab  next / previous item", 0, 15),
            ("  \u2190 \u2192 or Space change the highlighted option (in a short window, \u2190 on an action goes back across to the options)", 0, 15),
            ("  Enter        choose: browse (project, output), type a value, or run the highlighted action", 0, 15),
            ("  Backspace    on Output: go back to the default Archive folder", 0, 15),
            ("  p / o        browse for the project / output folder", 0, 15),
            ("", 0),
            ("Actions (each is in the Actions area, and has a shortcut key)", curses.A_BOLD),
        ]
        for key, label, _, about in ACTIONS:
            rows.append(("  %-3s %-15s %s" % (key, label, about[0]), 0, 22))
        rows += [
            ("", 0),
            ("Boxes", curses.A_BOLD),
            ("  Questions, errors and results open in a box in the middle of the window.", 0),
            ("  \u2190 \u2192 choose a button, Enter confirms, y / n answer directly, Esc cancels.", 0),
            ("", 0),
            ("Browser", curses.A_BOLD),
            ("  Enter        open a folder or choose a file", 0, 15),
            ("  \u2190 or Backspace  up one folder        ~ home        v /Volumes (network shares)", 0),
            ("  g            type a path              / filter by name     .  show hidden files", 0),
            ("  Esc          cancel", 0),
            ("", 0),
            ("About the savings prediction", curses.A_BOLD),
            ("  Sizes are estimates from the scan: video is assumed to be spread evenly over its frames, and", 0),
            ("  audio is sized from its bit rate. 'Data to read and write' is what drives the run time,", 0),
            ("  especially over a network share. Options marked * differ from the script's built-in defaults.", 0),
            ("  Handles and the search window change the cuts themselves: scan again after changing them.", 0),
            ("", 0),
            ("Text size", curses.A_BOLD),
            ("  The terminal sets the font: Cmd + / Cmd - / Cmd 0 in Terminal. This program fits itself to it.", 0),
            ("", 0),
            ("Saved settings: %s" % CONFIG_PATH, self.c["dim"]),
        ]
        self.pager("Help", rows)

    # ---- browser
    def browse(self, mode):
        """Pick a .kdenlive file (mode 'project') or a folder (mode 'folder'). Returns a path or None."""
        start = None
        if mode == "folder" and self.effective_out():
            start = os.path.dirname(self.effective_out())
        if not start and self.project:
            start = os.path.dirname(self.project)
        start = start or self.cfg.get("last_dir") or os.path.expanduser("~")
        while start and not os.path.isdir(start):
            start = os.path.dirname(start)
        cwd = start or os.path.expanduser("~")
        prev = None  # folder before the last move, to go back to if a folder cannot be opened
        cursor, top, filt, hidden, came_from = 0, 0, "", False, None
        title = "Choose the project (.kdenlive)" if mode == "project" else "Choose the output folder"
        while True:
            entries = []
            if mode == "folder":
                entries.append(("[ Use this folder ]", cwd, "use", None))
            if os.path.dirname(cwd) != cwd:
                entries.append(("..", os.path.dirname(cwd), "dir", None))
            try:
                names = sorted(os.listdir(cwd), key=str.lower)
            except OSError as e:
                self.error(["Cannot open this folder:", cwd, e.strerror or str(e)])
                back = prev if prev and prev != cwd else os.path.dirname(cwd)
                if back == cwd:
                    return None
                cwd, prev, cursor, top, filt = back, None, 0, 0, ""
                continue
            for n in names:
                if (n.startswith(".") and not hidden) or (filt and filt.lower() not in n.lower()):
                    continue
                p = os.path.join(cwd, n)
                try:
                    isdir = os.path.isdir(p)
                    if isdir:
                        entries.append((n + "/", p, "dir", None))
                    elif mode == "project" and n.lower().endswith(".kdenlive"):
                        entries.append((n, p, "file", os.path.getmtime(p)))
                except OSError:
                    continue
            if came_from:
                cursor = next((i for i, e in enumerate(entries) if e[1] == came_from), cursor)
                came_from = None
            cursor = max(0, min(cursor, len(entries) - 1))
            if self.too_small():
                if self.getkey() in ("\x1b", "q"):
                    return None
                continue
            self.scr.erase()
            h, w = self.size()
            self.bar(0, title)
            self.put(1, 1, short_path(cwd, w - 3), curses.A_BOLD)
            if filt:
                self.put(1, max(2, w - len(filt) - 12), "filter: %s" % filt, self.c["acc"])
            body = h - 5
            if cursor < top:
                top = cursor
            elif cursor >= top + body:
                top = cursor - body + 1
            for i, (label, p, kind, mtime) in enumerate(entries[top:top + body]):
                y = 3 + i
                attr = self.c["sel"] if top + i == cursor else (self.c["acc"] if kind == "use" else
                                                                (curses.A_BOLD if kind == "dir" else 0))
                self.put(y, 2, label.ljust(w - 24) if kind == "file" else label, attr)
                if kind == "file":
                    self.put(y, w - 20, time.strftime("%Y-%m-%d %H:%M", time.localtime(mtime)),
                             attr if top + i == cursor else self.c["dim"])
            if mode == "project" and not any(e[2] == "file" for e in entries):
                self.put(h - 3, 2, "No .kdenlive files in this folder.", self.c["dim"])
            self.footer(["Enter open/choose", "← up", "~ home", "v /Volumes", "g go to path", "/ filter",
                         ". hidden", "Esc cancel"])
            self.scr.refresh()
            k = self.getkey()
            if k in ("\x1b", "q", "\x03"):
                return None
            if k == "KEY_UP":
                cursor -= 1
            elif k == "KEY_DOWN":
                cursor += 1
            elif k == "KEY_PPAGE":
                cursor -= body
            elif k == "KEY_NPAGE":
                cursor += body
            elif k == "KEY_HOME":
                cursor = 0
            elif k == "KEY_END":
                cursor = len(entries) - 1
            elif k in ("KEY_LEFT", "KEY_BACKSPACE", "\x7f", "\b"):
                if os.path.dirname(cwd) != cwd:
                    prev, came_from, cwd, filt = cwd, cwd, os.path.dirname(cwd), ""
            elif k in ("\n", "\r", "KEY_ENTER", "KEY_RIGHT") and entries:
                label, p, kind, _ = entries[cursor]
                if kind == "use":
                    self.cfg["last_dir"] = p
                    return p
                if kind == "dir":
                    came_from = cwd if label == ".." else None
                    prev, cwd, cursor, top, filt = cwd, p, 0, 0, ""
                elif kind == "file" and k != "KEY_RIGHT":
                    self.cfg["last_dir"] = cwd
                    return p
            elif k == "~":
                prev, cwd, cursor, top, filt = cwd, os.path.expanduser("~"), 0, 0, ""
            elif k == "v":
                if os.path.isdir("/Volumes"):
                    prev, cwd, cursor, top, filt = cwd, "/Volumes", 0, 0, ""
                else:
                    self.error("There is no /Volumes folder on this computer (it is where a Mac shows network "
                               "shares and drives).")
            elif k == ".":
                hidden = not hidden
            elif k == "/":
                s = self.ask_text("Filter", "Show only names containing (empty shows everything):", filt)
                if s is not None:
                    filt, cursor, top = s, 0, 0
            elif k == "g":
                s = self.ask_text("Go to", "A full path, or one relative to this folder (~ is your home folder):",
                                  hint=short_path(cwd, 70))
                if s and s.strip():
                    p = os.path.abspath(os.path.join(cwd, os.path.expanduser(s.strip())))
                    if os.path.isdir(p):
                        prev, cwd, cursor, top, filt = cwd, p, 0, 0, ""
                    elif mode == "project" and os.path.isfile(p) and p.lower().endswith(".kdenlive"):
                        self.cfg["last_dir"] = os.path.dirname(p)
                        return p
                    elif mode == "folder" and os.path.isdir(os.path.dirname(p)):
                        if self.confirm(["This folder does not exist yet:", p, "Use it? It is created when the run "
                                         "starts."], "New folder"):
                            return p
                    else:
                        self.error(["Not found:", p] + (["(Only .kdenlive files can be chosen here.)"]
                                                        if mode == "project" and os.path.isfile(p) else []))

    # ---- scan
    def need_project(self):
        if self.project:
            return True
        self.error("Choose a project first: highlight Project and press Enter.", "No project")
        return False

    def need_scan(self):
        """True if there is a scan of the current project; otherwise offers to scan now."""
        if self.scan_valid():
            return True
        if not self.need_project():
            return False
        if self.confirm("This needs a scan of the project. Scan it now? (It reads a little of each file and "
                        "writes nothing.)", "No scan yet", "Scan", "Cancel"):
            self.run_scan()
        return self.scan_valid()

    def run_scan(self):
        if not self.need_project():
            return
        if self.core_err:
            self.error(self.core_err, "Script problem")
            return
        fd, tmp = tempfile.mkstemp(prefix="kdenlive_trim_scan_", suffix=".json")
        os.close(fd)
        argv = self.command(scan_file=tmp)
        st = {"i": 0, "n": 0, "name": "", "status": "Starting", "errors": []}
        try:
            proc = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                    stderr=subprocess.PIPE, text=True, errors="replace")
        except OSError as e:
            self.error(["Could not start the scan:", str(e)], "Scan failed")
            return

        def reader():
            for line in proc.stderr:
                line = line.rstrip("\n")
                if line.startswith("PROGRESS "):
                    parts = line.split(" ", 3)
                    st["i"], st["n"] = int(parts[1]), int(parts[2])
                    st["name"] = parts[3] if len(parts) > 3 else ""
                    st["status"] = "Analysing"
                elif line.startswith("STATUS "):
                    st["status"], st["name"] = line[7:], ""
                elif line.strip():
                    st["errors"].append(line)
        t = threading.Thread(target=reader, daemon=True)
        t.start()
        t0 = time.time()
        cancelled = False
        self.draw_main()  # the box sits on top of the main screen
        try:
            while proc.poll() is None or t.is_alive():
                win = self.draw_scan(st, t0)
                win.timeout(200)
                try:
                    k = win.get_wch()
                except curses.error:
                    k = None
                if k == curses.KEY_RESIZE:
                    curses.update_lines_cols()
                    self.scr.clear()
                    self.draw_main()
                elif k in ("\x1b", "x", "\x03", "q") and proc.poll() is None:
                    cancelled = True
                    proc.send_signal(signal.SIGINT)
                    try:
                        proc.wait(5)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                    break
        finally:
            self.scr.touchwin()
            self.scr.refresh()
        t.join(1)
        try:
            if cancelled:
                self.notice("Scan cancelled", "The scan was stopped. Nothing was written.", "warn")
            elif proc.returncode != 0:
                lines = st["errors"][-12:] or ["The scan stopped with exit code %s." % proc.returncode]
                self.error(lines, "Scan failed")
            else:
                with open(tmp, encoding="utf-8") as f:
                    data = json.load(f)
                self.scan = {"data": data, "time": time.time(), "project": self.project,
                             "search_seconds": self.opts["search_seconds"], "out_dir": self.out_dir}
                self.draw_main()
                p = self.predict()
                lines = ["Scanned %d source file(s) in %ds." % (len(data["sources"]), time.time() - t0)]
                if p:
                    lines.append(("With your options: %s of original files \u2192 %s, %s." % (
                        fmt_size_ui(p["before"]), fmt_size_ui(p["after"]), self.result_text(p).replace(" (see w)", "")),
                        self.c["ok"] if p["saved"] > 0 else self.c["warn"]))
                    if p["missing"]:
                        lines.append(("%d file(s) used by the project were not found (see Files)." % p["missing"],
                                      self.c["warn"]))
                if data["project"].get("moved_from"):
                    lines.append("The project was moved, so its files were found next to it, as Kdenlive does.")
                lines.append(("What-if compares the options; Files shows each file.", self.c["dim"]))
                self.notice("Scan complete", lines)
        except (OSError, ValueError) as e:
            self.error(["Could not read the scan:", str(e)], "Scan failed")
        finally:
            try:
                os.remove(tmp)
            except OSError:
                pass

    def draw_scan(self, st, t0):
        """The scan's progress box. Returns its window (keys are read from it)."""
        frac = (st["i"] + 1) / st["n"] if st["n"] else 0.0
        bw = 40
        n = int(round(frac * bw))
        if st["n"] and st["status"] == "Analysing":
            doing = "File %d of %d: %s" % (st["i"] + 1, st["n"], st["name"])
        else:
            doing = st["status"]
        lines = [("Reading a little of each file to work out the cuts. Nothing is written.", self.c["dim"]), "",
                 ("\u2588" * n + "\u2591" * (bw - n) + "  %3d%%" % (frac * 100), self.c["acc"]), doing, "",
                 ("Elapsed %ds.  Esc cancels." % (time.time() - t0), self.c["dim"])]
        win, _, _ = self.draw_box("Scanning %s" % os.path.basename(self.project), lines, "info", width=74)
        win.refresh()
        return win

    # ---- what-if and files
    def whatif_rows(self):
        rows = []
        for o in OPTIONS:
            if o["key"] not in PREDICTED:
                continue
            for v in self.alternatives(o):
                rows.append((o, v, self.predict(dict(self.opts, **{o["key"]: v}))))
        return rows

    def whatif_screen(self):
        if not self.need_scan():
            return
        now = self.predict()
        rows = self.whatif_rows()
        cursor, top = 0, 0
        while True:
            if self.too_small():
                if self.getkey() in ("\x1b", "q"):
                    return
                continue
            self.scr.erase()
            h, w = self.size()
            self.bar(0, "What each option would change (predicted from the scan, other options as set)")
            moved = now["read"] + now["written"]
            self.put(2, 1, "Now:  %s → %s, %s, data to move %s" % (
                fmt_size_ui(now["before"]), fmt_size_ui(now["after"]), self.result_text(now), fmt_size_ui(moved)),
                curses.A_BOLD)
            # column x positions: option, change to, saves, data to move
            cx = (1, 19, 40, 60)
            for x, t in zip(cx, ("Option", "Change to", "Saves", "Data to move")):
                self.put(4, x, t, curses.A_UNDERLINE)
            body = max(3, h - 13)
            if cursor < top:
                top = cursor
            elif cursor >= top + body:
                top = cursor - body + 1
            for i, (o, v, p) in enumerate(rows[top:top + body]):
                y = 5 + i
                sel = top + i == cursor
                better = p["saved"] - now["saved"]
                mv = p["read"] + p["written"]
                cells = (o["label"], fmt_value(o, v),
                         "%s (%s)" % (fmt_size_ui(p["saved"]), fmt_delta(better)),
                         "%s (%s)" % (fmt_size_ui(mv), fmt_delta(mv - moved)))
                attrs = (0, 0, self.c["ok"] if better > 1000 else (self.c["warn"] if better < -1000 else 0),
                         self.c["ok"] if mv < moved - 1000 else (self.c["warn"] if mv > moved + 1000 else 0))
                if sel:
                    self.put(y, 1, " " * (w - 3), self.c["sel"])
                for x, t, a, nx in zip(cx, cells, attrs, cx[1:] + (w,)):
                    self.put(y, x, t, self.c["sel"] if sel else a, width=nx - x - 1)
            # pros and cons of the highlighted change
            o, v, p = rows[cursor]
            about = o["about"][v] if isinstance(o["about"], dict) else o["about"]
            y = 6 + body
            self.put(y, 1, "─" * (w - 3), self.c["dim"])
            yy = y + 1
            for t in about:
                for line in self.wrap(t, w - 4):
                    if yy < h - 1:
                        attr = self.c["ok"] if t.startswith("+") else (self.c["warn"] if t.startswith("-") else 0)
                        self.put(yy, 2, line, attr)
                        yy += 1
            if now["approx"] and o["key"] != "handles" and yy < h - 1:
                self.put(yy, 2, "Handles changed since the scan: figures for the cuts are estimates until you rescan.",
                         self.c["dim"])
            self.footer(["↑↓ select", "Enter apply this change", "f files", "Esc back"])
            self.scr.refresh()
            k = self.getkey()
            if k in ("\x1b", "q", "\x03", "w"):
                return
            if k == "KEY_UP":
                cursor = max(0, cursor - 1)
            elif k == "KEY_DOWN":
                cursor = min(len(rows) - 1, cursor + 1)
            elif k in ("\n", "\r", "KEY_ENTER"):
                o, v, _ = rows[cursor]
                self.opts[o["key"]] = v
                self.flash("%s set to %s." % (o["label"], fmt_value(o, v)))
                return
            elif k == "f":
                self.files_screen()

    def files_screen(self):
        if not self.need_scan():
            return
        p = self.predict()
        files = sorted(p["files"], key=lambda f: (f["action"] != "trim", -(f["before"] - f["after"]),
                                                  f["name"].lower()))
        rows = [("%-8s %10s %10s %10s  %s" % ("Action", "Before", "After", "Saves", "File"), curses.A_UNDERLINE)]
        for f in files:
            act = {"trim": "TRIM", "copy": "COPY", "keep": "LEAVE", "missing": "MISSING"}[f["action"]]
            attr = {"trim": self.c["ok"], "missing": self.c["bad"]}.get(f["action"], 0)
            note = ("  (%s)" % f["note"]) if f["note"] else ""
            saves = fmt_size_ui(f["before"] - f["after"]) if abs(f["before"] - f["after"]) >= 1000 else "-"
            rows.append(("%-8s %10s %10s %10s  %s%s" % (act, fmt_size_ui(f["before"]), fmt_size_ui(f["after"]), saves,
                                                        f["name"], note), attr, 42))
        rows.append(("", 0))
        rows.append(("TRIM = trimmed into videos/, COPY = copied unchanged, LEAVE = left where it is "
                     "(Copy other files: no), MISSING = not found.", self.c["dim"]))
        rows.append(("Sizes include each video's proxy. Estimates from the scan.", self.c["dim"]))
        self.pager("Per-file prediction: %d to trim, %d to copy" % (p["trims"], p["copies"]), rows)

    # ---- command and run
    def command_screen(self):
        if not self.need_project():
            return
        cmd = self.quoted(self.command())
        h, w = self.size()
        rows = [("This is the command Run uses (options that differ from the script's built-in defaults):", 0),
                ("", 0)]
        rows += [(line, curses.A_BOLD) for line in self.wrap(cmd, w - 4)]
        rows += [("", 0), ("y copies it to the clipboard (macOS)", self.c["dim"])]
        k = self.pager("Command line", rows, footer=("y copy", "Esc back"))
        if k == "y":
            if shutil.which("pbcopy"):
                subprocess.run(["pbcopy"], input=cmd, text=True)
                self.notice("Copied", "The command is on the clipboard.")
            else:
                self.error("pbcopy was not found (it is part of macOS), so the command could not be copied.")

    def run_job(self):
        if not self.need_project():
            return
        if self.core_err:
            self.error(self.core_err, "Script problem")
            return
        out = self.effective_out()
        complete = False
        if os.path.isdir(out):
            left = [n for n in os.listdir(out) if n not in ("kdenlive_trim.log", ".DS_Store")]
            archived = os.path.join(out, os.path.basename(self.project))
            if left and os.path.isfile(archived) and os.path.isfile(os.path.join(out, "kdenlive_trim.log")):
                # an archive of this project from an earlier run: offer to finish it rather than start again
                if not self.confirm(["This output folder already has an archive of this project:", (out, self.c["dim"]),
                                     "Complete it: bring in only the files its project still uses from outside the "
                                     "archive (for example after a failed copy). Everything already in it stays as "
                                     "it is, and its project file is backed up before it is updated.",
                                     ("To start again from scratch instead, delete or move that folder.",
                                      self.c["dim"])], "Archive already there", "Complete it", "Cancel"):
                    return
                complete = True
            elif left:
                self.error(["The output folder already has files from an earlier run:", out,
                            "Move or delete it, or choose another output folder."], "Output folder not empty")
                return
        argv = self.command() + (["--complete"] if complete else [])
        lines = ["Trim %s" % os.path.basename(self.project), ("into %s" % out, self.c["dim"])]
        p = self.predict()
        if p:
            lines.append("Predicted: %s \u2192 %s, %s." % (fmt_size_ui(p["before"]), fmt_size_ui(p["after"]),
                                                           self.result_text(p).replace(" (see w)", "")))
        else:
            lines.append(("Not scanned yet, so there is no prediction.", self.c["dim"]))
        flags = argv[3:]
        lines.append(("Options: %s" % (self.quoted(flags) if flags else "the script's defaults"), self.c["dim"]))
        if not complete and not self.confirm(lines, "Start the trim?", "Start", "Cancel"):
            return
        save_config(dict(self.cfg, last_project=self.project))
        curses.def_prog_mode()
        curses.endwin()
        print("\n%s\n" % self.quoted(argv), flush=True)
        # the trim script handles Ctrl-C itself (cleans up and stops); this program just waits for it
        old = signal.signal(signal.SIGINT, lambda *_: None)
        try:
            rc = subprocess.call(argv)
        except OSError as e:
            print("Could not start: %s" % e)
            rc = -1
        finally:
            signal.signal(signal.SIGINT, old)
        status = {0: "Finished.", 130: "Interrupted."}.get(rc, "Stopped (exit code %s)." % rc)
        try:
            input("\n%s Press Enter to go back to the control dashboard." % status)
        except (EOFError, KeyboardInterrupt):
            pass
        curses.reset_prog_mode()
        self.scr.clear()
        self.draw_main()
        log = os.path.join(out, "kdenlive_trim.log")
        if rc == 0:
            self.notice("Run finished", ["The archive is in:", out, "Its log: %s" % log,
                                         "Open the new project in Kdenlive and check it before deleting anything."])
        elif rc == 130:
            left = os.path.isdir(out) and any(n not in ("kdenlive_trim.log", ".DS_Store") for n in os.listdir(out))
            self.notice("Run interrupted", ["The run was stopped. The original project and media are untouched.",
                                            "Delete the %s folder before running again." % out if left else
                                            "Nothing was written."], "warn")
        else:
            self.error(["The run stopped with an error (exit code %s)." % rc,
                        "Its message was shown in the terminal just before you pressed Enter, and is in the log "
                        "if the run got that far:", log], "Run stopped")

def menu_start(stdscr, args):
    curses.raw()  # Ctrl-C arrives as a key, so it cannot kill the program mid-draw
    stdscr.keypad(True)
    try:
        curses.curs_set(0)
    except curses.error:
        pass
    app = App(stdscr, args)
    try:
        app.main_loop()
    finally:
        cfg = dict(app.cfg)
        if app.project:
            cfg["last_project"] = app.project
        cfg.pop("script", None)  # older versions remembered a script path; the control dashboard always runs this file
        if not app.cfg_problem:  # a file that could not be read is left as it is, not replaced on the way out
            save_config(cfg)


# options that only make sense for a run started from the command line, so --gui refuses them
NOT_IN_MENU = (("report", "--report"), ("report_json", "--report-json"), ("output", "-o/--output"),
               ("plain", "--plain"), ("complete", "--complete"))


def menu_main(argv):
    """The control dashboard: no arguments, or --gui with an optional project and any of its own options, which are
    set for that session in place of the saved defaults (until Save defaults keeps them). Scan and Run start this
    same file."""
    ap = make_parser(menu=True)
    ap.prog = "%s --gui" % os.path.basename(sys.argv[0])
    ap.description = ("Open the control dashboard, optionally with a project selected. Any of its options given "
                      "here (and --out-dir) are set for this session, in place of your saved defaults.")
    given = vars(ap.parse_args(argv))
    refused = [flag for dest, flag in NOT_IN_MENU if dest in given]
    if refused:
        ap.error("%s can't be used with --gui, which takes only a project, --out-dir and the control dashboard's "
                 "own options "
                 "(--quick-check, --handles, --min-saving, --long-gop, --audio, --proxies, --no-copy-unchanged, "
                 "--allow-drift, --search-seconds, --ffmpeg, --ffprobe)" % " and ".join(refused))
    for o in OPTIONS:
        if o["type"] == "number" and o["key"] in given and not o["min"] <= given[o["key"]] <= o["max"]:
            ap.error("--%s must be from %s to %s in the control dashboard" % (o["key"].replace("_", "-"), fmt_num(o["min"]),
                                                                 fmt_num(o["max"])))
    if given.get("project") and not os.path.isfile(given["project"]):
        ap.error("project not found: %s" % given["project"])
    args = argparse.Namespace(project=given.get("project"), out_dir=given.get("out_dir"),
                              presets={k: v for k, v in given.items() if k in OPT_BY_KEY})
    if curses is None:
        sys.exit("The control dashboard needs Python's curses module, which this Python does not have.\n"
                 "Give a project and options on the command line instead (see --help).")
    if not sys.stdin.isatty() or not sys.stdout.isatty():
        sys.exit("The control dashboard needs a terminal window. To run without one, give a project and options "
                 "(see --help).")
    args.script_path = os.path.realpath(__file__)  # what Scan and Run start
    args.core = sys.modules[__name__]  # predict() and friends, from this file
    locale.setlocale(locale.LC_ALL, "")
    os.environ.setdefault("ESCDELAY", "25")  # Esc responds at once instead of after 1 s
    # stale LINES/COLUMNS variables would pin curses to an old window size; without them it asks the terminal
    os.environ.pop("LINES", None)
    os.environ.pop("COLUMNS", None)
    curses.wrapper(menu_start, args)


if __name__ == "__main__":
    main()
