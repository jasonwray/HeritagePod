#!/usr/bin/env python3
"""
ipod3g-sync: Drag-and-Drop FLAC -> AIFF Sync & iTunesDB Builder for 3rd Gen iPod (and 1G-5.5G)

Features:
- Converts FLAC -> 16-bit/44.1kHz stereo AIFF in RAM (/dev/shm or tmpdir) so the
  iPod flash storage is only written once, while keeping your PC's FLACs untouched.
- Copies native formats (.aiff, .aif, .wav, .mp3, .m4a) directly without re-encoding.
- Reads FLAC Vorbis comments and ID3 tags using zero external Python dependencies.
- Builds /iPod_Control/iTunes/iTunesDB natively (Master Playlist + Artist/Album/Track records)
  with zero reliance on iTunes or libgpod.
- Includes both a CLI and a Tkinter Desktop Drop/Sync GUI.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import List, Optional, Dict, Tuple

# Mac HFS+ epoch offset (seconds between 1904-01-01 and 1970-01-01)
MAC_EPOCH_OFFSET = 2082844800

SUPPORTED_EXTENSIONS = {".flac", ".aiff", ".aif", ".wav", ".mp3", ".m4a", ".m4b"}
MUSIC_DIRS_COUNT = 20  # F00 .. F19


@dataclass
class TrackMetadata:
    track_id: int
    dbid: int
    title: str
    artist: str
    album: str
    genre: str
    composer: str
    track_number: int
    total_tracks: int
    disc_number: int
    total_discs: int
    year: int
    duration_ms: int
    sample_rate: int
    bitrate_kbps: int
    file_size: int
    filetype_code: str      # 'AIFF', 'MPG3', 'M4A ', 'WAV '
    filetype_desc: str      # 'AIFF Audio File', 'MPEG audio file', etc.
    ipod_rel_path: str      # Colon-separated path: ':iPod_Control:Music:F00:T1001.aif'
    source_hash: str        # Quick fingerprint to avoid re-syncing duplicate tracks
    date_added: int         # Unix timestamp


# =====================================================================
# 1. Pure-Python Audio Metadata & Duration Parser (Zero Dependencies)
# =====================================================================

def _heuristic_from_path(path: Path) -> Tuple[str, str, int, str]:
    """Extract fallback (artist, album, track_number, title) from .../Artist/Album/01 - Title.ext"""
    stem = path.stem
    track_num = 0
    title = stem
    parts = stem.split(" ", 1)
    if len(parts) == 2:
        cleaned = parts[0].rstrip(".-_")
        if cleaned.isdigit():
            track_num = int(cleaned)
            title = parts[1].lstrip("-_ ")
    album = path.parent.name if path.parent.name else "Unknown Album"
    artist = path.parent.parent.name if path.parent.parent.name else "Unknown Artist"
    return artist, album, track_num, title


def parse_flac_metadata(path: Path) -> dict:
    """
    Parse FLAC STREAMINFO and VORBIS_COMMENT blocks directly in pure Python.
    Returns dict with title, artist, album, genre, composer, track_number,
    total_tracks, disc_number, total_discs, year, duration_ms, sample_rate,
    bits_per_sample, channels.
    """
    fb_artist, fb_album, fb_track, fb_title = _heuristic_from_path(path)
    info = {
        "title": fb_title,
        "artist": fb_artist,
        "album": fb_album,
        "genre": "",
        "composer": "",
        "track_number": fb_track,
        "total_tracks": 0,
        "disc_number": 1,
        "total_discs": 1,
        "year": 0,
        "duration_ms": 0,
        "sample_rate": 44100,
        "bits_per_sample": 16,
        "channels": 2,
    }

    with path.open("rb") as f:
        if f.read(4) != b"fLaC":
            raise ValueError(f"{path} is not a valid FLAC file")

        while True:
            header = f.read(4)
            if len(header) < 4:
                break
            is_last = (header[0] & 0x80) != 0
            block_type = header[0] & 0x7F
            length = (header[1] << 16) | (header[2] << 8) | header[3]
            block_data = f.read(length)

            if block_type == 0 and len(block_data) >= 18:
                # STREAMINFO block
                # Bytes 10..18: 20 bits sample_rate, 3 bits channels-1, 5 bits bps-1, 36 bits total_samples
                val = struct.unpack(">Q", block_data[10:18])[0]
                sample_rate = (val >> 44) & 0xFFFFF
                channels = ((val >> 41) & 0x07) + 1
                bps = ((val >> 36) & 0x1F) + 1
                total_samples = val & 0xFFFFFFFFF
                if sample_rate > 0:
                    info["sample_rate"] = sample_rate
                    info["duration_ms"] = int((total_samples * 1000) / sample_rate)
                info["channels"] = channels
                info["bits_per_sample"] = bps

            elif block_type == 4 and len(block_data) >= 8:
                # VORBIS_COMMENT block (little-endian)
                pos = 0
                vendor_len = struct.unpack_from("<I", block_data, pos)[0]
                pos += 4 + vendor_len
                if pos + 4 <= len(block_data):
                    num_comments = struct.unpack_from("<I", block_data, pos)[0]
                    pos += 4
                    tags: Dict[str, str] = {}
                    for _ in range(num_comments):
                        if pos + 4 > len(block_data):
                            break
                        c_len = struct.unpack_from("<I", block_data, pos)[0]
                        pos += 4
                        if pos + c_len > len(block_data):
                            break
                        comment = block_data[pos : pos + c_len].decode("utf-8", errors="replace")
                        pos += c_len
                        if "=" in comment:
                            k, v = comment.split("=", 1)
                            tags[k.upper().strip()] = v.strip()

                    if "TITLE" in tags and tags["TITLE"]:
                        info["title"] = tags["TITLE"]
                    if "ARTIST" in tags and tags["ARTIST"]:
                        info["artist"] = tags["ARTIST"]
                    elif "ALBUMARTIST" in tags and tags["ALBUMARTIST"]:
                        info["artist"] = tags["ALBUMARTIST"]
                    if "ALBUM" in tags and tags["ALBUM"]:
                        info["album"] = tags["ALBUM"]
                    if "GENRE" in tags and tags["GENRE"]:
                        info["genre"] = tags["GENRE"]
                    if "COMPOSER" in tags and tags["COMPOSER"]:
                        info["composer"] = tags["COMPOSER"]

                    # Track number (e.g. "3" or "03/12")
                    trk_raw = tags.get("TRACKNUMBER", "").strip()
                    if trk_raw:
                        if "/" in trk_raw:
                            p1, p2 = trk_raw.split("/", 1)
                            info["track_number"] = _safe_int(p1, fb_track)
                            info["total_tracks"] = _safe_int(p2)
                        else:
                            info["track_number"] = _safe_int(trk_raw, fb_track)
                    if "TRACKTOTAL" in tags or "TOTALTRACKS" in tags:
                        info["total_tracks"] = _safe_int(
                            tags.get("TRACKTOTAL") or tags.get("TOTALTRACKS", "0")
                        )

                    # Disc number
                    disc_raw = tags.get("DISCNUMBER", "1")
                    if "/" in disc_raw:
                        d1, d2 = disc_raw.split("/", 1)
                        info["disc_number"] = max(1, _safe_int(d1, 1))
                        info["total_discs"] = max(1, _safe_int(d2, 1))
                    else:
                        info["disc_number"] = max(1, _safe_int(disc_raw, 1))

                    # Year / Date
                    date_raw = tags.get("DATE") or tags.get("YEAR") or ""
                    if len(date_raw) >= 4 and date_raw[:4].isdigit():
                        info["year"] = int(date_raw[:4])

            if is_last:
                break

    return info


def _safe_int(val: str, default: int = 0) -> int:
    try:
        return int(val.strip())
    except (ValueError, AttributeError):
        return default


def _parse_mp4_atoms(path: Path, info: dict) -> bool:
    """
    Pure-Python MP4/M4A parser for duration, sample_rate (from mdhd) and
    iTunes tags (©nam, ©ART, ©alb, ©gen, ©wrt, ©day, trkn, disk from moov.udta.meta.ilst).
    """
    try:
        file_size = path.stat().st_size
        with path.open("rb") as f:
            def _walk(start: int, end: int, depth: int = 0):
                pos = start
                while pos + 8 <= end:
                    f.seek(pos)
                    hdr = f.read(8)
                    if len(hdr) < 8:
                        break
                    sz, btype = struct.unpack(">I4s", hdr)
                    hdr_len = 8
                    if sz == 1:
                        ext_sz = f.read(8)
                        if len(ext_sz) < 8:
                            break
                        sz = struct.unpack(">Q", ext_sz)[0]
                        hdr_len = 16
                    elif sz == 0:
                        sz = end - pos
                    if sz < hdr_len or pos + sz > end:
                        break

                    body_start = pos + hdr_len
                    body_end = pos + sz

                    if btype in (b"moov", b"trak", b"mdia", b"minf", b"stbl", b"udta"):
                        _walk(body_start, body_end, depth + 1)
                    elif btype == b"meta":
                        # FullBox (4B version/flags) before child boxes
                        _walk(body_start + 4, body_end, depth + 1)
                    elif btype == b"mdhd":
                        f.seek(body_start)
                        mdhd = f.read(min(32, body_end - body_start))
                        if len(mdhd) >= 20:
                            ver = mdhd[0]
                            if ver == 0 and len(mdhd) >= 20:
                                ts, dur = struct.unpack_from(">II", mdhd, 12)
                            elif ver == 1 and len(mdhd) >= 28:
                                ts, dur = struct.unpack_from(">IQ", mdhd, 20)
                            else:
                                ts, dur = 0, 0
                            if ts > 0 and dur > 0:
                                info["sample_rate"] = ts
                                info["duration_ms"] = int((dur * 1000) // ts)
                    elif btype == b"ilst":
                        _parse_ilst(body_start, body_end)
                    pos += sz

            def _parse_ilst(start: int, end: int):
                pos = start
                while pos + 8 <= end:
                    f.seek(pos)
                    hdr = f.read(8)
                    if len(hdr) < 8:
                        break
                    sz, itype = struct.unpack(">I4s", hdr)
                    if sz < 16 or pos + sz > end:
                        break
                    # Look for child 'data' box
                    dpos = pos + 8
                    while dpos + 16 <= pos + sz:
                        f.seek(dpos)
                        dhdr = f.read(16)
                        if len(dhdr) < 16:
                            break
                        dsz, dtype, dflags, _loc = struct.unpack(">I4sII", dhdr)
                        if dsz < 16 or dpos + dsz > pos + sz:
                            break
                        if dtype == b"data":
                            payload = f.read(dsz - 16)
                            if itype in (b"\xa9nam", b"\xa9ART", b"\xa9alb", b"\xa9gen", b"\xa9wrt", b"\xa9day"):
                                txt = payload.decode("utf-8", errors="replace").strip("\x00").strip()
                                if txt:
                                    if itype == b"\xa9nam":
                                        info["title"] = txt
                                    elif itype == b"\xa9ART":
                                        info["artist"] = txt
                                    elif itype == b"\xa9alb":
                                        info["album"] = txt
                                    elif itype == b"\xa9gen":
                                        info["genre"] = txt
                                    elif itype == b"\xa9wrt":
                                        info["composer"] = txt
                                    elif itype == b"\xa9day" and len(txt) >= 4 and txt[:4].isdigit():
                                        info["year"] = int(txt[:4])
                            elif itype == b"trkn" and len(payload) >= 6:
                                tnum, ttot = struct.unpack_from(">HH", payload, 2)
                                if tnum > 0:
                                    info["track_number"] = tnum
                                if ttot > 0:
                                    info["total_tracks"] = ttot
                            elif itype == b"disk" and len(payload) >= 6:
                                dnum, dtot = struct.unpack_from(">HH", payload, 2)
                                if dnum > 0:
                                    info["disc_number"] = dnum
                                if dtot > 0:
                                    info["total_discs"] = dtot
                            elif itype == b"stik" and len(payload) >= 1:
                                if payload[-1] == 2:
                                    info["is_audiobook"] = True
                        dpos += dsz
                    pos += sz

            _walk(0, file_size)
        if path.suffix.lower() == ".m4b":
            info["is_audiobook"] = True
        return True
    except Exception:
        return False


def _parse_id3v2_tags(path: Path, info: dict) -> bool:
    """Pure-Python ID3v2.3 / ID3v2.4 tag reader for .mp3 and .aif files."""
    try:
        with path.open("rb") as f:
            hdr = f.read(10)
            if len(hdr) < 10 or hdr[:3] != b"ID3":
                return False
            ver_major = hdr[3]
            # Synchsafe 28-bit integer size
            tag_size = ((hdr[6] & 0x7F) << 21) | ((hdr[7] & 0x7F) << 14) | ((hdr[8] & 0x7F) << 7) | (hdr[9] & 0x7F)
            tag_data = f.read(min(tag_size, 512 * 1024))

        pos = 0
        limit = len(tag_data)
        while pos + 10 <= limit:
            fid = tag_data[pos:pos + 4]
            if fid == b"\x00\x00\x00\x00" or not all(32 <= b <= 90 for b in fid):
                break
            if ver_major == 4:
                b0, b1, b2, b3 = tag_data[pos + 4:pos + 8]
                fsz = ((b0 & 0x7F) << 21) | ((b1 & 0x7F) << 14) | ((b2 & 0x7F) << 7) | (b3 & 0x7F)
            else:
                fsz = struct.unpack_from(">I", tag_data, pos + 4)[0]
            pos += 10
            if fsz <= 0 or pos + fsz > limit:
                break
            fbody = tag_data[pos:pos + fsz]
            pos += fsz

            if fid in (b"TIT2", b"TPE1", b"TALB", b"TCON", b"TCOM", b"TRCK", b"TPOS", b"TDRC", b"TYER") and len(fbody) > 1:
                enc = fbody[0]
                raw = fbody[1:]
                if enc == 0:
                    txt = raw.decode("latin-1", errors="replace")
                elif enc == 1:
                    txt = raw.decode("utf-16", errors="replace")
                elif enc == 2:
                    txt = raw.decode("utf-16-be", errors="replace")
                else:
                    txt = raw.decode("utf-8", errors="replace")
                txt = txt.split("\x00")[0].strip()
                if not txt:
                    continue
                if fid == b"TIT2":
                    info["title"] = txt
                elif fid == b"TPE1":
                    info["artist"] = txt
                elif fid == b"TALB":
                    info["album"] = txt
                elif fid == b"TCON":
                    info["genre"] = txt
                elif fid == b"TCOM":
                    info["composer"] = txt
                elif fid == b"TRCK":
                    info["track_number"] = _safe_int(txt.split("/")[0], info["track_number"])
                elif fid == b"TPOS":
                    info["disc_number"] = _safe_int(txt.split("/")[0], info["disc_number"])
                elif fid in (b"TDRC", b"TYER") and len(txt) >= 4 and txt[:4].isdigit():
                    info["year"] = int(txt[:4])
        return True
    except Exception:
        return False


def parse_generic_metadata(path: Path) -> dict:
    """
    Parse metadata from non-FLAC files (.aiff, .wav, .mp3, .m4a).
    Uses pure-Python MP4/ID3v2 parsers, mutagen/ffprobe if available, and filename heuristics.
    """
    ext = path.suffix.lower()
    if ext == ".flac":
        return parse_flac_metadata(path)

    # Heuristic fallback from path: .../Artist/Album/01 - Title.ext
    stem = path.stem
    track_num = 0
    title = stem
    parts = stem.split(" ", 1)
    if len(parts) == 2:
        cleaned = parts[0].rstrip(".-_")
        if cleaned.isdigit():
            track_num = int(cleaned)
            title = parts[1].lstrip("-_ ")

    album = path.parent.name if path.parent.name else "Unknown Album"
    artist = path.parent.parent.name if path.parent.parent.name else "Unknown Artist"
    if artist.startswith("smb-share:") or artist in ("gvfs", "1000", "user", "run") or re.match(r"^F\d{2}$", artist):
        artist = "Unknown Artist"
    if album.startswith("smb-share:") or album in ("gvfs", "1000", "user", "run") or re.match(r"^F\d{2}$", album):
        album = "Unknown Album"

    info = {
        "title": title,
        "artist": artist,
        "album": album,
        "genre": "",
        "composer": "",
        "track_number": track_num,
        "total_tracks": 0,
        "disc_number": 1,
        "total_discs": 1,
        "year": 0,
        "duration_ms": 0,
        "sample_rate": 44100,
        "bits_per_sample": 16,
        "channels": 2,
    }

    # 1. Pure-Python native MP4 / ID3v2 parsers (zero external dependencies)
    if ext in (".m4a", ".mp4", ".m4b"):
        _parse_mp4_atoms(path, info)
    elif ext == ".mp3":
        _parse_id3v2_tags(path, info)

    # 2. Try mutagen if installed
    try:
        import mutagen
        mfile = mutagen.File(str(path), easy=True)
        if mfile is not None:
            if getattr(mfile, "info", None) is not None:
                if getattr(mfile.info, "length", 0):
                    info["duration_ms"] = int(mfile.info.length * 1000)
                if getattr(mfile.info, "sample_rate", 0):
                    info["sample_rate"] = int(mfile.info.sample_rate)
            mtags = mfile.tags or {}
            def _mfirst(k: str) -> str:
                v = mtags.get(k)
                if isinstance(v, list):
                    return str(v[0]).strip() if v else ""
                return str(v).strip() if v else ""
            if _mfirst("title"):
                info["title"] = _mfirst("title")
            if _mfirst("artist"):
                info["artist"] = _mfirst("artist")
            if _mfirst("album"):
                info["album"] = _mfirst("album")
            if _mfirst("genre"):
                info["genre"] = _mfirst("genre")
            if _mfirst("composer"):
                info["composer"] = _mfirst("composer")
            if _mfirst("tracknumber"):
                t_raw = _mfirst("tracknumber")
                info["track_number"] = _safe_int(t_raw.split("/")[0], track_num)
            if _mfirst("date"):
                d_raw = _mfirst("date")
                if len(d_raw) >= 4 and d_raw[:4].isdigit():
                    info["year"] = int(d_raw[:4])
    except Exception:
        pass

    # Try ffprobe if installed
    if shutil.which("ffprobe"):
        try:
            cmd = [
                "ffprobe",
                "-v", "quiet",
                "-print_format", "json",
                "-show_format",
                "-show_streams",
                str(path),
            ]
            res = subprocess.run(cmd, capture_output=True, text=True, check=True)
            data = json.loads(res.stdout)
            fmt = data.get("format", {})
            if "duration" in fmt:
                info["duration_ms"] = int(float(fmt["duration"]) * 1000)
            tags = {k.upper(): str(v) for k, v in fmt.get("tags", {}).items()}
            if tags.get("TITLE"):
                info["title"] = tags["TITLE"]
            if tags.get("ARTIST"):
                info["artist"] = tags["ARTIST"]
            if tags.get("ALBUM"):
                info["album"] = tags["ALBUM"]
            if tags.get("GENRE"):
                info["genre"] = tags["GENRE"]
            if tags.get("TRACK"):
                t_raw = tags["TRACK"]
                if "/" in t_raw:
                    p1, p2 = t_raw.split("/", 1)
                    info["track_number"] = _safe_int(p1, track_num)
                    info["total_tracks"] = _safe_int(p2, 0)
                else:
                    info["track_number"] = _safe_int(t_raw, track_num)
            for stream in data.get("streams", []):
                if stream.get("codec_type") == "audio":
                    if "sample_rate" in stream:
                        info["sample_rate"] = int(stream["sample_rate"])
                    break
        except Exception:
            pass

    # If duration still 0 for AIFF/WAV, estimate from file size
    if info["duration_ms"] == 0:
        sz = path.stat().st_size
        if ext in (".aiff", ".aif", ".wav"):
            # ~176,400 bytes/sec for 16-bit 44.1kHz stereo
            info["duration_ms"] = max(1000, int((sz / 176400.0) * 1000))
        else:
            # Estimate ~192 kbps
            info["duration_ms"] = max(1000, int((sz * 8) / 192))

    return info


# =====================================================================
# 2. Fast FLAC -> 16-bit/44.1kHz AIFF Decoder (RAM-Buffered)
# =====================================================================

def convert_flac_to_aiff(flac_path: Path, dest_aiff_path: Path, meta: dict) -> None:
    """
    Decodes a FLAC file to standard 16-bit, 44.1kHz (or 48kHz) big-endian AIFF
    compatible with the 3rd Gen iPod Wolfson WM8731 DAC.
    Uses RAM (/dev/shm) as staging before writing sequentially to the iPod.
    """
    target_sr = meta.get("sample_rate", 44100)
    if target_sr not in (44100, 48000):
        target_sr = 44100

    shm_dir = Path("/dev/shm") if (sys.platform != "win32" and Path("/dev/shm").is_dir()) else Path(tempfile.gettempdir())
    with tempfile.NamedTemporaryFile(dir=shm_dir, suffix=".aif", delete=False) as tmp:
        tmp_path = Path(tmp.name)

    try:
        if shutil.which("ffmpeg"):
            cmd = [
                "ffmpeg", "-y", "-v", "error",
                "-i", str(flac_path),
                "-map", "0:a:0",          # Audio stream only (strip embedded cover art that bloats 3G monochrome iPods)
                "-ar", str(target_sr),
                "-ac", "2",
                "-c:a", "pcm_s16be",
                "-write_id3v2", "1",
                str(tmp_path),
            ]
            subprocess.run(cmd, check=True)
        elif shutil.which("gst-launch-1.0"):
            # Fallback to GStreamer if ffmpeg isn't installed yet
            # Wait: GStreamer doesn't always have aiffmux in base plugins, so if aiffmux fails, write WAV or raw PCM wrapped in AIFF header!
            _decode_flac_via_gstreamer_to_aiff(flac_path, tmp_path, target_sr)
        elif shutil.which("flac"):
            cmd = [
                "flac", "-d", "-f", "--totally-silent",
                "--force-aiff-format",
                "-o", str(tmp_path),
                str(flac_path),
            ]
            subprocess.run(cmd, check=True)
        else:
            raise RuntimeError(
                "No FLAC decoder found! Please install ffmpeg (`sudo apt install ffmpeg`) or flac."
            )

        dest_aiff_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tmp_path, dest_aiff_path)
    finally:
        tmp_path.unlink(missing_ok=True)


def _decode_flac_via_gstreamer_to_aiff(flac_path: Path, out_aiff: Path, sample_rate: int) -> None:
    """
    Fallback decoder using gst-launch-1.0 (which is pre-installed on standard Ubuntu/Linux desktops)
    to decode FLAC to raw 16-bit big-endian stereo PCM and wrap in an AIFF FORM container.
    """
    with tempfile.NamedTemporaryFile(dir=out_aiff.parent, suffix=".raw", delete=False) as raw_tmp:
        raw_path = Path(raw_tmp.name)

    try:
        cmd = [
            "gst-launch-1.0", "-q",
            "filesrc", f"location={flac_path}",
            "!", "flacparse", "!", "flacdec",
            "!", "audioconvert", "!", "audioresample",
            "!", f"audio/x-raw,format=S16BE,channels=2,rate={sample_rate}",
            "!", "filesink", f"location={raw_path}",
        ]
        subprocess.run(cmd, check=True)
        pcm_size = raw_path.stat().st_size
        num_frames = pcm_size // 4  # 2 channels * 2 bytes

        # Construct standard 54-byte AIFF header
        # COMM chunk (18 bytes data): channels=2, numSampleFrames, sampleSize=16, sampleRate (80-bit IEEE 754 extended)
        sr_ext = _int_to_ieee754_extended(sample_rate)
        comm_chunk = b"COMM" + struct.pack(">IhIh", 18, 2, num_frames, 16) + sr_ext
        ssnd_header = b"SSND" + struct.pack(">III", pcm_size + 8, 0, 0)
        form_size = 4 + len(comm_chunk) + len(ssnd_header) + pcm_size
        aiff_header = b"FORM" + struct.pack(">I", form_size) + b"AIFF" + comm_chunk + ssnd_header

        with out_aiff.open("wb") as out_f, raw_path.open("rb") as in_f:
            out_f.write(aiff_header)
            shutil.copyfileobj(in_f, out_f, length=1024 * 1024)
    finally:
        raw_path.unlink(missing_ok=True)


def _int_to_ieee754_extended(val: int) -> bytes:
    """Convert integer sample rate (e.g. 44100) to 80-bit big-endian IEEE 754 extended float for AIFF COMM chunk."""
    if val <= 0:
        return b"\x00" * 10
    exp = 16383 + 31
    mant = val
    while (mant & 0x80000000) == 0:
        mant <<= 1
        exp -= 1
    return struct.pack(">HII", exp, mant, 0)


# =====================================================================
# 2B. Fast FLAC / AIFF -> 16-bit/44.1kHz Apple Lossless (ALAC .m4a)
# =====================================================================

_LIBALAC_HANDLE = None


def _get_libalac():
    """Load (or auto-compile from ./alac_codec) the Apple open-source ALAC encoder shared library."""
    global _LIBALAC_HANDLE
    if _LIBALAC_HANDLE is not None:
        return _LIBALAC_HANDLE

    import ctypes
    here = Path(__file__).resolve().parent
    ext = ".dll" if sys.platform == "win32" else (".dylib" if sys.platform == "darwin" else ".so")
    so_path = here / f"libalac{ext}"
    if not so_path.is_file():
        so_path = here / "libalac.so"
    codec_dir = here / "alac_codec"
    bridge_cpp = here / "alac_c_bridge.cpp"

    if not so_path.is_file() and codec_dir.is_dir() and bridge_cpp.is_file() and shutil.which("g++"):
        try:
            cmd = [
                "g++", "-O3", "-fPIC", "-shared",
                "-I", str(codec_dir),
                str(bridge_cpp),
                str(codec_dir / "EndianPortable.c"),
                str(codec_dir / "ALACBitUtilities.c"),
                str(codec_dir / "ALACEncoder.cpp"),
                str(codec_dir / "ALACDecoder.cpp"),
                str(codec_dir / "ag_enc.c"),
                str(codec_dir / "ag_dec.c"),
                str(codec_dir / "dp_enc.c"),
                str(codec_dir / "dp_dec.c"),
                str(codec_dir / "matrix_enc.c"),
                str(codec_dir / "matrix_dec.c"),
                "-o", str(so_path),
            ]
            subprocess.run(cmd, check=True)
        except Exception:
            pass

    if so_path.is_file():
        try:
            lib = ctypes.CDLL(str(so_path))
            lib.alac_encode_pcm16.argtypes = [
                ctypes.c_void_p, ctypes.c_uint32, ctypes.c_uint32, ctypes.c_uint32,
                ctypes.c_void_p, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_uint32,
                ctypes.POINTER(ctypes.c_uint32), ctypes.c_void_p,
            ]
            lib.alac_encode_pcm16.restype = ctypes.c_int32
            _LIBALAC_HANDLE = lib
            return lib
        except Exception:
            pass
    return None


def _mp4_box(box_type: bytes, payload: bytes) -> bytes:
    return struct.pack(">I4s", 8 + len(payload), box_type) + payload


def _mp4_full_box(box_type: bytes, version: int, flags: int, payload: bytes) -> bytes:
    vf = ((version & 0xFF) << 24) | (flags & 0xFFFFFF)
    return _mp4_box(box_type, struct.pack(">I", vf) + payload)


def _build_mp4_udta_ilst(meta: dict) -> bytes:
    """Build Apple iTunes udta.meta.ilst metadata atoms (no cover art, 3G safe)."""
    def _text_atom(atom_4cc: bytes, text: str) -> bytes:
        if not text:
            return b""
        raw = str(text).encode("utf-8")
        return _mp4_box(atom_4cc, _mp4_box(b"data", struct.pack(">II", 1, 0) + raw))

    def _trkn_atom(num: int, total: int = 0) -> bytes:
        return _mp4_box(
            b"trkn",
            _mp4_box(b"data", struct.pack(">IIHHHH", 0, 0, 0, max(0, int(num)), max(0, int(total)), 0)),
        )

    def _disk_atom(num: int, total: int = 1) -> bytes:
        return _mp4_box(
            b"disk",
            _mp4_box(b"data", struct.pack(">IIHHH", 0, 0, 0, max(1, int(num)), max(1, int(total)))),
        )

    items = bytearray()
    if meta.get("title"):
        items += _text_atom(b"\xa9nam", meta["title"])
    if meta.get("artist"):
        items += _text_atom(b"\xa9ART", meta["artist"])
    if meta.get("composer"):
        items += _text_atom(b"\xa9wrt", meta["composer"])
    if meta.get("album"):
        items += _text_atom(b"\xa9alb", meta["album"])
    if meta.get("genre"):
        items += _text_atom(b"\xa9gen", meta["genre"])
    if meta.get("track_number"):
        items += _trkn_atom(meta["track_number"], meta.get("total_tracks") or 0)
    if meta.get("disc_number"):
        items += _disk_atom(meta["disc_number"], meta.get("total_discs") or 1)
    if meta.get("year"):
        items += _text_atom(b"\xa9day", str(meta["year"]))
    if meta.get("is_audiobook") or str(meta.get("genre", "")).lower() == "audiobook" or str(meta.get("filetype_code", "")).strip() == "M4B":
        # stik: 2 = Audiobook (triggers iPod Audiobook menu & bookmarking)
        items += _mp4_box(b"stik", _mp4_box(b"data", struct.pack(">IIB", 21, 0, 2)))
        items += _mp4_box(b"pgap", _mp4_box(b"data", struct.pack(">IIB", 21, 0, 1)))  # gapless
        items += _mp4_box(b"shfl", _mp4_box(b"data", struct.pack(">IIB", 21, 0, 1)))  # skip when shuffling
        items += _mp4_box(b"bkmk", _mp4_box(b"data", struct.pack(">IIB", 21, 0, 1)))  # remember playback position

    ilst = _mp4_box(b"ilst", bytes(items))
    meta_hdlr = _mp4_full_box(b"hdlr", 0, 0, b"\x00\x00\x00\x00mdirappl" + b"\x00" * 9 + b"\xd4")
    meta_box = _mp4_full_box(b"meta", 0, 0, meta_hdlr + ilst)
    return _mp4_box(b"udta", meta_box)


def _mux_alac_m4a(
    packets_blob: bytes,
    packet_sizes: List[int],
    cookie_24: bytes,
    total_frames: int,
    sample_rate: int = 44100,
    channels: int = 2,
    meta: Optional[dict] = None,
) -> bytes:
    """
    Mux encoded ALAC packets into an Apple iTunes-compliant faststart .m4a container:
      - 5 packets per chunk in stsc/stco (matching iTunes ALAC muxing for PortalPlayer DMA)
      - Populated maxFrameBytes and avgBitRate in the 24-byte ALAC magic cookie
      - 4096-byte (4 KB sector) alignment for mdat audio data (stco[0]) via a free atom
    """
    ftyp = _mp4_box(
        b"ftyp",
        b"M4A " + struct.pack(">I", 0) + b"M4A " + b"mp42" + b"isom" + b"\x00\x00\x00\x00",
    )

    num_packets = len(packet_sizes)
    max_frame_bytes = max(packet_sizes) if packet_sizes else 0
    avg_bitrate = (
        int(((len(packets_blob) * 8.0) / num_packets) * (sample_rate / 4096.0))
        if num_packets > 0
        else 0
    )

    # Ensure bytes 12..20 of the 24-byte ALAC cookie contain accurate maxFrameBytes and avgBitRate
    patched_cookie = (
        cookie_24[:12]
        + struct.pack(">II", max_frame_bytes, avg_bitrate)
        + cookie_24[20:24]
    )

    alac_config_box = _mp4_full_box(b"alac", 0, 0, patched_cookie)
    sample_entry_payload = (
        b"\x00" * 6
        + struct.pack(">H", 1)
        + b"\x00" * 8
        + struct.pack(">HH", channels, 16)
        + b"\x00" * 4
        + struct.pack(">I", (sample_rate & 0xFFFF) << 16)
        + alac_config_box
    )
    alac_sample_entry = _mp4_box(b"alac", sample_entry_payload)
    stsd = _mp4_full_box(b"stsd", 0, 0, struct.pack(">I", 1) + alac_sample_entry)

    if num_packets == 0:
        stts_entries = b""
        stts_count = 0
    elif num_packets == 1:
        stts_entries = struct.pack(">II", 1, total_frames)
        stts_count = 1
    else:
        last_frames = total_frames - 4096 * (num_packets - 1)
        if last_frames == 4096:
            stts_entries = struct.pack(">II", num_packets, 4096)
            stts_count = 1
        else:
            stts_entries = struct.pack(">IIII", num_packets - 1, 4096, 1, last_frames)
            stts_count = 2
    stts = _mp4_full_box(b"stts", 0, 0, struct.pack(">I", stts_count) + stts_entries)

    # Group 5 ALAC packets per chunk in stsc/stco (exact Apple iTunes layout)
    SAMPLES_PER_CHUNK = 5
    if num_packets == 0:
        stsc_payload = struct.pack(">I", 0)
        chunk_first_pkt_indices: List[int] = []
    elif num_packets <= SAMPLES_PER_CHUNK:
        stsc_payload = struct.pack(">IIII", 1, 1, num_packets, 1)
        chunk_first_pkt_indices = [0]
    else:
        full_chunks = num_packets // SAMPLES_PER_CHUNK
        rem_pkts = num_packets % SAMPLES_PER_CHUNK
        chunk_first_pkt_indices = list(range(0, num_packets, SAMPLES_PER_CHUNK))
        if rem_pkts == 0:
            stsc_payload = struct.pack(">IIII", 1, 1, SAMPLES_PER_CHUNK, 1)
        else:
            stsc_payload = struct.pack(
                ">IIIIIII",
                2,
                1, SAMPLES_PER_CHUNK, 1,
                full_chunks + 1, rem_pkts, 1,
            )
    stsc = _mp4_full_box(b"stsc", 0, 0, stsc_payload)

    stsz_payload = struct.pack(">II", 0, num_packets) + struct.pack(f">{num_packets}I", *packet_sizes)
    stsz = _mp4_full_box(b"stsz", 0, 0, stsz_payload)
    udta = _build_mp4_udta_ilst(meta or {})

    mac_now = int(time.time()) + MAC_EPOCH_OFFSET

    def _build_moov(mdat_data_offset: int) -> bytes:
        pkt_offsets = []
        cur = mdat_data_offset
        for sz in packet_sizes:
            pkt_offsets.append(cur)
            cur += sz
        chunk_offsets = [pkt_offsets[i] for i in chunk_first_pkt_indices]
        num_chunks = len(chunk_offsets)
        stco_payload = struct.pack(">I", num_chunks) + struct.pack(f">{num_chunks}I", *chunk_offsets)
        stco = _mp4_full_box(b"stco", 0, 0, stco_payload)

        stbl = _mp4_box(b"stbl", stsd + stts + stsc + stsz + stco)
        smhd = _mp4_full_box(b"smhd", 0, 0, struct.pack(">HH", 0, 0))
        url_box = _mp4_full_box(b"url ", 0, 1, b"")
        dref = _mp4_full_box(b"dref", 0, 0, struct.pack(">I", 1) + url_box)
        dinf = _mp4_box(b"dinf", dref)
        minf = _mp4_box(b"minf", smhd + dinf + stbl)

        mdhd = _mp4_full_box(
            b"mdhd",
            0,
            0,
            struct.pack(">IIIIHH", mac_now, mac_now, sample_rate, total_frames, 0x55C4, 0),
        )
        hdlr = _mp4_full_box(
            b"hdlr",
            0,
            0,
            b"\x00\x00\x00\x00soun" + b"\x00" * 14,
        )
        mdia = _mp4_box(b"mdia", mdhd + hdlr + minf)

        tkhd_payload = (
            struct.pack(">IIIII", mac_now, mac_now, 1, 0, total_frames)
            + b"\x00" * 8
            + struct.pack(">HHHH", 0, 0, 0x0100, 0)
            + struct.pack(">9I", 0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000)
            + struct.pack(">II", 0, 0)
        )
        tkhd = _mp4_full_box(b"tkhd", 0, 7, tkhd_payload)
        trak = _mp4_box(b"trak", tkhd + mdia)

        mvhd_payload = (
            struct.pack(">IIII", mac_now, mac_now, sample_rate, total_frames)
            + struct.pack(">IH", 0x00010000, 0x0100)
            + b"\x00" * 10
            + struct.pack(">9I", 0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000)
            + b"\x00" * 24
            + struct.pack(">I", 2)
        )
        mvhd = _mp4_full_box(b"mvhd", 0, 0, mvhd_payload)
        return _mp4_box(b"moov", mvhd + trak + udta)

    dummy_moov = _build_moov(0)
    # Pad with a `free` atom so mdat_data_offset (stco[0]) is aligned to a 4096-byte (4 KB) boundary
    min_mdat_data_offset = len(ftyp) + len(dummy_moov) + 8 + 8
    mdat_data_offset = ((min_mdat_data_offset + 4095) // 4096) * 4096
    free_box_size = mdat_data_offset - 8 - len(ftyp) - len(dummy_moov)
    free_box = _mp4_box(b"free", b"\x00" * (free_box_size - 8))

    real_moov = _build_moov(mdat_data_offset)
    mdat = _mp4_box(b"mdat", packets_blob)
    return ftyp + real_moov + free_box + mdat


def _encode_s16le_pcm_to_alac_m4a(pcm_bytes: bytes, dest_m4a_path: Path, sample_rate: int, meta: dict) -> int:
    """Encode raw S16LE stereo PCM bytes into an Apple Lossless .m4a file and return bitrate in kbps."""
    import ctypes

    libalac = _get_libalac()
    num_frames = len(pcm_bytes) // 4  # 2 channels * 2 bytes
    max_packets = (num_frames // 4096) + 2
    max_out = len(pcm_bytes) + 65536
    out_buf = ctypes.create_string_buffer(max_out)
    pkt_sizes = (ctypes.c_uint32 * max_packets)()
    num_pkts = ctypes.c_uint32(0)
    cookie = ctypes.create_string_buffer(24)

    comp_bytes = libalac.alac_encode_pcm16(
        pcm_bytes,
        num_frames,
        sample_rate,
        2,
        out_buf,
        max_out,
        pkt_sizes,
        max_packets,
        ctypes.byref(num_pkts),
        cookie,
    )
    if comp_bytes <= 0:
        raise RuntimeError(f"ALAC encoding failed with error code {comp_bytes}")

    m4a_bytes = _mux_alac_m4a(
        out_buf.raw[:comp_bytes],
        [int(pkt_sizes[i]) for i in range(num_pkts.value)],
        cookie.raw,
        num_frames,
        sample_rate=sample_rate,
        channels=2,
        meta=meta,
    )
    dest_m4a_path.parent.mkdir(parents=True, exist_ok=True)
    dest_m4a_path.write_bytes(m4a_bytes)

    duration_sec = max(0.1, num_frames / float(sample_rate))
    bitrate_kbps = max(128, int((len(m4a_bytes) * 8) / (duration_sec * 1000)))
    return bitrate_kbps


def convert_flac_to_alac(flac_path: Path, dest_m4a_path: Path, meta: dict) -> int:
    """
    Convert a FLAC file to 16-bit, 44.1kHz (or 48kHz) stereo Apple Lossless (.m4a)
    compatible with 3rd Gen iPod Firmware 2.2/2.3.
    Uses native libalac if available, with universal FFmpeg fallback.
    Returns the compressed bitrate in kbps.
    """
    target_sr = meta.get("sample_rate", 44100)
    if target_sr not in (44100, 48000):
        target_sr = 44100

    if _get_libalac() is not None:
        shm_dir = Path("/dev/shm") if (sys.platform != "win32" and Path("/dev/shm").is_dir()) else Path(tempfile.gettempdir())
        with tempfile.NamedTemporaryFile(dir=shm_dir, suffix=".raw", delete=False) as raw_tmp:
            raw_path = Path(raw_tmp.name)

        try:
            if shutil.which("gst-launch-1.0"):
                cmd = [
                    "gst-launch-1.0", "-q",
                    "filesrc", f"location={flac_path}",
                    "!", "flacparse", "!", "flacdec",
                    "!", "audioconvert", "!", "audioresample",
                    "!", f"audio/x-raw,format=S16LE,channels=2,rate={target_sr}",
                    "!", "filesink", f"location={raw_path}",
                ]
                subprocess.run(cmd, check=True)
            elif shutil.which("ffmpeg"):
                cmd = [
                    "ffmpeg", "-y", "-v", "error",
                    "-i", str(flac_path),
                    "-f", "s16le", "-acodec", "pcm_s16le",
                    "-ar", str(target_sr), "-ac", "2",
                    str(raw_path),
                ]
                subprocess.run(cmd, check=True)
            else:
                raise RuntimeError("Neither gst-launch-1.0 nor ffmpeg found for FLAC decoding.")

            pcm_bytes = raw_path.read_bytes()
        finally:
            raw_path.unlink(missing_ok=True)

        with tempfile.NamedTemporaryFile(dir=shm_dir, suffix=".m4a", delete=False) as m4a_tmp:
            tmp_m4a = Path(m4a_tmp.name)
        try:
            bitrate_kbps = _encode_s16le_pcm_to_alac_m4a(pcm_bytes, tmp_m4a, target_sr, meta)
            dest_m4a_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(tmp_m4a, dest_m4a_path)
            return bitrate_kbps
        finally:
            tmp_m4a.unlink(missing_ok=True)

    # Universal cross-platform fallback via FFmpeg with +faststart
    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("ffmpeg binary not found. Please install ffmpeg to convert FLAC -> ALAC.")
    dest_m4a_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        ff, "-y", "-v", "error",
        "-i", str(flac_path),
        "-c:a", "alac",
        "-ar", str(target_sr),
        "-ac", "2",
        "-movflags", "+faststart",
        str(dest_m4a_path),
    ]
    subprocess.run(cmd, check=True)
    size = dest_m4a_path.stat().st_size
    dur_sec = meta.get("duration_ms", 1000) / 1000.0
    return max(64, int((size * 8) / (dur_sec * 1000))) if dur_sec > 0 else 700


def _extract_aiff_s16le_pcm(aiff_path: Path) -> Tuple[bytes, int]:
    """
    Parse an uncompressed AIFF (.aif/.aiff) FORM container directly in Python,
    extract the big-endian 16-bit PCM (SSND chunk), and byte-swap to S16LE.
    Returns (s16le_pcm_bytes, sample_rate).
    """
    import array

    data = aiff_path.read_bytes()
    if len(data) < 54 or data[:4] != b"FORM" or data[8:12] not in (b"AIFF", b"AIFC"):
        raise ValueError(f"Not a valid AIFF file: {aiff_path}")

    pos = 12
    end = len(data)
    sample_rate = 44100
    channels = 2
    sample_size = 16
    pcm_be = b""

    while pos + 8 <= end:
        cid = data[pos:pos + 4]
        csize = struct.unpack(">I", data[pos + 4:pos + 8])[0]
        body_start = pos + 8
        body_end = min(end, body_start + csize)

        if cid == b"COMM" and (body_end - body_start) >= 18:
            channels, _num_frames, sample_size = struct.unpack(
                ">hIh", data[body_start:body_start + 8]
            )
            exp = struct.unpack(">H", data[body_start + 8:body_start + 10])[0] & 0x7FFF
            mant = struct.unpack(">Q", data[body_start + 10:body_start + 18])[0]
            if exp > 0 and mant > 0:
                sr = int(round(mant * (2.0 ** (exp - 16383 - 63))))
                if sr in (44100, 48000):
                    sample_rate = sr
        elif cid == b"SSND" and (body_end - body_start) >= 8:
            ssnd_offset, _blocksize = struct.unpack(">II", data[body_start:body_start + 8])
            pcm_start = body_start + 8 + ssnd_offset
            if pcm_start < body_end:
                pcm_be = data[pcm_start:body_end]

        pos = body_start + csize + (csize & 1)

    if not pcm_be:
        raise ValueError(f"No SSND audio data found in AIFF file: {aiff_path}")
    if sample_size != 16:
        raise ValueError(f"Unsupported AIFF bit depth ({sample_size}-bit) in {aiff_path}")

    # Ensure even byte length for 16-bit samples
    if len(pcm_be) & 1:
        pcm_be = pcm_be[:-1]

    arr = array.array("h")
    arr.frombytes(pcm_be)
    if sys.byteorder == "little":
        arr.byteswap()

    if channels == 1:
        # Up-mix mono to stereo
        stereo = array.array("h", [0] * (len(arr) * 2))
        stereo[0::2] = arr
        stereo[1::2] = arr
        arr = stereo

    raw_bytes = arr.tobytes()
    # Ensure whole 4-byte stereo frames
    rem = len(raw_bytes) % 4
    if rem:
        raw_bytes = raw_bytes[:-rem]
    return raw_bytes, sample_rate


def convert_aiff_to_alac(aiff_path: Path, dest_m4a_path: Path, meta: dict) -> int:
    """
    Convert an uncompressed AIFF (.aif/.aiff) file to 16-bit stereo Apple Lossless (.m4a).
    Uses native libalac if available, with universal FFmpeg fallback.
    Returns the compressed bitrate in kbps.
    """
    target_sr = meta.get("sample_rate", 44100)
    if target_sr not in (44100, 48000):
        target_sr = 44100

    if _get_libalac() is not None:
        pcm_bytes, detected_sr = _extract_aiff_s16le_pcm(aiff_path)
        if detected_sr in (44100, 48000):
            target_sr = detected_sr
        shm_dir = Path("/dev/shm") if (sys.platform != "win32" and Path("/dev/shm").is_dir()) else Path(tempfile.gettempdir())
        with tempfile.NamedTemporaryFile(dir=shm_dir, suffix=".m4a", delete=False) as m4a_tmp:
            tmp_m4a = Path(m4a_tmp.name)
        try:
            bitrate_kbps = _encode_s16le_pcm_to_alac_m4a(pcm_bytes, tmp_m4a, target_sr, meta)
            dest_m4a_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(tmp_m4a, dest_m4a_path)
            return bitrate_kbps
        finally:
            tmp_m4a.unlink(missing_ok=True)

    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("ffmpeg binary not found. Please install ffmpeg to convert AIFF -> ALAC.")
    dest_m4a_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        ff, "-y", "-v", "error",
        "-i", str(aiff_path),
        "-c:a", "alac",
        "-ar", str(target_sr),
        "-ac", "2",
        "-movflags", "+faststart",
        str(dest_m4a_path),
    ]
    subprocess.run(cmd, check=True)
    size = dest_m4a_path.stat().st_size
    dur_sec = meta.get("duration_ms", 1000) / 1000.0
    return max(64, int((size * 8) / (dur_sec * 1000))) if dur_sec > 0 else 700


# =====================================================================
# 3. 3rd Gen iPod iTunesDB Binary Writer (Exact flashpod byte layout)
# =====================================================================

MARKER_MP3 = b"\x00MP3"


def find_ffmpeg() -> Optional[str]:
    """Locate ffmpeg binary across Linux, macOS, and Windows."""
    # 1. System PATH
    found = shutil.which("ffmpeg")
    if found:
        return found
    if sys.platform == "win32":
        found_win = shutil.which("ffmpeg.exe")
        if found_win:
            return found_win

    # 2. Local bin / script directory / user home
    script_dir = Path(__file__).resolve().parent
    candidates = [
        script_dir / "ffmpeg",
        script_dir / "ffmpeg.exe",
        Path.home() / ".local" / "bin" / "ffmpeg",
        Path.home() / "bin" / "ffmpeg",
    ]

    # macOS Homebrew / MacPorts
    if sys.platform == "darwin":
        candidates.extend([
            Path("/opt/homebrew/bin/ffmpeg"),
            Path("/usr/local/bin/ffmpeg"),
            Path("/opt/local/bin/ffmpeg"),
        ])
    # Windows common install paths
    elif sys.platform == "win32":
        candidates.extend([
            Path("C:/ffmpeg/bin/ffmpeg.exe"),
            Path("C:/Program Files/ffmpeg/bin/ffmpeg.exe"),
            Path.home() / "AppData" / "Local" / "Microsoft" / "WinGet" / "Links" / "ffmpeg.exe",
            Path.home() / "scoop" / "shims" / "ffmpeg.exe",
        ])

    for cand in candidates:
        if cand.is_file() and (sys.platform == "win32" or os.access(cand, os.X_OK)):
            return str(cand)
    return None


def convert_audio_to_aac_m4b(
    src_file: Path,
    dest_file: Path,
    meta: dict,
    bitrate_kbps: int = 160,
) -> int:
    """
    Transcode an audio file (e.g. MP3) into an iPod-compatible AAC .m4b audiobook file
    with +faststart, brand M4B, disabled PNS/TNS (preventing high-frequency hardware decoder noise),
    and metadata atoms.
    """
    ff = find_ffmpeg()
    if not ff:
        raise RuntimeError("ffmpeg binary not found. Please install ffmpeg to transcode to AAC .m4b.")

    shm_dir = Path("/dev/shm") if (sys.platform != "win32" and Path("/dev/shm").is_dir()) else Path(tempfile.gettempdir())
    with tempfile.NamedTemporaryFile(dir=shm_dir, suffix=".m4b", delete=False) as tmp_f:
        tmp_m4b = Path(tmp_f.name)

    try:
        cmd = [
            ff,
            "-y",
            "-i", str(src_file),
            "-c:a", "aac",
            "-b:a", f"{bitrate_kbps}k",
            "-ar", "44100",
            "-ac", "2",
            "-aac_pns", "0",
            "-aac_tns", "0",
            "-cutoff", "18000",
            "-brand", "M4B ",
            "-movflags", "+faststart",
            "-metadata", f"title={meta.get('title', '')}",
            "-metadata", f"artist={meta.get('artist', '')}",
            "-metadata", f"album={meta.get('album', '')}",
            "-metadata", f"genre=Audiobook",
            "-metadata", "media_type=2",
        ]
        if meta.get("track_number"):
            trkn = str(meta["track_number"])
            if meta.get("total_tracks"):
                trkn += f"/{meta['total_tracks']}"
            cmd.extend(["-metadata", f"track={trkn}"])
        cmd.append(str(tmp_m4b))

        subprocess.run(cmd, check=True, capture_output=True)
        shutil.copyfile(tmp_m4b, dest_file)
        return bitrate_kbps
    finally:
        tmp_m4b.unlink(missing_ok=True)


def _pack_mhod_string(mhod_type: int, text: str) -> bytes:
    """Pack a UTF-16LE string into an iTunesDB mhod record (flashpod layout)."""
    data = text.encode("utf-16-le")
    body = struct.pack("<IIII", 1, len(data), 0, 0) + data
    return (
        b"mhod"
        + struct.pack("<III", 24, 24 + 16 + len(data), mhod_type)
        + struct.pack("<II", 0, 0)
        + body
    )


def _pack_mhod_playlist_order(position: int) -> bytes:
    """Pack a type-100 playlist position mhod attached to an mhip record."""
    return (
        b"mhod"
        + struct.pack("<III", 24, 24 + 20, 100)
        + struct.pack("<II", 0, 0)
        + struct.pack("<IIIII", position, 0, 0, 0, 0)
    )


def _pack_mhit(track: TrackMetadata, db_version: int = 0x0B) -> bytes:
    """Pack a single TrackMetadata into a 156-byte mhit record + child mhod records (exact flashpod layout)."""
    mhods: List[bytes] = []
    ext = Path(track.ipod_rel_path.replace(":", "/")).suffix.lower()
    is_m4b = (
        ext == ".m4b"
        or (ext == ".m4a" and (track.filetype_code.strip() == "M4B" or (track.genre and track.genre.lower() == "audiobook")))
    )
    if is_m4b:
        filetype_desc = "AAC audio book"
    elif ext in (".aif", ".aiff"):
        filetype_desc = "AIFF Audio File"
    elif ext == ".wav":
        filetype_desc = "WAV Audio File"
    elif ext == ".m4a":
        filetype_desc = "AAC audio file"
    else:
        filetype_desc = track.filetype_desc if track.filetype_desc else "MPEG audio file"

    fields = (
        (1, track.title or "Untitled"),
        (2, track.ipod_rel_path),
        (3, track.album or "Unknown Album"),
        (4, track.artist or "Unknown Artist"),
        (5, track.genre),
        (6, filetype_desc),
        (12, track.composer),
    )
    for typ, val in fields:
        if val:
            mhods.append(_pack_mhod_string(typ, val))

    mhod_blob = b"".join(mhods)
    header_len = 156  # iTunes-4.x-era mhit header used by flashpod
    hfs_time = (int(track.date_added) + MAC_EPOCH_OFFSET) & 0xFFFFFFFF

    hdr = bytearray(header_len)
    hdr[0:4] = b"mhit"
    struct.pack_into("<III", hdr, 4, header_len, header_len + len(mhod_blob), len(mhods))
    struct.pack_into("<II", hdr, 16, track.track_id, 1)  # id, visible=1
    hdr[24:28] = b"M4B " if is_m4b else MARKER_MP3       # marker
    struct.pack_into("<I", hdr, 32, hfs_time)            # time modified
    struct.pack_into("<III", hdr, 36, track.file_size, track.duration_ms, track.track_number)
    struct.pack_into("<II", hdr, 52, track.year, track.bitrate_kbps)
    struct.pack_into("<I", hdr, 60, (track.sample_rate & 0xFFFF) << 16)
    struct.pack_into("<I", hdr, 88, hfs_time)            # time added (offset 88!)
    struct.pack_into("<Q", hdr, 96, track.dbid)          # 64-bit dbid (offset 96!)
    hdr[104] = 1                                         # checked = 1 (offset 104!)

    return bytes(hdr) + mhod_blob


def _pack_mhyp(name: str, tracks: List[TrackMetadata], is_master: bool, playlist_id: int) -> bytes:
    """Pack a playlist (mhyp) containing the given tracks (exact flashpod layout)."""
    title_mhod = _pack_mhod_string(1, name)
    items = bytearray()
    hfs_now = (int(time.time()) + MAC_EPOCH_OFFSET) & 0xFFFFFFFF

    for pos, trk in enumerate(tracks, start=1):
        pos_mhod = _pack_mhod_playlist_order(pos)
        item = b"mhip" + struct.pack(
            "<IIIIIII",
            76,
            76 + len(pos_mhod),
            1,
            0,
            pos,
            trk.track_id,
            hfs_now,
        )
        item += bytes(76 - len(item)) + pos_mhod
        items.extend(item)

    header_len = 108
    hdr = bytearray(header_len)
    hdr[0:4] = b"mhyp"
    struct.pack_into(
        "<IIII",
        hdr,
        4,
        header_len,
        header_len + len(title_mhod) + len(items),
        1,
        len(tracks),
    )
    struct.pack_into("<I", hdr, 20, 1 if is_master else 0)
    struct.pack_into("<I", hdr, 24, hfs_now)
    struct.pack_into("<Q", hdr, 28, playlist_id)

    return bytes(hdr) + title_mhod + bytes(items)


def build_itunesdb_bytes(
    tracks: List[TrackMetadata],
    playlists: Optional[Dict[str, List[TrackMetadata]]] = None,
    db_version: int = 0x0B,
) -> bytes:
    """
    Build a complete binary iTunesDB file using flashpod's exact byte layout for 1G-4G iPods.
    """
    import secrets

    # Assign strictly sequential track_ids (52, 53, 54...) in exact mhlt/mhyp order,
    # matching flashpod.itunesdb.Library.next_track_id() and clean_and_slice.py.
    ordered_tracks = list(tracks)
    now_unix = int(time.time())
    for idx, t in enumerate(ordered_tracks, start=52):
        t.track_id = idx
        t.dbid = secrets.randbits(64)
        t.date_added = now_unix

    # 1. Build Track List (mhlt) inside Data Set 1 (mhsd type=1)
    mhit_blobs = b"".join(_pack_mhit(t, db_version=db_version) for t in ordered_tracks)
    mhlt = b"mhlt" + struct.pack("<II", 92, len(ordered_tracks)) + bytes(92 - 12)
    sd1_payload = mhlt + mhit_blobs
    mhsd1_blob = b"mhsd" + struct.pack("<III", 96, 96 + len(sd1_payload), 1) + bytes(96 - 16) + sd1_payload

    # 2. Build Playlist List (mhlp) inside Data Set 2 (mhsd type=2)
    def is_audiobook_track(trk: TrackMetadata) -> bool:
        return (
            trk.ipod_rel_path.lower().endswith(".m4b")
            or trk.filetype_code.strip() == "M4B"
            or (trk.genre and trk.genre.strip().lower() == "audiobook")
        )

    music_tracks = [t for t in ordered_tracks if not is_audiobook_track(t)]
    audiobook_tracks = [t for t in ordered_tracks if is_audiobook_track(t)]

    # Master Playlist (is_master=True): On 3G iPod firmware 2.3, the firmware's
    # memory indexer only loads tracks that belong to the Master Playlist.
    # The firmware then parses the Master Playlist for .m4b tracks to populate the Audiobooks menu!
    mpl = _pack_mhyp("FLASHPOD", ordered_tracks, is_master=True, playlist_id=secrets.randbits(64))
    playlists_to_write = [mpl]
    written_names = {"flashpod", "ipod"}

    if playlists:
        for pl_name, pl_tracks in playlists.items():
            if pl_tracks and pl_name.lower() not in written_names:
                pl_blob = _pack_mhyp(pl_name, pl_tracks, is_master=False, playlist_id=secrets.randbits(64))
                playlists_to_write.append(pl_blob)
                written_names.add(pl_name.lower())

    mhlp = b"mhlp" + struct.pack("<II", 92, len(playlists_to_write)) + bytes(92 - 12)
    sd2_payload = mhlp + b"".join(playlists_to_write)
    mhsd2_blob = b"mhsd" + struct.pack("<III", 96, 96 + len(sd2_payload), 2) + bytes(96 - 16) + sd2_payload

    # 3. Wrap in Database Header (mhbd)
    mhbd_hdr = bytearray(104)
    mhbd_hdr[0:4] = b"mhbd"
    struct.pack_into(
        "<IIIII",
        mhbd_hdr,
        4,
        104,
        104 + len(mhsd1_blob) + len(mhsd2_blob),
        1,
        0x0B,
        2,
    )
    struct.pack_into("<Q", mhbd_hdr, 24, secrets.randbits(64))

    return bytes(mhbd_hdr) + mhsd1_blob + mhsd2_blob


# =====================================================================
# 4. iPod Library Manager (State, Sync, Rebuild)
# =====================================================================

class IPodLibrary:
    def __init__(self, ipod_root: Path):
        self.root = ipod_root.resolve()
        self.control_dir = self.root / "iPod_Control"
        self.music_dir = self.control_dir / "Music"
        self.itunes_dir = self.control_dir / "iTunes"
        self.db_path = self.itunes_dir / "iTunesDB"
        self.manifest_path = self.control_dir / "heritagepod_manifest.json"
        self.legacy_manifest_path = self.control_dir / "ipod3g_sync_manifest.json"
        self.old_itunes_manifest_path = self.itunes_dir / "ipod3g_sync_manifest.json"
        self.tracks: List[TrackMetadata] = []
        self.playlists: Dict[str, List[str]] = {}

    def ensure_structure(self) -> None:
        self.itunes_dir.mkdir(parents=True, exist_ok=True)
        for i in range(50):
            (self.music_dir / f"F{i:02d}").mkdir(parents=True, exist_ok=True)

    def load_manifest(self) -> None:
        if not self.manifest_path.is_file():
            if self.legacy_manifest_path.is_file():
                try:
                    shutil.copy(str(self.legacy_manifest_path), str(self.manifest_path))
                except Exception:
                    pass
            elif self.old_itunes_manifest_path.is_file():
                try:
                    shutil.copy(str(self.old_itunes_manifest_path), str(self.manifest_path))
                except Exception:
                    pass
        if self.manifest_path.is_file():
            try:
                data = json.loads(self.manifest_path.read_text(encoding="utf-8"))
                self.tracks = [TrackMetadata(**item) for item in data.get("tracks", [])]
                raw_pl = data.get("playlists", {})
                self.playlists = raw_pl if isinstance(raw_pl, dict) else {}
                # Filter out tracks whose files were manually deleted
                valid_tracks = []
                valid_rels = set()
                for t in self.tracks:
                    disk_path = self.ipod_rel_to_path(t.ipod_rel_path)
                    if disk_path.is_file():
                        valid_tracks.append(t)
                        valid_rels.add(t.ipod_rel_path)
                self.tracks = valid_tracks
                # Clean up playlist entries pointing to deleted tracks
                for pl_name in list(self.playlists.keys()):
                    self.playlists[pl_name] = [r for r in self.playlists[pl_name] if r in valid_rels]
            except Exception as e:
                print(f"Warning: could not read manifest ({e}); starting fresh scan.", file=sys.stderr)
                self.tracks = []
                self.playlists = {}
        else:
            self.tracks = []
            self.playlists = {}

    def create_playlist(self, name: str) -> bool:
        name = name.strip()
        if not name or name in self.playlists:
            return False
        self.playlists[name] = []
        return True

    def delete_playlist(self, name: str) -> bool:
        if name in self.playlists:
            del self.playlists[name]
            return True
        return False

    def rename_playlist(self, old_name: str, new_name: str) -> bool:
        new_name = new_name.strip()
        if old_name in self.playlists and new_name and new_name != old_name:
            self.playlists[new_name] = self.playlists.pop(old_name)
            return True
        return False

    def add_to_playlist(self, name: str, rel_paths: List[str]) -> int:
        if name not in self.playlists:
            self.playlists[name] = []
        added = 0
        cur_set = set(self.playlists[name])
        for r in rel_paths:
            if r not in cur_set:
                self.playlists[name].append(r)
                cur_set.add(r)
                added += 1
        return added

    def remove_from_playlist(self, name: str, rel_paths: List[str]) -> int:
        if name not in self.playlists:
            return 0
        to_del = set(rel_paths)
        orig_len = len(self.playlists[name])
        self.playlists[name] = [r for r in self.playlists[name] if r not in to_del]
        return orig_len - len(self.playlists[name])

    def reorder_playlist(self, name: str, from_idx: int, to_idx: int) -> bool:
        if name not in self.playlists or from_idx < 0 or to_idx < 0:
            return False
        items = self.playlists[name]
        if from_idx >= len(items) or to_idx >= len(items):
            return False
        item = items.pop(from_idx)
        items.insert(to_idx, item)
        return True

    def save_manifest_and_db(self, db_version: int = 0x0B) -> None:
        self.ensure_structure()
        for idx, t in enumerate(self.tracks, start=52):
            t.track_id = idx
            if t.artist.startswith("smb-share:") or t.artist in ("gvfs", "1000", "user", "run"):
                t.artist = "Unknown Artist"
            if t.album.startswith("smb-share:") or t.album in ("gvfs", "1000", "user", "run"):
                t.album = "Unknown Album"

        # Resolve playlists to TrackMetadata lists
        by_rel = {t.ipod_rel_path: t for t in self.tracks}
        resolved_playlists: Dict[str, List[TrackMetadata]] = {}
        for pl_name, rel_list in self.playlists.items():
            pl_trks = [by_rel[r] for r in rel_list if r in by_rel]
            if pl_trks:
                resolved_playlists[pl_name] = pl_trks

        payload = {
            "tracks": [asdict(t) for t in self.tracks],
            "playlists": self.playlists,
        }
        self.manifest_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        try:
            self.legacy_manifest_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        except Exception:
            pass
        db_bytes = build_itunesdb_bytes(self.tracks, playlists=resolved_playlists, db_version=db_version)
        # Early iPod firmware has a ~3.78 MB hardware RAM buffer limit for iTunesDB
        max_db_bytes = int(3.78 * 1024 * 1024)
        if len(db_bytes) > max_db_bytes:
            print(
                f"WARNING: iTunesDB size ({len(db_bytes) / (1024*1024):.2f} MB) exceeds the ~3.78 MB "
                "early-iPod RAM ceiling! The stock OS may display 0 songs until tracks are trimmed.",
                file=sys.stderr,
            )
        tmp_db = self.itunes_dir / "iTunesDB.new"
        with open(tmp_db, "wb") as f:
            f.write(db_bytes)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_db, self.db_path)
        # Keep /iPod_Control/iTunes/ clean (only iTunesDB) so old iTunesPrefs/iTunesControl cannot override it
        backup_dir = self.control_dir / "iTunes_backup_2022"
        for p in list(self.itunes_dir.iterdir()):
            if p.name != "iTunesDB":
                backup_dir.mkdir(parents=True, exist_ok=True)
                shutil.move(str(p), str(backup_dir / p.name))
        try:
            os.sync()
        except Exception:
            pass

    def ipod_rel_to_path(self, ipod_rel: str) -> Path:
        parts = [p for p in ipod_rel.split(":") if p]
        return self.root.joinpath(*parts)

    def next_ids(self) -> Tuple[int, int]:
        max_id = max((t.track_id for t in self.tracks), default=1000)
        next_tid = max_id + 1
        next_dbid = (0x3347000000000000 | next_tid)
        return next_tid, next_dbid

    def add_paths(
        self,
        sources: List[Path],
        progress_cb=None,
        flac_format: str = "alac",
    ) -> Tuple[int, int]:
        """
        Scan source files/folders, convert FLAC -> ALAC (.m4a) or AIFF (.aif),
        copy native files, and update iTunesDB.
        Returns (added_count, skipped_count).
        """
        self.ensure_structure()
        self.load_manifest()
        flac_format = (flac_format or "alac").strip().lower()

        existing_hashes = {t.source_hash for t in self.tracks}

        files_to_Import: List[Path] = []
        for raw_src in sources:
            raw_str = str(raw_src).strip()
            # Convert smb://server/share/path URIs to platform-native paths
            if raw_str.startswith("smb://") and hasattr(os, "getuid"):
                from urllib.parse import unquote, urlparse
                parsed = urlparse(raw_str)
                parts = [p for p in parsed.path.split("/") if p]
                if parsed.hostname and parts:
                    share = parts[0]
                    subpath = "/".join(unquote(p) for p in parts[1:])
                    gvfs_base = Path(f"/run/user/{os.getuid()}/gvfs/smb-share:server={parsed.hostname},share={share}")
                    raw_str = str(gvfs_base / subpath)
            elif raw_str.startswith("smb://") and sys.platform == "win32":
                from urllib.parse import unquote, urlparse
                parsed = urlparse(raw_str)
                raw_str = f"\\\\{parsed.hostname}{unquote(parsed.path).replace('/', chr(92))}"
            elif raw_str.startswith("file://"):
                from urllib.parse import unquote, urlparse
                raw_str = unquote(urlparse(raw_str).path)

            src = Path(os.path.expanduser(raw_str))
            # Fix classic Linux Tk askdirectory bug where double-clicking "Album" returns "/path/to/Album/Album"
            if not src.exists() and src.parent.is_dir() and src.name == src.parent.name:
                src = src.parent
            # Note: avoid .resolve() on GVFS FUSE mounts if it fails, only resolve when safe
            try:
                if not str(src).startswith("/run/user/"):
                    src = src.resolve()
            except Exception:
                pass

            if src.is_file() and src.suffix.lower() in SUPPORTED_EXTENSIONS:
                files_to_Import.append(src)
            elif src.is_dir():
                for root_dir, _, filenames in os.walk(src, followlinks=True):
                    for fn in sorted(filenames):
                        p = Path(root_dir) / fn
                        if p.suffix.lower() in SUPPORTED_EXTENSIONS and not fn.startswith("._"):
                            files_to_Import.append(p)

        added = 0
        skipped = 0
        total = len(files_to_Import)

        for idx, src_file in enumerate(files_to_Import, start=1):
            # Compute fast fingerprint (filename + size + mtime + first 64KB)
            st = src_file.stat()
            h = hashlib.sha1()
            h.update(f"{src_file.name}:{st.st_size}".encode("utf-8"))
            with src_file.open("rb") as f:
                h.update(f.read(65536))
            fingerprint = h.hexdigest()

            if fingerprint in existing_hashes:
                skipped += 1
                if progress_cb:
                    progress_cb(idx, total, f"Skipped duplicate: {src_file.name}")
                continue

            ext = src_file.suffix.lower()
            meta = parse_generic_metadata(src_file)
            track_id, dbid = self.next_ids()
            folder_idx = track_id % MUSIC_DIRS_COUNT
            folder_name = f"F{folder_idx:02d}"

            t0 = time.perf_counter()
            if ext == ".flac":
                target_sr = meta["sample_rate"] if meta["sample_rate"] in (44100, 48000) else 44100
                if flac_format == "aiff":
                    dest_ext = ".aif"
                    ft_code = "AIFF"
                    ft_desc = "AIFF Audio File"
                    dest_name = f"T{track_id}{dest_ext}"
                    dest_path = self.music_dir / folder_name / dest_name
                    if progress_cb:
                        progress_cb(idx, total, f"Converting FLAC -> AIFF: {meta['title']}")
                    convert_flac_to_aiff(src_file, dest_path, meta)
                    bitrate = int((target_sr * 16 * 2) / 1000)  # 1411 kbps for 44.1kHz
                else:
                    dest_ext = ".m4a"
                    ft_code = "M4A "
                    ft_desc = "Apple Lossless audio file"
                    dest_name = f"T{track_id}{dest_ext}"
                    dest_path = self.music_dir / folder_name / dest_name
                    if progress_cb:
                        progress_cb(idx, total, f"Converting FLAC -> ALAC (.m4a): {meta['title']}")
                    bitrate = convert_flac_to_alac(src_file, dest_path, meta)
            else:
                dest_ext = ext
                dest_name = f"T{track_id}{dest_ext}"
                dest_path = self.music_dir / folder_name / dest_name
                if progress_cb:
                    progress_cb(idx, total, f"Copying {ext.upper()}: {meta['title']}")
                shutil.copyfile(src_file, dest_path)
                target_sr = meta["sample_rate"]
                if ext in (".aiff", ".aif"):
                    ft_code, ft_desc = "AIFF", "AIFF Audio File"
                    bitrate = 1411
                elif ext == ".wav":
                    ft_code, ft_desc = "WAV ", "WAV Audio File"
                    bitrate = 1411
                elif ext == ".m4b":
                    ft_code, ft_desc = "M4B ", "AAC audio book"
                    bitrate = 256
                elif ext == ".m4a":
                    ft_code, ft_desc = "M4A ", "AAC audio file"
                    bitrate = 256
                else:
                    ft_code, ft_desc = "MPG3", "MPEG audio file"
                    bitrate = 320

            elapsed_ms = (time.perf_counter() - t0) * 1000
            file_size = dest_path.stat().st_size
            ipod_rel = f":iPod_Control:Music:{folder_name}:{dest_name}"

            new_track = TrackMetadata(
                track_id=track_id,
                dbid=dbid,
                title=meta["title"],
                artist=meta["artist"],
                album=meta["album"],
                genre=meta["genre"],
                composer=meta["composer"],
                track_number=meta["track_number"],
                total_tracks=meta["total_tracks"],
                disc_number=meta["disc_number"],
                total_discs=meta["total_discs"],
                year=meta["year"],
                duration_ms=meta["duration_ms"],
                sample_rate=target_sr,
                bitrate_kbps=bitrate,
                file_size=file_size,
                filetype_code=ft_code,
                filetype_desc=ft_desc,
                ipod_rel_path=ipod_rel,
                source_hash=fingerprint,
                date_added=int(time.time()),
            )
            self.tracks.append(new_track)
            existing_hashes.add(fingerprint)
            added += 1

            if progress_cb:
                progress_cb(
                    idx,
                    total,
                    f"Added [{meta['artist']} - {meta['title']}] ({elapsed_ms:.0f} ms)",
                )

        self.save_manifest_and_db()
        return added, skipped

    def remove_tracks_by_rel_paths(self, rel_paths: set, delete_files: bool = True) -> int:
        """
        Remove tracks matching the given ipod_rel_path set from the library and optionally
        unlink their audio files from /iPod_Control/Music/F##/.
        """
        self.load_manifest()
        kept: List[TrackMetadata] = []
        removed = 0
        for t in self.tracks:
            if t.ipod_rel_path in rel_paths:
                removed += 1
                if delete_files:
                    try:
                        disk_path = self.ipod_rel_to_path(t.ipod_rel_path)
                        if disk_path.is_file():
                            disk_path.unlink()
                    except Exception as e:
                        print(f"Warning: could not delete {t.ipod_rel_path}: {e}", file=sys.stderr)
            else:
                kept.append(t)
        if removed > 0:
            self.tracks = kept
            for pl_name in list(self.playlists.keys()):
                self.playlists[pl_name] = [r for r in self.playlists[pl_name] if r not in rel_paths]
            self.save_manifest_and_db()
        return removed

    def update_tracks_metadata(
        self,
        ordered_rel_paths: List[str],
        updates: dict,
        auto_number: bool = False,
        strip_title_numbers: bool = False,
        prefix_album: bool = False,
        set_audiobook: Optional[bool] = None,
    ) -> int:
        """
        Update metadata fields on tracks in ordered_rel_paths and rewrite iTunesDB.
        Only fields present in `updates` are modified.
        If set_audiobook is True, converts .m4a to .m4b on disk and sets Audiobook flags.
        """
        import re

        self.load_manifest()
        by_path = {t.ipod_rel_path: t for t in self.tracks}
        updated = 0
        for idx, rel in enumerate(ordered_rel_paths, start=1):
            t = by_path.get(rel)
            if t is None:
                continue
            if "title" in updates:
                t.title = str(updates["title"]).strip() or "Untitled"
            if strip_title_numbers:
                cleaned = re.sub(r"^\s*\d{1,3}\s*[-._)\]]+\s*", "", t.title).strip()
                if cleaned:
                    t.title = cleaned
            if prefix_album:
                album_prefix = (updates.get("album") or t.album or "").strip()
                if album_prefix and not t.title.lower().startswith(album_prefix.lower()):
                    t.title = f"{album_prefix} - {t.title}"
            if "artist" in updates:
                t.artist = str(updates["artist"]).strip() or "Unknown Artist"
            if "album" in updates:
                t.album = str(updates["album"]).strip() or "Unknown Album"
            if "genre" in updates:
                t.genre = str(updates["genre"]).strip()
            if "composer" in updates:
                t.composer = str(updates["composer"]).strip()
            if "track_number" in updates:
                t.track_number = max(0, int(updates["track_number"]))
            if auto_number:
                t.track_number = idx
                t.total_tracks = len(ordered_rel_paths)
            if "disc_number" in updates:
                t.disc_number = max(1, int(updates["disc_number"]))
            if "year" in updates:
                t.year = max(0, int(updates["year"]))

            if set_audiobook is True:
                # Stock iPod firmware requires .m4b extension to display in Audiobooks menu
                old_rel = t.ipod_rel_path
                if t.ipod_rel_path.lower().endswith(".m4a"):
                    old_path = self.ipod_rel_to_path(t.ipod_rel_path)
                    new_path = old_path.with_suffix(".m4b")
                    if old_path.is_file():
                        try:
                            old_path.rename(new_path)
                        except Exception as e:
                            print(f"Warning: could not rename {old_path} -> {new_path}: {e}", file=sys.stderr)
                    t.ipod_rel_path = t.ipod_rel_path[:-4] + ".m4b"
                    t.filetype_code = "M4B "
                    t.filetype_desc = "AAC audio book"
                elif t.ipod_rel_path.lower().endswith(".m4b"):
                    t.filetype_code = "M4B "
                    t.filetype_desc = "AAC audio book"
                else:
                    # For MP3/AIFF/WAV audiobooks, retain native filetype code
                    t.filetype_code = "MPG3" if t.ipod_rel_path.lower().endswith(".mp3") else t.filetype_code
                    t.filetype_desc = "MPEG audio file" if t.ipod_rel_path.lower().endswith(".mp3") else t.filetype_desc
                t.genre = "Audiobook"
                if old_rel != t.ipod_rel_path:
                    for pl_name, p_list in self.playlists.items():
                        self.playlists[pl_name] = [t.ipod_rel_path if r == old_rel else r for r in p_list]
            elif set_audiobook is False:
                old_rel = t.ipod_rel_path
                if t.ipod_rel_path.lower().endswith(".m4b"):
                    old_path = self.ipod_rel_to_path(t.ipod_rel_path)
                    new_path = old_path.with_suffix(".m4a")
                    if old_path.is_file():
                        try:
                            old_path.rename(new_path)
                        except Exception as e:
                            print(f"Warning: could not rename {old_path} -> {new_path}: {e}", file=sys.stderr)
                    t.ipod_rel_path = t.ipod_rel_path[:-4] + ".m4a"
                    t.filetype_code = "M4A "
                    t.filetype_desc = "AAC audio file"
                if t.genre and t.genre.lower() == "audiobook":
                    t.genre = "Music"
                if old_rel != t.ipod_rel_path:
                    for pl_name, p_list in self.playlists.items():
                        self.playlists[pl_name] = [t.ipod_rel_path if r == old_rel else r for r in p_list]
            updated += 1

        if updated > 0:
            self.save_manifest_and_db()
        return updated

    def re_read_tags_from_files(self, rel_paths: Optional[set] = None, progress_cb=None) -> int:
        """
        Re-read embedded ID3/MP4/FLAC tags and exact durations directly from the audio files
        on the iPod using pure-Python MP4/ID3 parsers (and optional mutagen fallback).
        """
        self.load_manifest()
        targets = [
            t for t in self.tracks
            if (rel_paths is None or t.ipod_rel_path in rel_paths)
        ]
        updated = 0
        total = len(targets)
        for idx, t in enumerate(targets, start=1):
            disk_path = self.ipod_rel_to_path(t.ipod_rel_path)
            if not disk_path.is_file():
                continue
            if progress_cb and (idx == 1 or idx % 10 == 0 or idx == total):
                progress_cb(idx, total, f"Reading tags from {disk_path.name}...")
            ext = disk_path.suffix.lower()
            changed_this = False
            try:
                if ext in (".m4a", ".m4b"):
                    parsed = _parse_mp4_atoms(disk_path)
                elif ext == ".mp3":
                    parsed = _parse_id3v2_tags(disk_path)
                elif ext == ".flac":
                    parsed = parse_flac_metadata(disk_path)
                else:
                    parsed = {}

                if parsed.get("title"):
                    t.title = parsed["title"]
                    changed_this = True
                if parsed.get("artist"):
                    t.artist = parsed["artist"]
                    changed_this = True
                if parsed.get("album"):
                    t.album = parsed["album"]
                    changed_this = True
                if parsed.get("genre"):
                    t.genre = parsed["genre"]
                    changed_this = True
                if parsed.get("composer"):
                    t.composer = parsed["composer"]
                    changed_this = True
                if parsed.get("track_number"):
                    t.track_number = int(parsed["track_number"])
                    changed_this = True
                if parsed.get("total_tracks"):
                    t.total_tracks = int(parsed["total_tracks"])
                    changed_this = True
                if parsed.get("disc_number"):
                    t.disc_number = int(parsed["disc_number"])
                    changed_this = True
                if parsed.get("year"):
                    t.year = int(parsed["year"])
                    changed_this = True
                if parsed.get("duration_ms", 0) > 0:
                    t.duration_ms = int(parsed["duration_ms"])
                    changed_this = True
                if parsed.get("sample_rate", 0) > 0:
                    t.sample_rate = int(parsed["sample_rate"])
                    changed_this = True
                if parsed.get("bitrate_kbps", 0) > 0:
                    t.bitrate_kbps = int(parsed["bitrate_kbps"])
                    changed_this = True
            except Exception:
                pass

            if not changed_this:
                try:
                    import mutagen
                    mfile = mutagen.File(str(disk_path), easy=True)
                    if mfile is not None:
                        if getattr(mfile, "info", None) is not None:
                            if getattr(mfile.info, "length", 0):
                                t.duration_ms = int(mfile.info.length * 1000)
                            if getattr(mfile.info, "sample_rate", 0):
                                t.sample_rate = int(mfile.info.sample_rate)
                            if getattr(mfile.info, "bitrate", 0):
                                t.bitrate_kbps = max(32, int(mfile.info.bitrate) // 1000)
                        mtags = mfile.tags or {}
                        def _mfirst(k: str) -> str:
                            v = mtags.get(k)
                            if isinstance(v, list):
                                return str(v[0]).strip() if v else ""
                            return str(v).strip() if v else ""
                        if _mfirst("title"):
                            t.title = _mfirst("title")
                        if _mfirst("artist"):
                            t.artist = _mfirst("artist")
                        if _mfirst("album"):
                            t.album = _mfirst("album")
                        if _mfirst("genre"):
                            t.genre = _mfirst("genre")
                        if _mfirst("composer"):
                            t.composer = _mfirst("composer")
                        if _mfirst("tracknumber"):
                            t.track_number = _safe_int(_mfirst("tracknumber").split("/")[0], t.track_number)
                        if _mfirst("date"):
                            d_raw = _mfirst("date")
                            if len(d_raw) >= 4 and d_raw[:4].isdigit():
                                t.year = int(d_raw[:4])
                        changed_this = True
                except Exception:
                    pass

            if changed_this:
                updated += 1

        if updated > 0:
            self.save_manifest_and_db()
        return updated

    def convert_aiff_tracks_to_alac(
        self,
        rel_paths: Optional[set] = None,
        progress_cb=None,
    ) -> Tuple[int, int]:
        """
        Convert existing uncompressed AIFF (.aif/.aiff) tracks on the iPod into
        Apple Lossless (.m4a) in-place, removing the old .aif files and updating iTunesDB.
        Returns (converted_count, bytes_saved).
        """
        self.load_manifest()
        targets = [
            t for t in self.tracks
            if t.filetype_code.strip() == "AIFF"
            and (rel_paths is None or t.ipod_rel_path in rel_paths)
        ]
        converted = 0
        bytes_saved = 0
        total = len(targets)

        for idx, t in enumerate(targets, start=1):
            old_disk_path = self.ipod_rel_to_path(t.ipod_rel_path)
            if not old_disk_path.is_file():
                continue
            if progress_cb:
                progress_cb(idx, total, f"Converting AIFF -> ALAC: {t.artist} - {t.title}")

            new_disk_path = old_disk_path.with_suffix(".m4a")
            meta_dict = {
                "title": t.title,
                "artist": t.artist,
                "album": t.album,
                "genre": t.genre,
                "composer": t.composer,
                "track_number": t.track_number,
                "total_tracks": t.total_tracks,
                "disc_number": t.disc_number,
                "total_discs": t.total_discs,
                "year": t.year,
                "sample_rate": t.sample_rate if t.sample_rate in (44100, 48000) else 44100,
            }
            old_size = old_disk_path.stat().st_size
            bitrate = convert_aiff_to_alac(old_disk_path, new_disk_path, meta_dict)
            new_size = new_disk_path.stat().st_size

            if new_disk_path != old_disk_path and old_disk_path.is_file():
                old_disk_path.unlink(missing_ok=True)

            # Update TrackMetadata in place
            parts = t.ipod_rel_path.split(":")
            parts[-1] = new_disk_path.name
            t.ipod_rel_path = ":".join(parts)
            t.filetype_code = "M4A "
            t.filetype_desc = "Apple Lossless audio file"
            t.file_size = new_size
            t.bitrate_kbps = bitrate
            converted += 1
            bytes_saved += max(0, old_size - new_size)

        if converted > 0:
            self.save_manifest_and_db()
        return converted, bytes_saved

    def convert_audiobook_tracks_to_m4b(
        self,
        rel_paths: Optional[set] = None,
        progress_cb=None,
    ) -> Tuple[int, int]:
        """
        Transcode MP3/audio tracks marked as Audiobooks on the iPod into
        hardware-compatible AAC .m4b files in-place, removing the old files
        and updating iTunesDB. Returns (converted_count, bytes_saved).
        """
        self.load_manifest()
        targets = [
            t for t in self.tracks
            if not t.ipod_rel_path.lower().endswith(".m4b")
            and (
                (rel_paths is not None and t.ipod_rel_path in rel_paths)
                or (rel_paths is None and (t.genre and t.genre.lower() == "audiobook"))
            )
        ]
        converted = 0
        bytes_saved = 0
        total = len(targets)

        for idx, t in enumerate(targets, start=1):
            old_disk_path = self.ipod_rel_to_path(t.ipod_rel_path)
            if not old_disk_path.is_file():
                continue
            if progress_cb:
                progress_cb(idx, total, f"Transcoding to AAC .m4b: {t.title} ({t.album})")

            new_disk_path = old_disk_path.with_suffix(".m4b")
            meta_dict = {
                "title": t.title,
                "artist": t.artist,
                "album": t.album,
                "genre": "Audiobook",
                "composer": t.composer,
                "track_number": t.track_number,
                "total_tracks": t.total_tracks,
            }
            old_size = old_disk_path.stat().st_size
            bitrate = convert_audio_to_aac_m4b(old_disk_path, new_disk_path, meta_dict, bitrate_kbps=128)
            new_size = new_disk_path.stat().st_size

            if new_disk_path != old_disk_path and old_disk_path.is_file():
                old_disk_path.unlink(missing_ok=True)

            # Update TrackMetadata in place
            parts = t.ipod_rel_path.split(":")
            parts[-1] = new_disk_path.name
            t.ipod_rel_path = ":".join(parts)
            t.filetype_code = "M4B "
            t.filetype_desc = "AAC audio book"
            t.file_size = new_size
            t.bitrate_kbps = bitrate
            t.genre = "Audiobook"
            converted += 1
            bytes_saved += (old_size - new_size)

        if converted > 0:
            self.save_manifest_and_db()
        return converted, bytes_saved


# =====================================================================
# 5. Desktop GUI & CLI Entrypoint
# =====================================================================

def eject_ipod_device(mount_path: Path) -> Tuple[bool, str]:
    """
    Safely flush, unmount, and eject the iPod block device so the
    iPod display transitions from 'Do not disconnect' to 'OK to disconnect'.
    Cross-platform support for Linux, macOS, and Windows.
    """
    p = Path(mount_path)
    if not p.is_dir():
        return False, f"Directory does not exist: {mount_path}"

    if hasattr(os, "sync"):
        try:
            os.sync()
        except Exception:
            pass

    # --- macOS (Darwin) ---
    if sys.platform == "darwin":
        try:
            res = subprocess.run(["diskutil", "eject", str(p)], capture_output=True, text=True)
            if res.returncode == 0:
                return True, "iPod safely ejected via diskutil (OK to disconnect)."
            res2 = subprocess.run(["diskutil", "unmountDisk", str(p)], capture_output=True, text=True)
            if res2.returncode == 0:
                return True, "iPod unmounted via diskutil (OK to disconnect)."
            return False, f"diskutil error: {res.stderr.strip() or res2.stderr.strip()}"
        except Exception as e:
            return False, f"macOS eject failed: {e}"

    # --- Windows (win32) ---
    if sys.platform == "win32":
        drive_letter = str(p.resolve())[:2].upper()
        if len(drive_letter) == 2 and drive_letter[1] == ":":
            ps_cmd = f'(New-Object -comObject Shell.Application).Namespace(17).ParseName("{drive_letter}").InvokeVerb("Eject")'
            try:
                res = subprocess.run(["powershell", "-NoProfile", "-Command", ps_cmd], capture_output=True, text=True)
                if res.returncode == 0:
                    return True, f"Drive {drive_letter} safely ejected (OK to disconnect)."
            except Exception:
                pass
            try:
                res = subprocess.run(["mountvol", f"{drive_letter}\\", "/P"], capture_output=True, text=True)
                if res.returncode == 0:
                    return True, f"Drive {drive_letter} dismounted (OK to disconnect)."
            except Exception:
                pass
            return True, f"Buffers flushed on {drive_letter}. Safe to disconnect."

    # --- Linux / Unix ---
    dev = None
    if shutil.which("findmnt"):
        try:
            res = subprocess.run(
                ["findmnt", "-n", "-o", "SOURCE", str(p)],
                capture_output=True,
                text=True,
            )
            if res.returncode == 0 and res.stdout.strip():
                dev = res.stdout.strip()
        except Exception:
            pass

    # Method 1: GIO mount -e (standard unprivileged desktop eject)
    if shutil.which("gio"):
        try:
            res = subprocess.run(
                ["gio", "mount", "-e", str(p)],
                capture_output=True,
                text=True,
            )
            if res.returncode == 0:
                return True, "iPod safely unmounted and ejected (OK to disconnect)."
        except Exception:
            pass

    # Method 2: udisksctl unmount & power-off
    if dev and shutil.which("udisksctl"):
        try:
            subprocess.run(["udisksctl", "unmount", "-b", dev], capture_output=True)
            res_po = subprocess.run(["udisksctl", "power-off", "-b", dev], capture_output=True, text=True)
            if res_po.returncode != 0:
                parent_dev = re.sub(r"p?\d+$", "", dev)
                if parent_dev and parent_dev != dev:
                    res_po = subprocess.run(["udisksctl", "power-off", "-b", parent_dev], capture_output=True, text=True)
            if res_po.returncode == 0:
                return True, "iPod unmounted and powered off safely (OK to disconnect)."
        except Exception:
            pass

    # Method 3: eject command
    target = dev if dev else str(p)
    if shutil.which("eject"):
        try:
            res = subprocess.run(["eject", target], capture_output=True, text=True)
            if res.returncode == 0:
                return True, "iPod safely ejected via eject."
        except Exception:
            pass

    # Method 4: umount fallback
    if shutil.which("umount"):
        try:
            res = subprocess.run(["umount", str(p)], capture_output=True, text=True)
            if res.returncode == 0:
                return True, "iPod unmounted via umount (OK to disconnect)."
            return False, f"Could not unmount {p}: {res.stderr.strip()}"
        except Exception as e:
            return False, str(e)

    return False, "No eject/unmount command succeeded."


def detect_mounted_ipods() -> List[Path]:
    """Scan platform-specific mount points for mounted iPods."""
    candidates: List[Path] = []

    # macOS: check /Volumes/*
    if sys.platform == "darwin":
        volumes = Path("/Volumes")
        if volumes.is_dir():
            try:
                for child in volumes.iterdir():
                    if child.is_dir() and (child / "iPod_Control").exists():
                        candidates.append(child)
            except PermissionError:
                pass
        return candidates

    # Windows: check drive letters C:\ through Z:\
    if sys.platform == "win32":
        import string
        for letter in string.ascii_uppercase[2:]:
            root = Path(f"{letter}:\\")
            try:
                if root.is_dir() and (root / "iPod_Control").exists():
                    candidates.append(root)
            except (PermissionError, OSError):
                continue
        return candidates

    # Linux / BSD
    user = os.environ.get("USER", "")
    search_roots = [
        Path(f"/run/media/{user}"),
        Path(f"/media/{user}"),
        Path("/media"),
        Path("/mnt"),
    ]
    for root in search_roots:
        if not root.is_dir():
            continue
        try:
            for child in root.iterdir():
                if child.is_dir() and (child / "iPod_Control").exists():
                    candidates.append(child)
        except PermissionError:
            continue
    return candidates


def detect_gvfs_music_dir() -> Optional[Path]:
    """Detect mounted GVFS SMB/network shares (Linux only)."""
    if not hasattr(os, "getuid"):
        return None
    gvfs_root = Path(f"/run/user/{os.getuid()}/gvfs")
    if gvfs_root.is_dir():
        try:
            for share in gvfs_root.iterdir():
                if share.is_dir():
                    music_sub = share / "Music"
                    if music_sub.is_dir():
                        return music_sub
                    return share
        except PermissionError:
            pass
    return None


def _fmt_duration(ms: int) -> str:
    secs = max(0, int(ms) // 1000)
    m, s = divmod(secs, 60)
    return f"{m}:{s:02d}"


def launch_gui(initial_ipod: Optional[Path] = None) -> None:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk, simpledialog

    root = tk.Tk()
    root.title("HeritagePod — Vintage iPod Sync & Library Manager")
    root.geometry("1080x680")
    root.minsize(860, 520)

    ipod_var = tk.StringVar()
    detected = detect_mounted_ipods()
    if initial_ipod:
        ipod_var.set(str(initial_ipod))
    elif detected:
        ipod_var.set(str(detected[0]))

    nas_default = detect_gvfs_music_dir()
    source_path_var = tk.StringVar(value=str(nas_default) if nas_default else "")
    flac_target_var = tk.StringVar(value="ALAC (.m4a)")

    # In-memory cache of loaded tracks and playlists for instant search/filter/sort
    cached_tracks: List[TrackMetadata] = []
    tracks_by_rel: Dict[str, TrackMetadata] = {}
    cached_playlists: Dict[str, List[str]] = {}
    sort_state = {"col": "artist", "reverse": False}

    def _pick_directory(title: str, initial_dir: Optional[str] = None) -> Optional[str]:
        if sys.platform.startswith("linux") and shutil.which("zenity"):
            cmd = ["zenity", "--file-selection", "--directory", f"--title={title}"]
            if initial_dir and Path(initial_dir).is_dir():
                cmd.append(f"--filename={initial_dir.rstrip('/')}/")
            res = subprocess.run(cmd, capture_output=True, text=True)
            if res.returncode == 0 and res.stdout.strip():
                return res.stdout.strip()
            return None
        d = filedialog.askdirectory(title=title, initialdir=initial_dir)
        if not d:
            return None
        p = Path(d)
        if not p.exists() and p.parent.is_dir() and p.name == p.parent.name:
            return str(p.parent)
        return str(p)

    # --- Row 1: iPod Mount Path ---
    top_frame = ttk.Frame(root, padding=(12, 10, 12, 4))
    top_frame.pack(fill=tk.X)

    ttk.Label(top_frame, text="iPod Mount Path:", width=16).pack(side=tk.LEFT)
    ipod_entry = ttk.Entry(top_frame, textvariable=ipod_var, width=42)
    ipod_entry.pack(side=tk.LEFT, padx=(6, 6), fill=tk.X, expand=True)

    def browse_ipod():
        d = _pick_directory("Select Mounted iPod Root Directory", ipod_var.get().strip())
        if d:
            ipod_var.set(d)
            reload_from_disk()

    ttk.Button(top_frame, text="Browse...", command=browse_ipod).pack(side=tk.LEFT, padx=2)
    ttk.Button(top_frame, text="Refresh Library", command=lambda: reload_from_disk()).pack(side=tk.LEFT, padx=2)
    ttk.Button(top_frame, text="Rebuild iTunesDB", command=lambda: rebuild_db_now()).pack(side=tk.LEFT, padx=2)
    ttk.Button(top_frame, text="⏏ Eject iPod", command=lambda: eject_ipod_now()).pack(side=tk.LEFT, padx=(6, 2))

    # --- Row 2: Source / NAS Path + FLAC Target Format + Add Buttons ---
    src_frame = ttk.Frame(root, padding=(12, 4, 12, 6))
    src_frame.pack(fill=tk.X)
    ttk.Label(src_frame, text="Source / NAS Path:", width=16).pack(side=tk.LEFT)
    src_entry = ttk.Entry(src_frame, textvariable=source_path_var, width=32)
    src_entry.pack(side=tk.LEFT, padx=(6, 6), fill=tk.X, expand=True)

    ttk.Label(src_frame, text="FLAC ->").pack(side=tk.LEFT, padx=(4, 2))
    flac_combo = ttk.Combobox(
        src_frame,
        textvariable=flac_target_var,
        values=("ALAC (.m4a)", "AIFF (.aif)"),
        width=12,
        state="readonly",
    )
    flac_combo.pack(side=tk.LEFT, padx=(0, 6))

    def sync_typed_path():
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return
        s = source_path_var.get().strip()
        if not s:
            messagebox.showerror("Error", "Please enter or paste a folder/file path to sync.")
            return
        _run_sync([Path(s)])

    ttk.Button(src_frame, text="Sync Path", command=sync_typed_path).pack(side=tk.LEFT, padx=2)
    ttk.Button(src_frame, text="+ Add Folder...", command=lambda: add_folder()).pack(side=tk.LEFT, padx=2)
    ttk.Button(src_frame, text="+ Add Files...", command=lambda: add_files()).pack(side=tk.LEFT, padx=2)

    # --- Row 3: Search & Filter Bar ---
    filter_frame = ttk.LabelFrame(root, text="Search & Filter Library", padding=(10, 6, 10, 8))
    filter_frame.pack(fill=tk.X, padx=12, pady=(2, 6))

    search_var = tk.StringVar()
    playlist_filter_var = tk.StringVar(value="All Tracks (Library)")
    artist_filter_var = tk.StringVar(value="All Artists")
    album_filter_var = tk.StringVar(value="All Albums")
    format_filter_var = tk.StringVar(value="All Formats")
    count_label_var = tk.StringVar(value="0 / 0 tracks")

    ttk.Label(filter_frame, text="Search:").pack(side=tk.LEFT)
    search_entry = ttk.Entry(filter_frame, textvariable=search_var, width=18)
    search_entry.pack(side=tk.LEFT, padx=(4, 8), fill=tk.X, expand=True)

    ttk.Label(filter_frame, text="Playlist:").pack(side=tk.LEFT)
    playlist_combo = ttk.Combobox(
        filter_frame,
        textvariable=playlist_filter_var,
        values=["All Tracks (Library)"],
        width=16,
        state="readonly",
    )
    playlist_combo.pack(side=tk.LEFT, padx=(4, 8))

    ttk.Label(filter_frame, text="Artist:").pack(side=tk.LEFT)
    artist_combo = ttk.Combobox(filter_frame, textvariable=artist_filter_var, width=16, state="readonly")
    artist_combo.pack(side=tk.LEFT, padx=(4, 8))

    ttk.Label(filter_frame, text="Album:").pack(side=tk.LEFT)
    album_combo = ttk.Combobox(filter_frame, textvariable=album_filter_var, width=18, state="readonly")
    album_combo.pack(side=tk.LEFT, padx=(4, 8))

    ttk.Label(filter_frame, text="Format:").pack(side=tk.LEFT)
    format_combo = ttk.Combobox(
        filter_frame,
        textvariable=format_filter_var,
        values=("All Formats", "ALAC", "AIFF", "MPG3", "M4A", "M4B"),
        width=10,
        state="readonly",
    )
    format_combo.pack(side=tk.LEFT, padx=(4, 8))

    def clear_filters():
        search_var.set("")
        playlist_filter_var.set("All Tracks (Library)")
        artist_filter_var.set("All Artists")
        album_filter_var.set("All Albums")
        format_filter_var.set("All Formats")
        apply_filter_and_populate()

    ttk.Button(filter_frame, text="Clear", width=6, command=clear_filters).pack(side=tk.LEFT, padx=(0, 6))
    ttk.Label(filter_frame, textvariable=count_label_var, width=14, anchor=tk.E).pack(side=tk.RIGHT)

    # --- Row 4: Track Table (Multi-select + Sortable Columns) ---
    mid_frame = ttk.Frame(root, padding=(12, 0, 12, 6))
    mid_frame.pack(fill=tk.BOTH, expand=True)

    cols = ("id", "artist", "album", "track", "title", "genre", "year", "time", "format")
    tree = ttk.Treeview(mid_frame, columns=cols, show="headings", height=16, selectmode="extended")

    col_specs = [
        ("id", "ID", 52, tk.CENTER),
        ("artist", "Artist", 170, tk.W),
        ("album", "Album", 190, tk.W),
        ("track", "#", 42, tk.CENTER),
        ("title", "Title", 250, tk.W),
        ("genre", "Genre", 105, tk.W),
        ("year", "Year", 55, tk.CENTER),
        ("time", "Time", 58, tk.CENTER),
        ("format", "Fmt", 58, tk.CENTER),
    ]
    for col_id, label, width, anchor in col_specs:
        tree.heading(col_id, text=label, command=lambda c=col_id: toggle_sort(c))
        tree.column(col_id, width=width, anchor=anchor)

    tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

    sb = ttk.Scrollbar(mid_frame, orient=tk.VERTICAL, command=tree.yview)
    tree.configure(yscrollcommand=sb.set)
    sb.pack(side=tk.RIGHT, fill=tk.Y)

    # --- Row 5: Action Buttons (Edit Tags / Select Album / Playlists / Delete) ---
    act_frame = ttk.Frame(root, padding=(12, 4, 12, 6))
    act_frame.pack(fill=tk.X)

    ttk.Button(
        act_frame,
        text="Edit Metadata / Tags...",
        command=lambda: open_edit_dialog(),
    ).pack(side=tk.LEFT, padx=(0, 6))
    ttk.Button(
        act_frame,
        text="Select Whole Album",
        command=lambda: select_group("album"),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="Select Whole Artist",
        command=lambda: select_group("artist"),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="+ Add to Playlist...",
        command=lambda: prompt_add_to_playlist_dialog(),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="📋 Manage Playlists...",
        command=lambda: open_playlist_manager(),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="Re-read Tags from File(s)",
        command=lambda: reread_selected_tags(),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="Convert AIFF -> ALAC (.m4a)",
        command=lambda: convert_selected_aiff_to_alac(),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="Transcode Audiobooks -> AAC (.m4b)",
        command=lambda: convert_selected_audiobooks_to_m4b(),
    ).pack(side=tk.LEFT, padx=3)
    ttk.Button(
        act_frame,
        text="Delete Selected Track(s)...",
        command=lambda: delete_selected_tracks(),
    ).pack(side=tk.RIGHT, padx=(6, 0))

    # --- Row 6: Status Bar ---
    status_var = tk.StringVar(value="Ready. Double-click any track (or select multiple tracks) to edit tags, or press Delete to remove.")
    status_bar = ttk.Label(root, textvariable=status_var, padding=(12, 4, 12, 8), relief=tk.SUNKEN, anchor=tk.W)
    status_bar.pack(fill=tk.X, side=tk.BOTTOM)

    # --- Helper Functions for Filtering, Sorting, Selection ---
    def _sort_key_for_col(t: TrackMetadata, col: str):
        if col == "id":
            return (t.track_id,)
        if col == "artist":
            return (t.artist.lower(), t.album.lower(), t.disc_number, t.track_number, t.title.lower())
        if col == "album":
            return (t.album.lower(), t.disc_number, t.track_number, t.title.lower())
        if col == "track":
            return (t.track_number, t.title.lower())
        if col == "title":
            return (t.title.lower(), t.artist.lower())
        if col == "genre":
            return ((t.genre or "").lower(), t.artist.lower(), t.album.lower(), t.track_number)
        if col == "year":
            return (t.year or 0, t.artist.lower(), t.album.lower(), t.track_number)
        if col == "time":
            return (t.duration_ms,)
        if col == "format":
            return (t.filetype_code.strip(), t.artist.lower(), t.album.lower(), t.track_number)
        return (t.artist.lower(), t.album.lower(), t.track_number)

    def toggle_sort(col: str):
        if sort_state["col"] == col:
            sort_state["reverse"] = not sort_state["reverse"]
        else:
            sort_state["col"] = col
            sort_state["reverse"] = False
        apply_filter_and_populate()

    def update_filter_dropdowns():
        pl_names = sorted(cached_playlists.keys(), key=lambda s: s.lower())
        playlist_combo["values"] = ["All Tracks (Library)"] + pl_names
        if playlist_filter_var.get() not in playlist_combo["values"]:
            playlist_filter_var.set("All Tracks (Library)")

        artists = sorted({t.artist for t in cached_tracks if t.artist}, key=lambda s: s.lower())
        artist_combo["values"] = ["All Artists"] + artists
        if artist_filter_var.get() not in artist_combo["values"]:
            artist_filter_var.set("All Artists")

        sel_artist = artist_filter_var.get()
        albums = sorted(
            {
                t.album
                for t in cached_tracks
                if t.album and (sel_artist == "All Artists" or t.artist == sel_artist)
            },
            key=lambda s: s.lower(),
        )
        album_combo["values"] = ["All Albums"] + albums
        if album_filter_var.get() not in album_combo["values"]:
            album_filter_var.set("All Albums")

    def apply_filter_and_populate(preserve_selection: bool = True):
        prev_sel = set(tree.selection()) if preserve_selection else set()
        for row in tree.get_children():
            tree.delete(row)

        q = search_var.get().strip().lower()
        f_playlist = playlist_filter_var.get()
        f_artist = artist_filter_var.get()
        f_album = album_filter_var.get()
        f_fmt = format_filter_var.get()

        pl_rel_list = cached_playlists.get(f_playlist) if f_playlist != "All Tracks (Library)" else None
        pl_rel_set = set(pl_rel_list) if pl_rel_list is not None else None

        filtered: List[TrackMetadata] = []
        for t in cached_tracks:
            if pl_rel_set is not None and t.ipod_rel_path not in pl_rel_set:
                continue
            if f_artist != "All Artists" and t.artist != f_artist:
                continue
            if f_album != "All Albums" and t.album != f_album:
                continue
            if f_fmt != "All Formats" and t.filetype_code.strip() != f_fmt:
                continue
            if q:
                haystack = f"{t.title} {t.artist} {t.album} {t.genre} {t.composer} {t.year or ''} {t.track_id} {t.ipod_rel_path}".lower()
                if q not in haystack:
                    continue
            filtered.append(t)

        col = sort_state["col"]
        if pl_rel_list is not None and col in ("track", "id"):
            pos_map = {r: idx for idx, r in enumerate(pl_rel_list)}
            filtered.sort(key=lambda t: pos_map.get(t.ipod_rel_path, 999999), reverse=sort_state["reverse"])
        else:
            filtered.sort(key=lambda t: _sort_key_for_col(t, col), reverse=sort_state["reverse"])

        to_reselect = []
        for t in filtered:
            iid = t.ipod_rel_path
            tree.insert(
                "",
                tk.END,
                iid=iid,
                values=(
                    t.track_id,
                    t.artist,
                    t.album,
                    t.track_number if t.track_number > 0 else "-",
                    t.title,
                    t.genre or "",
                    t.year if t.year > 0 else "-",
                    _fmt_duration(t.duration_ms),
                    t.filetype_code.strip(),
                ),
            )
            if iid in prev_sel:
                to_reselect.append(iid)

        if to_reselect:
            tree.selection_set(to_reselect)

        count_label_var.set(f"{len(filtered)} / {len(cached_tracks)} tracks")

    def reload_from_disk():
        nonlocal cached_tracks, tracks_by_rel, cached_playlists
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            cached_tracks = []
            tracks_by_rel = {}
            cached_playlists = {}
            apply_filter_and_populate(preserve_selection=False)
            return
        lib = IPodLibrary(Path(p))
        lib.load_manifest()
        cached_tracks = list(lib.tracks)
        tracks_by_rel = {t.ipod_rel_path: t for t in cached_tracks}
        cached_playlists = dict(lib.playlists)
        update_filter_dropdowns()
        apply_filter_and_populate()
        status_var.set(f"Loaded {len(cached_tracks)} tracks from {p}. Double-click to edit tags, or select & Delete.")

    search_var.trace_add("write", lambda *_: apply_filter_and_populate())

    def on_artist_combo_changed(_event=None):
        update_filter_dropdowns()
        apply_filter_and_populate()

    playlist_combo.bind("<<ComboboxSelected>>", lambda _e: apply_filter_and_populate())
    artist_combo.bind("<<ComboboxSelected>>", on_artist_combo_changed)
    album_combo.bind("<<ComboboxSelected>>", lambda _e: apply_filter_and_populate())
    format_combo.bind("<<ComboboxSelected>>", lambda _e: apply_filter_and_populate())

    def select_all_visible(_event=None):
        tree.selection_set(tree.get_children())
        return "break"

    tree.bind("<Control-a>", select_all_visible)
    tree.bind("<Control-A>", select_all_visible)

    def select_group(field: str):
        sel = list(tree.selection())
        if not sel:
            messagebox.showinfo("Select Track First", f"Select at least one track to highlight its entire {field}.")
            return
        target_vals = {getattr(tracks_by_rel[iid], field) for iid in sel if iid in tracks_by_rel}
        matching = [
            iid for iid in tree.get_children()
            if iid in tracks_by_rel and getattr(tracks_by_rel[iid], field) in target_vals
        ]
        if matching:
            tree.selection_set(matching)
            status_var.set(f"Selected {len(matching)} track(s) matching {field}: {', '.join(sorted(target_vals))}")

    # --- Delete Tracks ---
    def delete_selected_tracks(_event=None):
        sel = list(tree.selection())
        if not sel:
            messagebox.showinfo("No Tracks Selected", "Please select one or more tracks in the table to delete.")
            return
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        sample_names = [
            f"• {tracks_by_rel[iid].artist} — {tracks_by_rel[iid].title} ({tracks_by_rel[iid].album})"
            for iid in sel[:8]
            if iid in tracks_by_rel
        ]
        more_txt = f"\n...and {len(sel) - 8} more track(s)." if len(sel) > 8 else ""
        confirm = messagebox.askyesno(
            "Confirm Delete from iPod",
            f"Delete {len(sel)} selected track(s) from your iPod and remove their audio files?\n\n"
            + "\n".join(sample_names)
            + more_txt,
        )
        if not confirm:
            return
        status_var.set(f"Deleting {len(sel)} track(s) and updating iTunesDB...")
        root.update_idletasks()
        lib = IPodLibrary(Path(p))
        removed = lib.remove_tracks_by_rel_paths(set(sel), delete_files=True)
        reload_from_disk()
        status_var.set(f"Deleted {removed} track(s) from iPod and updated iTunesDB. Safe to eject.")

    tree.bind("<Delete>", delete_selected_tracks)

    # --- Re-read Tags via Mutagen ---
    def reread_selected_tags():
        sel = list(tree.selection())
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        if not sel:
            confirm = messagebox.askyesno(
                "Re-read Tags",
                "No tracks selected. Re-read embedded tags for ALL tracks currently showing 'Unknown Artist' or 'Unknown Album'?",
            )
            if not confirm:
                return
            sel = [
                t.ipod_rel_path
                for t in cached_tracks
                if t.artist in ("Unknown Artist", "") or t.album in ("Unknown Album", "Music", "")
            ]
            if not sel:
                messagebox.showinfo("No Untagged Tracks", "No tracks with 'Unknown Artist' or 'Unknown Album' found.")
                return
        lib = IPodLibrary(Path(p))
        def cb(idx, total, msg):
            status_var.set(f"[{idx}/{total}] {msg}")
            root.update_idletasks()
        updated = lib.re_read_tags_from_files(set(sel), progress_cb=cb)
        reload_from_disk()
        status_var.set(f"Refreshed embedded tags on {updated} track(s) and updated iTunesDB!")

    # --- Convert Existing AIFF Tracks on iPod to ALAC (.m4a) ---
    def convert_selected_aiff_to_alac():
        sel = list(tree.selection())
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        if sel:
            aiff_rels = [
                iid for iid in sel
                if iid in tracks_by_rel and tracks_by_rel[iid].filetype_code.strip() == "AIFF"
            ]
        else:
            aiff_rels = [
                t.ipod_rel_path for t in cached_tracks
                if t.filetype_code.strip() == "AIFF"
            ]
        if not aiff_rels:
            messagebox.showinfo(
                "No AIFF Tracks",
                "No uncompressed AIFF (.aif) tracks found in the current selection (or library).",
            )
            return
        confirm = messagebox.askyesno(
            "Convert AIFF -> ALAC (.m4a)",
            f"Convert {len(aiff_rels)} AIFF track(s) on your iPod to Apple Lossless (.m4a) in-place?\n\n"
            "This preserves 100% bit-perfect lossless audio while freeing ~40–55% disk space and improving battery life.",
        )
        if not confirm:
            return
        lib = IPodLibrary(Path(p))
        def cb(idx, total, msg):
            status_var.set(f"[{idx}/{total}] {msg}")
            root.update_idletasks()
        converted, saved_bytes = lib.convert_aiff_tracks_to_alac(set(aiff_rels), progress_cb=cb)
        reload_from_disk()
        saved_mb = saved_bytes / (1024 * 1024)
        status_var.set(
            f"Converted {converted} AIFF track(s) to ALAC (.m4a) — saved {saved_mb:.1f} MB! iTunesDB updated."
        )

    # --- Transcode MP3 Audiobooks to AAC (.m4b) ---
    def convert_selected_audiobooks_to_m4b():
        sel = list(tree.selection())
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        if sel:
            targets = [
                iid for iid in sel
                if iid in tracks_by_rel and not tracks_by_rel[iid].ipod_rel_path.lower().endswith(".m4b")
            ]
        else:
            targets = [
                t.ipod_rel_path for t in cached_tracks
                if not t.ipod_rel_path.lower().endswith(".m4b")
                and (t.genre and t.genre.lower() == "audiobook")
            ]
        if not targets:
            messagebox.showinfo(
                "No Audiobooks to Transcode",
                "No MP3 audiobooks found to transcode into native .m4b.",
            )
            return
        confirm = messagebox.askyesno(
            "Transcode to AAC Audiobook (.m4b)",
            f"Transcode {len(targets)} audiobook track(s) on your iPod into hardware-compatible AAC (.m4b)?\n\n"
            "This enables the native top-level Audiobooks menu, bookmarking, and variable playback speed on your iPod.",
        )
        if not confirm:
            return
        lib = IPodLibrary(Path(p))
        def cb(idx, total, msg):
            status_var.set(f"[{idx}/{total}] {msg}")
            root.update_idletasks()
        converted, bytes_saved = lib.convert_audiobook_tracks_to_m4b(set(targets), progress_cb=cb)
        reload_from_disk()
        saved_mb = bytes_saved / (1024 * 1024)
        status_var.set(
            f"Transcoded {converted} audiobook(s) to AAC (.m4b) — saved {saved_mb:.1f} MB! Ready in Audiobooks menu."
        )

    # --- Single & Batch/Album Metadata Editor Modal ---
    KEEP_SENTINEL = "<Keep Individual Values>"

    def open_edit_dialog(_event=None):
        sel = list(tree.selection())
        if not sel:
            messagebox.showinfo(
                "No Tracks Selected",
                "Select one track to edit its tags, or select multiple tracks (e.g. an entire album) to batch-edit Artist/Album/Genre/Year.",
            )
            return
        selected_objs = [tracks_by_rel[iid] for iid in sel if iid in tracks_by_rel]
        if not selected_objs:
            return

        is_batch = len(selected_objs) > 1
        dlg = tk.Toplevel(root)
        dlg.title(
            f"HeritagePod — Edit Track Metadata ({selected_objs[0].title})"
            if not is_batch
            else f"HeritagePod — Batch Edit Metadata ({len(selected_objs)} Tracks Selected)"
        )
        dlg.geometry("560x500" if not is_batch else "560x540")
        dlg.transient(root)
        dlg.grab_set()

        frm = ttk.Frame(dlg, padding=16)
        frm.pack(fill=tk.BOTH, expand=True)

        if is_batch:
            info_lbl = ttk.Label(
                frm,
                text=(
                    f"Editing {len(selected_objs)} tracks at once.\n"
                    f"Fields showing '{KEEP_SENTINEL}' will keep each track's existing value unless you type a new value."
                ),
                wraplength=500,
                foreground="#444444",
            )
            info_lbl.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))
        else:
            t0 = selected_objs[0]
            info_lbl = ttk.Label(
                frm,
                text=f"File: {t0.ipod_rel_path}  |  {t0.filetype_code.strip()}  |  {_fmt_duration(t0.duration_ms)}  |  {t0.bitrate_kbps} kbps",
                foreground="#444444",
            )
            info_lbl.grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 10))

        def _shared_val(getter) -> str:
            vals = {str(getter(t)) for t in selected_objs}
            return vals.pop() if len(vals) == 1 else KEEP_SENTINEL

        fields_spec = [
            ("title", "Title:", _shared_val(lambda t: t.title)),
            ("artist", "Artist:", _shared_val(lambda t: t.artist)),
            ("album", "Album:", _shared_val(lambda t: t.album)),
            ("genre", "Genre:", _shared_val(lambda t: t.genre or "")),
            ("composer", "Composer:", _shared_val(lambda t: t.composer or "")),
            ("track_number", "Track #:", _shared_val(lambda t: t.track_number or 0)),
            ("disc_number", "Disc #:", _shared_val(lambda t: t.disc_number or 1)),
            ("year", "Year:", _shared_val(lambda t: t.year or 0)),
        ]

        field_vars: Dict[str, tk.StringVar] = {}
        initial_vals: Dict[str, str] = {}

        for row_idx, (key, label_text, init_val) in enumerate(fields_spec, start=1):
            ttk.Label(frm, text=label_text, width=14).grid(row=row_idx, column=0, sticky=tk.W, pady=4)
            var = tk.StringVar(value=init_val)
            field_vars[key] = var
            initial_vals[key] = init_val
            ent = ttk.Entry(frm, textvariable=var, width=46)
            ent.grid(row=row_idx, column=1, sticky=tk.EW, pady=4, padx=(6, 0))

        frm.columnconfigure(1, weight=1)

        auto_num_var = tk.BooleanVar(value=False)
        strip_num_var = tk.BooleanVar(value=False)
        prefix_album_var = tk.BooleanVar(value=False)
        initial_is_audiobook = all(
            t.ipod_rel_path.lower().endswith(".m4b") or t.filetype_code.strip() == "M4B"
            for t in selected_objs
        )
        audiobook_var = tk.BooleanVar(value=initial_is_audiobook)

        chk_row = len(fields_spec) + 1
        if is_batch:
            ttk.Checkbutton(
                frm,
                text=f"Auto-number tracks sequentially (1..{len(selected_objs)}) in current table order",
                variable=auto_num_var,
            ).grid(row=chk_row, column=0, columnspan=2, sticky=tk.W, pady=(8, 2))
            chk_row += 1

        ttk.Checkbutton(
            frm,
            text="Strip leading track numbers from Titles (e.g. '01 - Song' -> 'Song')",
            variable=strip_num_var,
        ).grid(row=chk_row, column=0, columnspan=2, sticky=tk.W, pady=(4, 4))
        chk_row += 1

        ttk.Checkbutton(
            frm,
            text="Prefix Title with Album/Book name (e.g. 'Project Hail Mary - 01' for Audiobooks)",
            variable=prefix_album_var,
        ).grid(row=chk_row, column=0, columnspan=2, sticky=tk.W, pady=(4, 4))
        chk_row += 1

        ttk.Checkbutton(
            frm,
            text="Audiobook Mode (sets .m4b extension & tags to appear under Audiobooks menu with bookmarking)",
            variable=audiobook_var,
        ).grid(row=chk_row, column=0, columnspan=2, sticky=tk.W, pady=(4, 8))
        chk_row += 1

        def save_changes(_event=None):
            updates = {}
            for key, var in field_vars.items():
                val = var.get().strip()
                if val == KEEP_SENTINEL:
                    continue
                # In batch mode, only apply fields that were either changed or explicitly set
                if is_batch and val == initial_vals[key] and key in ("title", "track_number"):
                    continue
                if key in ("track_number", "disc_number", "year"):
                    if not val.lstrip("-").isdigit():
                        messagebox.showerror("Invalid Number", f"'{key}' must be an integer.", parent=dlg)
                        return
                    updates[key] = int(val)
                else:
                    updates[key] = val

            new_ab = audiobook_var.get()
            set_ab = new_ab if (new_ab != initial_is_audiobook or not is_batch) else None

            p = ipod_var.get().strip()
            lib = IPodLibrary(Path(p))
            count = lib.update_tracks_metadata(
                sel,
                updates,
                auto_number=auto_num_var.get(),
                strip_title_numbers=strip_num_var.get(),
                prefix_album=prefix_album_var.get(),
                set_audiobook=set_ab,
            )
            dlg.destroy()
            reload_from_disk()
            status_var.set(f"Updated metadata on {count} track(s) and rebuilt iTunesDB! Safe to eject.")

        btn_bar = ttk.Frame(frm)
        btn_bar.grid(row=chk_row + 1, column=0, columnspan=2, sticky=tk.E, pady=(12, 0))
        ttk.Button(btn_bar, text="Cancel", command=dlg.destroy).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(btn_bar, text="Save & Update iTunesDB", command=save_changes).pack(side=tk.RIGHT)

        dlg.bind("<Return>", save_changes)
        dlg.bind("<Escape>", lambda _e: dlg.destroy())

    tree.bind("<Double-1>", open_edit_dialog)

    # --- Right-Click Context Menu on Track Table ---
    def mark_audiobook(is_ab: bool):
        sel = list(tree.selection())
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        if not sel:
            messagebox.showinfo("No Tracks Selected", "Please select one or more tracks to change media type.")
            return
        target_name = "Audiobook (.m4b)" if is_ab else "Music (.m4a)"
        confirm = messagebox.askyesno(
            f"Mark as {target_name}",
            f"Convert {len(sel)} selected track(s) to {target_name}?\n\n"
            + ("This sets the .m4b extension, stik=2 atom, and audiobook flags so the track appears in the Audiobooks menu with position bookmarking."
               if is_ab else
               "This renames .m4b back to .m4a and clears audiobook flags so the track appears under standard Music."),
        )
        if not confirm:
            return
        lib = IPodLibrary(Path(p))
        updates = {"genre": "Audiobook"} if is_ab else {}
        count = lib.update_tracks_metadata(sel, updates, set_audiobook=is_ab)
        reload_from_disk()
        status_var.set(f"Marked {count} track(s) as {target_name} and rebuilt iTunesDB!")

    # --- Playlist Operations & Management ---
    def add_selected_to_playlist(target_name: str):
        sel = list(tree.selection())
        if not sel:
            messagebox.showinfo("No Tracks Selected", "Please select one or more tracks to add to the playlist.")
            return
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            return
        lib = IPodLibrary(Path(p))
        lib.load_manifest()
        if target_name not in lib.playlists:
            lib.create_playlist(target_name)
        added = lib.add_to_playlist(target_name, sel)
        lib.save_manifest_and_db()
        reload_from_disk()
        status_var.set(f"Added {added} track(s) to playlist '{target_name}' and updated iTunesDB! Safe to eject.")

    def prompt_new_playlist_and_add_selected():
        sel = list(tree.selection())
        name = simpledialog.askstring("New Playlist", "Enter new playlist name:", parent=root)
        if not name or not name.strip():
            return
        add_selected_to_playlist(name.strip())

    def prompt_add_to_playlist_dialog():
        sel = list(tree.selection())
        if not sel:
            messagebox.showinfo(
                "No Tracks Selected",
                "Please select one or more tracks in the table to add to a playlist.",
            )
            return

        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return

        pl_dlg = tk.Toplevel(root)
        pl_dlg.title("Add Tracks to Playlist")
        pl_dlg.geometry("440x250")
        pl_dlg.transient(root)
        pl_dlg.grab_set()

        frm = ttk.Frame(pl_dlg, padding=16)
        frm.pack(fill=tk.BOTH, expand=True)

        ttk.Label(
            frm,
            text=f"Add {len(sel)} selected track(s) to:",
            font=("TkDefaultFont", 10, "bold"),
        ).pack(anchor=tk.W, pady=(0, 10))

        pl_names = sorted(cached_playlists.keys(), key=lambda s: s.lower())
        mode_var = tk.StringVar(value="existing" if pl_names else "new")
        exist_var = tk.StringVar(value=pl_names[0] if pl_names else "")
        new_name_var = tk.StringVar()

        if pl_names:
            r1 = ttk.Radiobutton(frm, text="Existing Playlist:", variable=mode_var, value="existing")
            r1.pack(anchor=tk.W, pady=(2, 2))
            combo = ttk.Combobox(frm, textvariable=exist_var, values=pl_names, state="readonly", width=30)
            combo.pack(anchor=tk.W, padx=(24, 0), pady=(0, 8))

        r2 = ttk.Radiobutton(frm, text="New Playlist:", variable=mode_var, value="new")
        r2.pack(anchor=tk.W, pady=(2, 2))
        new_entry = ttk.Entry(frm, textvariable=new_name_var, width=32)
        new_entry.pack(anchor=tk.W, padx=(24, 0), pady=(0, 12))
        if not pl_names:
            new_entry.focus()

        def do_add(_event=None):
            mode = mode_var.get()
            if mode == "existing" and pl_names:
                target_name = exist_var.get().strip()
            else:
                target_name = new_name_var.get().strip()
                if not target_name:
                    messagebox.showerror("Invalid Name", "Please enter a name for the new playlist.", parent=pl_dlg)
                    return

            lib = IPodLibrary(Path(p))
            lib.load_manifest()
            if target_name not in lib.playlists:
                lib.create_playlist(target_name)
            added = lib.add_to_playlist(target_name, sel)
            lib.save_manifest_and_db()
            pl_dlg.destroy()
            reload_from_disk()
            status_var.set(f"Added {added} track(s) to playlist '{target_name}' and updated iTunesDB! Safe to eject.")

        btn_bar = ttk.Frame(frm)
        btn_bar.pack(fill=tk.X, pady=(10, 0))
        ttk.Button(btn_bar, text="Cancel", command=pl_dlg.destroy).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(btn_bar, text="Add Tracks", command=do_add).pack(side=tk.RIGHT)
        pl_dlg.bind("<Return>", do_add)
        pl_dlg.bind("<Escape>", lambda _e: pl_dlg.destroy())

    def open_playlist_manager():
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return

        lib = IPodLibrary(Path(p))
        lib.load_manifest()

        pm_dlg = tk.Toplevel(root)
        pm_dlg.title("HeritagePod — Playlist Manager")
        pm_dlg.geometry("860x520")
        pm_dlg.minsize(740, 420)
        pm_dlg.transient(root)
        pm_dlg.grab_set()

        bot_bar = ttk.Frame(pm_dlg, padding=(12, 0, 12, 10))
        bot_bar.pack(fill=tk.X, side=tk.BOTTOM)
        ttk.Label(
            bot_bar,
            text="Playlists appear directly on your iPod under Music > Playlists. Track order is preserved.",
            foreground="#555555",
        ).pack(side=tk.LEFT)
        ttk.Button(bot_bar, text="Close", command=pm_dlg.destroy).pack(side=tk.RIGHT)

        split_frame = ttk.Frame(pm_dlg, padding=(12, 12, 12, 6))
        split_frame.pack(fill=tk.BOTH, expand=True)

        # Left Pane: Playlists
        left_pane = ttk.LabelFrame(split_frame, text="Playlists", padding=8)
        left_pane.pack(side=tk.LEFT, fill=tk.BOTH, expand=False, padx=(0, 8))
        left_pane.configure(width=280)

        pl_listbox_frame = ttk.Frame(left_pane)
        pl_listbox_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        pl_listbox = tk.Listbox(
            pl_listbox_frame,
            height=16,
            selectmode=tk.SINGLE,
            font=("TkDefaultFont", 10),
            exportselection=False,
        )
        pl_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        pl_sb = ttk.Scrollbar(pl_listbox_frame, orient=tk.VERTICAL, command=pl_listbox.yview)
        pl_listbox.configure(yscrollcommand=pl_sb.set)
        pl_sb.pack(side=tk.RIGHT, fill=tk.Y)

        left_btn_bar = ttk.Frame(left_pane, padding=(0, 6, 0, 0))
        left_btn_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # Right Pane: Tracks
        right_pane = ttk.LabelFrame(split_frame, text="Tracks in Playlist", padding=8)
        right_pane.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        pl_tree_frame = ttk.Frame(right_pane)
        pl_tree_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        cols = ("pos", "artist", "title", "album", "time")
        pl_tree = ttk.Treeview(pl_tree_frame, columns=cols, show="headings", height=14, selectmode="extended")
        pl_tree.heading("pos", text="#")
        pl_tree.heading("artist", text="Artist")
        pl_tree.heading("title", text="Title")
        pl_tree.heading("album", text="Album")
        pl_tree.heading("time", text="Time")

        pl_tree.column("pos", width=42, anchor=tk.CENTER)
        pl_tree.column("artist", width=140, anchor=tk.W)
        pl_tree.column("title", width=220, anchor=tk.W)
        pl_tree.column("album", width=150, anchor=tk.W)
        pl_tree.column("time", width=55, anchor=tk.CENTER)

        pl_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        pl_tree_sb = ttk.Scrollbar(pl_tree_frame, orient=tk.VERTICAL, command=pl_tree.yview)
        pl_tree.configure(yscrollcommand=pl_tree_sb.set)
        pl_tree_sb.pack(side=tk.RIGHT, fill=tk.Y)

        right_btn_bar = ttk.Frame(right_pane, padding=(0, 6, 0, 0))
        right_btn_bar.pack(side=tk.BOTTOM, fill=tk.X)

        playlist_names: List[str] = []

        def get_current_selected_playlist() -> Optional[str]:
            cur_idx = pl_listbox.curselection()
            if cur_idx and 0 <= cur_idx[0] < len(playlist_names):
                return playlist_names[cur_idx[0]]
            return None

        def refresh_tracks_pane(_event=None):
            for item in pl_tree.get_children():
                pl_tree.delete(item)
            cur_pl = get_current_selected_playlist()
            if not cur_pl or cur_pl not in lib.playlists:
                right_pane.configure(text="Tracks in Playlist")
                return
            rels = lib.playlists[cur_pl]
            right_pane.configure(text=f"Tracks in '{cur_pl}' ({len(rels)} tracks)")
            by_rel = {t.ipod_rel_path: t for t in lib.tracks}
            for idx, r in enumerate(rels, start=1):
                t = by_rel.get(r)
                if t:
                    pl_tree.insert(
                        "",
                        tk.END,
                        iid=f"{idx}_{r}",
                        values=(idx, t.artist, t.title, t.album, _fmt_duration(t.duration_ms)),
                    )

        pl_listbox.bind("<<ListboxSelect>>", refresh_tracks_pane)

        def populate_playlists(select_name: Optional[str] = None):
            nonlocal playlist_names
            pl_listbox.delete(0, tk.END)
            playlist_names = sorted(lib.playlists.keys(), key=lambda s: s.lower())
            select_idx = 0 if playlist_names else None
            for idx, name in enumerate(playlist_names):
                cnt = len(lib.playlists[name])
                pl_listbox.insert(tk.END, f"{name}  ({cnt})")
                if select_name and name.lower() == select_name.lower():
                    select_idx = idx
            if select_idx is not None and playlist_names:
                pl_listbox.selection_set(select_idx)
                pl_listbox.see(select_idx)
            refresh_tracks_pane()

        # Left Buttons: New, Rename, Delete
        def new_playlist_action():
            name = simpledialog.askstring("New Playlist", "Enter new playlist name:", parent=pm_dlg)
            if not name or not name.strip():
                return
            name = name.strip()
            if name in lib.playlists:
                messagebox.showerror("Error", f"A playlist named '{name}' already exists.", parent=pm_dlg)
                return
            lib.create_playlist(name)
            lib.save_manifest_and_db()
            populate_playlists(select_name=name)
            reload_from_disk()

        def rename_playlist_action():
            cur_pl = get_current_selected_playlist()
            if not cur_pl:
                messagebox.showinfo("Select Playlist", "Please select a playlist to rename.", parent=pm_dlg)
                return
            new_name = simpledialog.askstring("Rename Playlist", "New playlist name:", initialvalue=cur_pl, parent=pm_dlg)
            if not new_name or not new_name.strip() or new_name.strip() == cur_pl:
                return
            new_name = new_name.strip()
            if new_name in lib.playlists:
                messagebox.showerror("Error", f"A playlist named '{new_name}' already exists.", parent=pm_dlg)
                return
            lib.rename_playlist(cur_pl, new_name)
            lib.save_manifest_and_db()
            populate_playlists(select_name=new_name)
            reload_from_disk()

        def delete_playlist_action():
            cur_pl = get_current_selected_playlist()
            if not cur_pl:
                messagebox.showinfo("Select Playlist", "Please select a playlist to delete.", parent=pm_dlg)
                return
            confirm = messagebox.askyesno(
                "Delete Playlist",
                f"Delete playlist '{cur_pl}' from iPod?\n\n(This will NOT delete any songs or audio files from your iPod).",
                parent=pm_dlg,
            )
            if not confirm:
                return
            lib.delete_playlist(cur_pl)
            lib.save_manifest_and_db()
            populate_playlists()
            reload_from_disk()

        ttk.Button(left_btn_bar, text="+ New", width=7, command=new_playlist_action).pack(side=tk.LEFT, padx=2)
        ttk.Button(left_btn_bar, text="Rename", width=8, command=rename_playlist_action).pack(side=tk.LEFT, padx=2)
        ttk.Button(left_btn_bar, text="Delete", width=7, command=delete_playlist_action).pack(side=tk.LEFT, padx=2)

        # Right Buttons: Move Up, Move Down, Remove Track, Add Selected from Library
        def move_track(delta: int):
            cur_pl = get_current_selected_playlist()
            if not cur_pl:
                return
            sel_items = list(pl_tree.selection())
            if not sel_items:
                return
            first_sel = sel_items[0]
            pos_str, rel = first_sel.split("_", 1)
            idx = int(pos_str) - 1
            new_idx = idx + delta
            if new_idx < 0 or new_idx >= len(lib.playlists[cur_pl]):
                return
            lib.reorder_playlist(cur_pl, idx, new_idx)
            lib.save_manifest_and_db()
            refresh_tracks_pane()
            new_iid = f"{new_idx + 1}_{rel}"
            if new_iid in pl_tree.get_children():
                pl_tree.selection_set(new_iid)
                pl_tree.see(new_iid)
            reload_from_disk()

        def remove_selected_from_playlist():
            cur_pl = get_current_selected_playlist()
            if not cur_pl:
                return
            sel_items = list(pl_tree.selection())
            if not sel_items:
                messagebox.showinfo("No Tracks Selected", "Select one or more tracks in the playlist to remove.", parent=pm_dlg)
                return
            rels_to_remove = [item.split("_", 1)[1] for item in sel_items]
            lib.remove_from_playlist(cur_pl, rels_to_remove)
            lib.save_manifest_and_db()
            populate_playlists(select_name=cur_pl)
            reload_from_disk()

        def add_main_table_selection():
            cur_pl = get_current_selected_playlist()
            if not cur_pl:
                messagebox.showinfo("Select Playlist", "Please select a playlist in the left pane first.", parent=pm_dlg)
                return
            main_sel = list(tree.selection())
            if not main_sel:
                messagebox.showinfo(
                    "No Tracks Selected in Library",
                    "To add tracks:\n1. Select tracks in the main library table behind this window.\n2. Click '+ Add from Library Selection' here.",
                    parent=pm_dlg,
                )
                return
            added = lib.add_to_playlist(cur_pl, main_sel)
            lib.save_manifest_and_db()
            populate_playlists(select_name=cur_pl)
            reload_from_disk()
            status_var.set(f"Added {added} track(s) to playlist '{cur_pl}'!")

        ttk.Button(right_btn_bar, text="▲ Up", width=6, command=lambda: move_track(-1)).pack(side=tk.LEFT, padx=2)
        ttk.Button(right_btn_bar, text="▼ Down", width=6, command=lambda: move_track(1)).pack(side=tk.LEFT, padx=2)
        ttk.Button(right_btn_bar, text="Remove Track(s)", command=remove_selected_from_playlist).pack(side=tk.LEFT, padx=6)
        ttk.Button(right_btn_bar, text="+ Add from Library Selection", command=add_main_table_selection).pack(side=tk.RIGHT, padx=2)

        populate_playlists()

    ctx_menu = tk.Menu(root, tearoff=0)
    ctx_menu.add_command(label="Edit Metadata / Tags...", command=open_edit_dialog)
    ctx_menu.add_command(label="Select Entire Album", command=lambda: select_group("album"))
    ctx_menu.add_command(label="Select Entire Artist", command=lambda: select_group("artist"))
    ctx_menu.add_separator()
    pl_cascade_menu = tk.Menu(ctx_menu, tearoff=0)
    ctx_menu.add_cascade(label="Add to Playlist", menu=pl_cascade_menu)
    ctx_menu.add_separator()
    ctx_menu.add_command(label="Mark as Audiobook (.m4b)", command=lambda: mark_audiobook(True))
    ctx_menu.add_command(label="Mark as Music (.m4a)", command=lambda: mark_audiobook(False))
    ctx_menu.add_separator()
    ctx_menu.add_command(label="Re-read Tags from Audio File(s)", command=reread_selected_tags)
    ctx_menu.add_command(label="Convert Selected AIFF -> ALAC (.m4a)", command=convert_selected_aiff_to_alac)
    ctx_menu.add_command(label="Transcode Selected Audiobooks -> AAC (.m4b)", command=convert_selected_audiobooks_to_m4b)
    ctx_menu.add_separator()
    ctx_menu.add_command(label="Delete Selected Track(s)...", command=delete_selected_tracks)

    def show_context_menu(event):
        row_id = tree.identify_row(event.y)
        if row_id and row_id not in tree.selection():
            tree.selection_set(row_id)
        if tree.selection():
            pl_cascade_menu.delete(0, tk.END)
            for pl_name in sorted(cached_playlists.keys(), key=lambda s: s.lower()):
                cnt = len(cached_playlists[pl_name])
                pl_cascade_menu.add_command(
                    label=f"{pl_name}  ({cnt})",
                    command=lambda name=pl_name: add_selected_to_playlist(name),
                )
            if cached_playlists:
                pl_cascade_menu.add_separator()
            pl_cascade_menu.add_command(
                label="+ New Playlist...",
                command=prompt_new_playlist_and_add_selected,
            )
            ctx_menu.tk_popup(event.x_root, event.y_root)

    tree.bind("<Button-3>", show_context_menu)

    # --- Add Folder / Add Files / Rebuild Actions ---
    def add_folder():
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return
        cur_src = source_path_var.get().strip()
        if cur_src and Path(cur_src).is_dir():
            default_music = cur_src
        elif nas_default and nas_default.is_dir():
            default_music = str(nas_default)
        elif (Path(p) / "Music").is_dir():
            default_music = str(Path(p) / "Music")
        else:
            default_music = str(Path.home())
        folder = _pick_directory("Select Album Folder (FLAC / MP3 / AIFF)", default_music)
        if not folder:
            return
        source_path_var.set(folder)
        _run_sync([Path(folder)])

    def add_files():
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return
        if sys.platform.startswith("linux") and shutil.which("zenity"):
            default_music = str(Path(p) / "Music") if (Path(p) / "Music").is_dir() else str(Path.home())
            cmd = [
                "zenity", "--file-selection", "--multiple", "--separator=\n",
                "--title=Select Audio Files",
                f"--filename={default_music.rstrip('/')}/",
                "--file-filter=Audio Files | *.flac *.FLAC *.aiff *.aif *.wav *.mp3 *.m4a *.m4b *.M4A *.M4B *.aac *.AAC",
            ]
            res = subprocess.run(cmd, capture_output=True, text=True)
            if res.returncode != 0 or not res.stdout.strip():
                return
            files = [line.strip() for line in res.stdout.splitlines() if line.strip()]
        else:
            files = filedialog.askopenfilenames(
                title="Select Audio Files",
                filetypes=[("Audio Files", "*.flac *.FLAC *.aiff *.aif *.wav *.mp3 *.m4a *.m4b *.aac")],
            )
        if not files:
            return
        _run_sync([Path(f) for f in files])

    def _run_sync(paths: List[Path]):
        lib = IPodLibrary(Path(ipod_var.get().strip()))
        def cb(idx, total, msg):
            status_var.set(f"[{idx}/{total}] {msg}")
            root.update_idletasks()
        target_fmt = "aiff" if "AIFF" in flac_target_var.get() else "alac"
        added, skipped = lib.add_paths(paths, progress_cb=cb, flac_format=target_fmt)
        reload_from_disk()
        status_var.set(f"Done! Added {added} tracks ({skipped} duplicates skipped). Safe to eject iPod.")

    def rebuild_db_now():
        p = ipod_var.get().strip()
        if not p or not Path(p).is_dir():
            messagebox.showerror("Error", "Please select a valid iPod mount directory first.")
            return
        lib = IPodLibrary(Path(p))
        lib.load_manifest()
        lib.save_manifest_and_db()
        reload_from_disk()
        status_var.set(f"Rebuilt iTunesDB ({len(lib.tracks)} tracks) & flushed to disk! Safe to eject iPod.")

    def eject_ipod_now():
        p = ipod_var.get().strip()
        if not p:
            messagebox.showinfo("Eject iPod", "No iPod mount path specified.")
            return
        mount_path = Path(p)
        if not mount_path.exists():
            messagebox.showinfo("Eject iPod", f"Path does not exist: {mount_path}")
            return
        status_var.set(f"Flushing buffers and ejecting {mount_path}...")
        root.update_idletasks()
        ok, msg = eject_ipod_device(mount_path)
        if ok:
            status_var.set(f"Ejected: {msg}")
            messagebox.showinfo(
                "Safe to Disconnect",
                f"iPod successfully unmounted & ejected:\n\n{msg}\n\nYour iPod screen should now show 'OK to disconnect'.",
            )
            reload_from_disk()
        else:
            status_var.set(f"Eject failed: {msg}")
            messagebox.showerror("Eject Failed", f"Could not cleanly eject iPod:\n\n{msg}")

    reload_from_disk()
    root.mainloop()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="HeritagePod: Dedicated sync, metadata, and playlist manager for vintage iPods without iTunes."
    )
    parser.add_argument(
        "--ipod", "-i",
        type=Path,
        help="Path to mounted iPod root directory (auto-detected if omitted)",
    )
    parser.add_argument(
        "--gui", "-g",
        action="store_true",
        help="Launch the desktop graphical sync window",
    )
    sub = parser.add_subparsers(dest="cmd")

    add_p = sub.add_parser("add", help="Convert & copy folders/files to the iPod and update iTunesDB")
    add_p.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")
    add_p.add_argument(
        "--flac-format",
        choices=["alac", "aiff"],
        default="alac",
        help="Target lossless format when converting FLAC files (default: alac)",
    )
    add_p.add_argument("sources", nargs="+", type=Path, help="FLAC/audio files or album directories")

    conv_p = sub.add_parser("convert-alac", help="Convert existing uncompressed AIFF (.aif) tracks on the iPod to ALAC (.m4a)")
    conv_p.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")

    conv_ab = sub.add_parser("convert-audiobook", help="Transcode MP3 audiobooks on the iPod to AAC .m4b for native Audiobooks menu")
    conv_ab.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")

    list_p = sub.add_parser("list", help="List all tracks currently indexed on the iPod")
    list_p.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")
    eject_p = sub.add_parser("eject", help="Safely flush buffers and unmount/eject the iPod")
    eject_p.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")
    rebuild_p = sub.add_parser("rebuild", help="Instantly rebuild iTunesDB from existing manifest without re-converting")
    rebuild_p.add_argument("--ipod", "-i", type=Path, help="Path to mounted iPod root directory")
    rebuild_p.add_argument("--db-version", type=int, default=0x0B, help="iTunesDB version header (default: 0x0B)")
    rebuild_p.add_argument("--limit", type=int, default=0, help="Write only the first N tracks to iTunesDB (for bisecting)")
    rebuild_p.add_argument("--aiff-only", action="store_true", help="Include only .aif (FLAC-converted) tracks in iTunesDB")

    args = parser.parse_args()

    if args.gui or (args.cmd is None and len(sys.argv) == 1):
        launch_gui(args.ipod)
        return

    ipod_path = args.ipod
    if ipod_path is None:
        detected = detect_mounted_ipods()
        if not detected:
            print("Error: Could not auto-detect a mounted iPod. Pass `--ipod /path/to/ipod`.", file=sys.stderr)
            sys.exit(1)
        ipod_path = detected[0]
        print(f"Auto-detected iPod at: {ipod_path}")

    lib = IPodLibrary(ipod_path)

    if args.cmd == "add":
        def cli_progress(idx: int, total: int, msg: str):
            print(f"[{idx}/{total}] {msg}")
        added, skipped = lib.add_paths(args.sources, progress_cb=cli_progress, flac_format=args.flac_format)
        print(f"\nSuccess: {added} track(s) synced to {ipod_path}, {skipped} skipped.")
        print(f"Updated database: {lib.db_path} ({len(lib.tracks)} total tracks)")
    elif args.cmd == "convert-alac":
        def cli_progress(idx: int, total: int, msg: str):
            print(f"[{idx}/{total}] {msg}")
        converted, saved_bytes = lib.convert_aiff_tracks_to_alac(progress_cb=cli_progress)
        print(
            f"\nSuccess: Converted {converted} AIFF track(s) to ALAC (.m4a) — saved {saved_bytes / (1024 * 1024):.1f} MB."
        )
    elif args.cmd == "convert-audiobook":
        def cli_progress(idx: int, total: int, msg: str):
            print(f"[{idx}/{total}] {msg}")
        converted, saved_bytes = lib.convert_audiobook_tracks_to_m4b(progress_cb=cli_progress)
        print(
            f"\nSuccess: Transcoded {converted} audiobook(s) to AAC (.m4b) — saved {saved_bytes / (1024 * 1024):.1f} MB. Ready in native Audiobooks menu!"
        )
    elif args.cmd == "rebuild":
        lib.load_manifest()
        full_tracks = list(lib.tracks)
        if args.aiff_only:
            lib.tracks = [t for t in lib.tracks if t.ipod_rel_path.lower().endswith(".aif")]
        if args.limit and args.limit > 0:
            lib.tracks = lib.tracks[:args.limit]
        # Write DB with the selected slice, while keeping all tracks in manifest
        selected_tracks = list(lib.tracks)
        lib.tracks = full_tracks
        lib.ensure_structure()
        for idx, t in enumerate(lib.tracks, start=52):
            t.track_id = idx
            if t.artist.startswith("smb-share:") or t.artist in ("gvfs", "1000", "user", "run"):
                t.artist = "Unknown Artist"
            if t.album.startswith("smb-share:") or t.album in ("gvfs", "1000", "user", "run"):
                t.album = "Unknown Album"
        payload = {"tracks": [asdict(t) for t in lib.tracks]}
        lib.manifest_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        db_bytes = build_itunesdb_bytes(selected_tracks, db_version=args.db_version)
        tmp_db = lib.itunes_dir / "iTunesDB.new"
        with open(tmp_db, "wb") as f:
            f.write(db_bytes)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_db, lib.db_path)
        try:
            os.sync()
        except Exception:
            pass
        print(f"Rebuilt {lib.db_path} ({len(selected_tracks)} of {len(full_tracks)} tracks, {len(db_bytes):,} bytes) and flushed disk cache.")
    elif args.cmd == "eject":
        ok, msg = eject_ipod_device(ipod_path)
        if ok:
            print(f"Success: {msg}")
        else:
            print(f"Error: {msg}", file=sys.stderr)
            sys.exit(1)
    elif args.cmd == "list":
        lib.load_manifest()
        print(f"Tracks on iPod ({len(lib.tracks)}):")
        for t in lib.tracks:
            mins, secs = divmod(t.duration_ms // 1000, 60)
            print(f"  [{t.track_id}] {t.artist} - {t.album} - {t.track_number:02d}. {t.title} ({mins}:{secs:02d}, {t.filetype_code.strip()})")
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
