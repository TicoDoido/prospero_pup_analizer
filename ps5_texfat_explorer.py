#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PS5 TexFAT / exFAT Explorer
---------------------------
Read-only browser/extractor for raw exFAT/TexFAT images such as PS5
ssd0.system / ssd0.system_ex images extracted from a PUP.

- No third-party modules required.
- Does NOT modify the image.
- Supports one or two FATs (TexFAT-style dual FAT).
- Uses VolumeFlags.ActiveFat when two FATs are present.
- Supports FAT-chained and NoFatChain contiguous files/directories.
- Optional PS5 FTP round-trip for SELF .ebin/.bin/.elf/.sprx -> decrypted ELF using ftpsrv.
- Bulk extraction isolates every SELF in a fresh FTP session and retries once on failure.
- English UI with a built-in dark theme.
"""

from __future__ import annotations

import os
import re
import struct
import sys
import traceback
import ftplib
import tempfile
import uuid
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, List, Optional, Tuple

import tkinter as tk
from tkinter import filedialog, messagebox, ttk


APP_TITLE = "PS5 TexFAT Explorer"
EOC_MIN = 0xFFFFFFF8
EXFAT_NAME = b"EXFAT   "
ELF_MAGIC = b"\x7fELF"
SELF_PS5_MAGIC = b"\x54\x14\xF5\xEE"
SELF_PS4_MAGIC = b"\x4F\x15\x3D\x1D"
SELF_EXTENSIONS = {".bin", ".ebin", ".self", ".elf", ".sprx"}


def u16(data: bytes, off: int) -> int:
    return struct.unpack_from("<H", data, off)[0]


def u32(data: bytes, off: int) -> int:
    return struct.unpack_from("<I", data, off)[0]


def u64(data: bytes, off: int) -> int:
    return struct.unpack_from("<Q", data, off)[0]


def human_size(value: int) -> str:
    units = ("B", "KiB", "MiB", "GiB", "TiB")
    n = float(value)
    for unit in units:
        if n < 1024.0 or unit == units[-1]:
            if unit == "B":
                return f"{int(n)} {unit}"
            return f"{n:.2f} {unit}"
        n /= 1024.0
    return f"{value} B"


def exfat_boot_checksum(region_first_11_sectors: bytes, sector_size: int) -> int:
    needed = 11 * sector_size
    if len(region_first_11_sectors) < needed:
        raise ValueError("Boot region is shorter than 11 sectors")

    checksum = 0
    for i in range(needed):
        # VolumeFlags (106,107) and PercentInUse (112) are skipped by exFAT.
        if i in (106, 107, 112):
            continue
        checksum = (((checksum & 1) << 31) | (checksum >> 1))
        checksum = (checksum + region_first_11_sectors[i]) & 0xFFFFFFFF
    return checksum


@dataclass
class BootInfo:
    partition_offset: int
    volume_length: int
    fat_offset: int
    fat_length: int
    cluster_heap_offset: int
    cluster_count: int
    root_cluster: int
    serial: int
    revision: int
    volume_flags: int
    bytes_per_sector_shift: int
    sectors_per_cluster_shift: int
    number_of_fats: int
    drive_select: int
    percent_in_use: int
    sector_size: int
    sectors_per_cluster: int
    cluster_size: int
    boot_signature: int

    @property
    def active_fat(self) -> int:
        if self.number_of_fats != 2:
            return 0
        return self.volume_flags & 1

    @property
    def declared_bytes(self) -> int:
        return self.volume_length * self.sector_size


@dataclass
class FsEntry:
    name: str
    is_dir: bool
    size: int
    valid_size: int
    first_cluster: int
    no_fat_chain: bool
    attributes: int
    parent: Optional["FsEntry"] = None
    children: Optional[List["FsEntry"]] = None
    source_offset: int = 0

    @property
    def path(self) -> str:
        if self.parent is None:
            return "/"
        parts = []
        node: Optional[FsEntry] = self
        while node is not None and node.parent is not None:
            parts.append(node.name)
            node = node.parent
        return "/" + "/".join(reversed(parts))

    @property
    def layout(self) -> str:
        return "contiguous" if self.no_fat_chain else "FAT chain"

    @property
    def type_text(self) -> str:
        if self.is_dir:
            return "Folder"
        ext = Path(self.name).suffix.lower()
        if ext:
            return ext[1:].upper() + " file"
        return "File"


class ExfatImage:
    def __init__(self, path: str):
        self.path = os.path.abspath(path)
        self.fp = open(self.path, "rb")
        self.file_size = os.path.getsize(self.path)
        self.boot = self._read_boot()
        self.main_checksum_valid, self.main_checksum = self._check_boot_region(0)

        backup_offset = 12 * self.boot.sector_size
        self.backup_boot_valid = False
        self.backup_checksum_valid = False
        self.backup_matches_main = False
        self.backup_checksum = None
        try:
            backup = self._read_boot_at(backup_offset)
            self.backup_boot_valid = True
            self.backup_checksum_valid, self.backup_checksum = self._check_boot_region(backup_offset)
            self.backup_matches_main = self._critical_boot_tuple(self.boot) == self._critical_boot_tuple(backup)
        except Exception:
            pass

        self.active_fat_offset = (
            self.boot.fat_offset + self.boot.active_fat * self.boot.fat_length
        ) * self.boot.sector_size
        self.fat_size_bytes = self.boot.fat_length * self.boot.sector_size
        self.heap_offset = self.boot.cluster_heap_offset * self.boot.sector_size

        self.root = FsEntry(
            name="/",
            is_dir=True,
            size=0,
            valid_size=0,
            first_cluster=self.boot.root_cluster,
            no_fat_chain=False,
            attributes=0x10,
            parent=None,
        )

    def close(self) -> None:
        try:
            self.fp.close()
        except Exception:
            pass

    def _read_exact(self, offset: int, size: int) -> bytes:
        if offset < 0 or size < 0:
            raise ValueError("Negative offset/size")
        if offset + size > self.file_size:
            raise EOFError(
                f"Read outside image: 0x{offset:X}+0x{size:X} > 0x{self.file_size:X}"
            )
        self.fp.seek(offset)
        data = self.fp.read(size)
        if len(data) != size:
            raise EOFError(f"Short read at 0x{offset:X}")
        return data

    def _read_boot(self) -> BootInfo:
        return self._read_boot_at(0)

    def _read_boot_at(self, offset: int) -> BootInfo:
        data = self._read_exact(offset, 512)
        if data[3:11] != EXFAT_NAME:
            raise ValueError(f"No EXFAT signature at 0x{offset:X}")
        if u16(data, 0x1FE) != 0xAA55:
            raise ValueError(f"Invalid boot signature at 0x{offset:X}")

        bps_shift = data[0x6C]
        spc_shift = data[0x6D]
        if not (9 <= bps_shift <= 16):
            raise ValueError(f"Invalid BytesPerSectorShift: {bps_shift}")
        if not (0 <= spc_shift <= 25):
            raise ValueError(f"Invalid SectorsPerClusterShift: {spc_shift}")

        sector_size = 1 << bps_shift
        sectors_per_cluster = 1 << spc_shift
        cluster_size = sector_size * sectors_per_cluster

        return BootInfo(
            partition_offset=u64(data, 0x40),
            volume_length=u64(data, 0x48),
            fat_offset=u32(data, 0x50),
            fat_length=u32(data, 0x54),
            cluster_heap_offset=u32(data, 0x58),
            cluster_count=u32(data, 0x5C),
            root_cluster=u32(data, 0x60),
            serial=u32(data, 0x64),
            revision=u16(data, 0x68),
            volume_flags=u16(data, 0x6A),
            bytes_per_sector_shift=bps_shift,
            sectors_per_cluster_shift=spc_shift,
            number_of_fats=data[0x6E],
            drive_select=data[0x6F],
            percent_in_use=data[0x70],
            sector_size=sector_size,
            sectors_per_cluster=sectors_per_cluster,
            cluster_size=cluster_size,
            boot_signature=u16(data, 0x1FE),
        )

    @staticmethod
    def _critical_boot_tuple(b: BootInfo) -> Tuple[int, ...]:
        return (
            b.partition_offset,
            b.volume_length,
            b.fat_offset,
            b.fat_length,
            b.cluster_heap_offset,
            b.cluster_count,
            b.root_cluster,
            b.serial,
            b.revision,
            b.bytes_per_sector_shift,
            b.sectors_per_cluster_shift,
            b.number_of_fats,
        )

    def _check_boot_region(self, offset: int) -> Tuple[bool, int]:
        sector = self.boot.sector_size
        data = self._read_exact(offset, 12 * sector)
        calc = exfat_boot_checksum(data[: 11 * sector], sector)
        checksum_sector = data[11 * sector : 12 * sector]
        stored = u32(checksum_sector, 0)
        repeated = all(
            u32(checksum_sector, i) == stored
            for i in range(0, len(checksum_sector), 4)
        )
        return (calc == stored and repeated), stored

    def cluster_offset(self, cluster: int) -> int:
        if cluster < 2 or cluster > self.boot.cluster_count + 1:
            raise ValueError(f"Invalid cluster 0x{cluster:X}")
        return self.heap_offset + (cluster - 2) * self.boot.cluster_size

    def fat_next(self, cluster: int) -> int:
        off = self.active_fat_offset + cluster * 4
        if off + 4 > self.active_fat_offset + self.fat_size_bytes:
            raise ValueError(f"FAT index outside FAT: cluster 0x{cluster:X}")
        return u32(self._read_exact(off, 4), 0)

    def iter_chain(self, first_cluster: int, max_clusters: Optional[int] = None):
        if first_cluster < 2:
            return
        seen = set()
        cluster = first_cluster
        count = 0
        max_allowed = max_clusters or (self.boot.cluster_count + 2)

        while 2 <= cluster < EOC_MIN:
            if cluster in seen:
                raise ValueError(f"FAT loop detected at cluster 0x{cluster:X}")
            if count >= max_allowed:
                raise ValueError("FAT chain exceeds safe cluster limit")
            seen.add(cluster)
            yield cluster
            count += 1
            nxt = self.fat_next(cluster)
            if nxt == 0 or nxt >= EOC_MIN:
                break
            cluster = nxt

    def read_entry_bytes(self, entry: FsEntry, limit: Optional[int] = None) -> bytes:
        total = entry.size
        if limit is not None:
            total = min(total, limit)
        if total <= 0:
            return b""

        chunks = []
        remaining = total
        if entry.no_fat_chain:
            off = self.cluster_offset(entry.first_cluster)
            available = min(remaining, self.file_size - off)
            if available < remaining:
                raise EOFError(
                    f"{entry.path}: data extends past EOF "
                    f"(need 0x{remaining:X}, have 0x{available:X})"
                )
            return self._read_exact(off, remaining)

        for cluster in self.iter_chain(entry.first_cluster):
            if remaining <= 0:
                break
            off = self.cluster_offset(cluster)
            take = min(self.boot.cluster_size, remaining)
            chunks.append(self._read_exact(off, take))
            remaining -= take

        if remaining:
            raise EOFError(f"{entry.path}: FAT chain ended 0x{remaining:X} bytes early")
        return b"".join(chunks)

    def _read_directory_data(self, entry: FsEntry) -> bytes:
        if entry.parent is None:
            chunks = []
            for cluster in self.iter_chain(entry.first_cluster):
                chunks.append(self._read_exact(self.cluster_offset(cluster), self.boot.cluster_size))
            return b"".join(chunks)

        return self.read_entry_bytes(entry)

    def list_dir(self, entry: FsEntry) -> List[FsEntry]:
        if not entry.is_dir:
            raise ValueError("Not a directory")
        if entry.children is not None:
            return entry.children

        raw = self._read_directory_data(entry)
        children: List[FsEntry] = []
        pos = 0

        while pos + 32 <= len(raw):
            etype = raw[pos]
            if etype == 0x00:
                break

            if etype != 0x85:
                pos += 32
                continue

            secondary_count = raw[pos + 1]
            set_size = (1 + secondary_count) * 32
            if pos + set_size > len(raw):
                break

            attrs = u16(raw, pos + 4)
            stream = None
            names: List[str] = []

            for n in range(1, secondary_count + 1):
                soff = pos + n * 32
                stype = raw[soff]
                if stype == 0xC0:
                    stream = raw[soff : soff + 32]
                elif stype == 0xC1:
                    name_raw = raw[soff + 2 : soff + 32]
                    names.append(name_raw.decode("utf-16le", errors="replace"))

            if stream is not None:
                name_length = stream[3]
                full_name = "".join(names)[:name_length]
                full_name = full_name.rstrip("\x00")

                flags = stream[1]
                valid_size = u64(stream, 8)
                first_cluster = u32(stream, 20)
                data_length = u64(stream, 24)

                if full_name:
                    child = FsEntry(
                        name=full_name,
                        is_dir=bool(attrs & 0x10),
                        size=data_length,
                        valid_size=valid_size,
                        first_cluster=first_cluster,
                        no_fat_chain=bool(flags & 0x02),
                        attributes=attrs,
                        parent=entry,
                        source_offset=pos,
                    )
                    children.append(child)

            pos += set_size

        children.sort(key=lambda x: (not x.is_dir, x.name.casefold()))
        entry.children = children
        return children

    def write_entry_to_file(
        self,
        entry: FsEntry,
        destination: str,
        progress: Optional[Callable[[int, int], None]] = None,
    ) -> None:
        total = entry.size
        done = 0
        os.makedirs(os.path.dirname(destination) or ".", exist_ok=True)

        with open(destination, "wb") as out:
            if total == 0:
                return

            if entry.no_fat_chain:
                src_off = self.cluster_offset(entry.first_cluster)
                remaining = total
                chunk_size = 4 * 1024 * 1024
                while remaining:
                    take = min(chunk_size, remaining)
                    data = self._read_exact(src_off, take)
                    out.write(data)
                    src_off += take
                    remaining -= take
                    done += take
                    if progress:
                        progress(done, total)
                return

            remaining = total
            for cluster in self.iter_chain(entry.first_cluster):
                if remaining <= 0:
                    break
                take = min(self.boot.cluster_size, remaining)
                out.write(self._read_exact(self.cluster_offset(cluster), take))
                remaining -= take
                done += take
                if progress:
                    progress(done, total)

            if remaining:
                raise EOFError(f"{entry.path}: FAT chain ended early")


def safe_windows_name(name: str) -> str:
    # Keep extraction usable on Windows without changing ordinary PS5 names.
    cleaned = re.sub(r'[<>:"/\\|?*\x00-\x1F]', "_", name)
    cleaned = cleaned.rstrip(" .")
    if not cleaned:
        cleaned = "_unnamed"
    reserved = {
        "CON", "PRN", "AUX", "NUL",
        *(f"COM{i}" for i in range(1, 10)),
        *(f"LPT{i}" for i in range(1, 10)),
    }
    stem = cleaned.split(".", 1)[0].upper()
    if stem in reserved:
        cleaned = "_" + cleaned
    return cleaned



class Ps5FtpRoundTrip:
    """One FTP connection to ps5-payload-dev/ftpsrv.

    ftpsrv enables SELF->ELF conversion by default on every new connection.
    IMPORTANT: the custom `SELF` command is a toggle, so this client does not
    send it automatically. A successful round-trip is verified by ELF magic.
    """

    def __init__(
        self,
        host: str,
        port: int = 2121,
        username: str = "",
        password: str = "",
        remote_dir: str = "/data/ps5_texfat_explorer",
        timeout: float = 20.0,
        passive: bool = True,
    ):
        self.host = host.strip()
        self.port = int(port)
        self.username = username
        self.password = password
        self.remote_dir = self._normalize_remote_dir(remote_dir)
        self.timeout = timeout
        self.passive = passive
        self.ftp: Optional[ftplib.FTP] = None

    @staticmethod
    def _normalize_remote_dir(path: str) -> str:
        path = (path or "/data/ps5_texfat_explorer").replace("\\", "/")
        if not path.startswith("/"):
            path = "/" + path
        path = re.sub(r"/+", "/", path).rstrip("/")
        return path or "/data/ps5_texfat_explorer"

    def connect(self) -> str:
        if not self.host:
            raise ValueError("Enter the PS5 IP address/host in FTP settings.")
        self.close()
        ftp = ftplib.FTP()
        ftp.connect(self.host, self.port, timeout=self.timeout)
        user = self.username or "anonymous"
        passwd = self.password if self.username else "anonymous@"
        welcome = ftp.login(user=user, passwd=passwd)
        ftp.set_pasv(self.passive)
        self.ftp = ftp
        self._ensure_remote_dir()
        return welcome

    def close(self) -> None:
        ftp, self.ftp = self.ftp, None
        if ftp is None:
            return
        try:
            ftp.quit()
        except Exception:
            try:
                ftp.close()
            except Exception:
                pass

    def _require(self) -> ftplib.FTP:
        if self.ftp is None:
            raise RuntimeError("FTP is not connected")
        return self.ftp

    def _ensure_remote_dir(self) -> None:
        ftp = self._require()
        # Build /data/ps5_texfat_explorer one component at a time. Existing
        # directories usually return 550, which is harmless here.
        current = ""
        for part in [p for p in self.remote_dir.split("/") if p]:
            current += "/" + part
            try:
                ftp.mkd(current)
            except ftplib.error_perm:
                pass
        # Verify the resulting path is actually accessible.
        old = ftp.pwd()
        try:
            ftp.cwd(self.remote_dir)
        finally:
            try:
                ftp.cwd(old)
            except Exception:
                ftp.cwd("/")

    def noop(self) -> str:
        return self._require().voidcmd("NOOP")

    def roundtrip_self(
        self,
        raw_path: str,
        final_path: str,
        original_name: str,
        progress: Optional[Callable[[str, int, int], None]] = None,
    ) -> Tuple[int, int, str]:
        """Upload SELF to /data, RETR it back, and require ELF output.

        Returns (uploaded_size, downloaded_size, remote_path).
        The remote temporary file is deleted whether the operation succeeds or
        fails. The local final_path is atomically replaced only after validation.
        """
        ftp = self._require()
        uploaded_size = os.path.getsize(raw_path)
        ext = Path(original_name).suffix.lower()
        if ext not in SELF_EXTENSIONS:
            ext = ".self"
        clean_stem = re.sub(r"[^A-Za-z0-9._-]+", "_", Path(original_name).stem)[:80] or "self"
        remote_name = f"ps5te_{uuid.uuid4().hex}_{clean_stem}{ext}"
        remote_path = self.remote_dir + "/" + remote_name

        sent = 0
        got = 0
        part_path = final_path + ".ps5ftp.part"

        def upload_cb(block: bytes):
            nonlocal sent
            sent += len(block)
            if progress:
                progress("upload", sent, uploaded_size)

        try:
            with open(raw_path, "rb") as src:
                ftp.storbinary(f"STOR {remote_path}", src, blocksize=256 * 1024, callback=upload_cb)

            # SELF decryption is enabled by default on a fresh ftpsrv connection.
            # Do NOT send the `SELF` command here because it toggles the state.
            try:
                remote_size = ftp.size(remote_path)
            except Exception:
                remote_size = None

            with open(part_path, "wb") as out:
                def download_cb(block: bytes):
                    nonlocal got
                    out.write(block)
                    got += len(block)
                    if progress:
                        progress("download", got, remote_size or max(got, 1))

                ftp.retrbinary(f"RETR {remote_path}", download_cb, blocksize=256 * 1024)

            with open(part_path, "rb") as chk:
                magic = chk.read(4)
            if magic != ELF_MAGIC:
                if magic in (SELF_PS5_MAGIC, SELF_PS4_MAGIC):
                    raise RuntimeError(
                        "ftpsrv returned an encrypted SELF instead of an ELF. "
                        "Use an ftpsrv build with SELF->ELF support and a supported firmware; "
                        "do not send the SELF command manually before the test because it is a toggle."
                    )
                raise RuntimeError(
                    f"The returned file is not an ELF (magic={magic.hex(' ').upper() or 'empty'})."
                )

            os.makedirs(os.path.dirname(final_path) or ".", exist_ok=True)
            os.replace(part_path, final_path)
            return uploaded_size, got, remote_path
        finally:
            try:
                if os.path.exists(part_path):
                    os.remove(part_path)
            except Exception:
                pass
            try:
                ftp.delete(remote_path)
            except Exception:
                pass


class ExplorerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1280x820")
        self.minsize(1000, 620)
        self._apply_dark_theme()

        self.image: Optional[ExfatImage] = None
        self.current_dir: Optional[FsEntry] = None
        self.history: List[FsEntry] = []
        self.history_pos = -1

        self.tree_nodes: Dict[str, FsEntry] = {}
        self.list_nodes: Dict[str, FsEntry] = {}

        self.path_var = tk.StringVar(value="No image opened")
        self.search_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Open a PS5 .img/.bin image to begin.")

        # Optional PS5 FTP SELF->ELF round-trip. The current ftpsrv defaults
        # SELF decryption to enabled for each new connection.
        self.ftp_decrypt_var = tk.BooleanVar(value=False)
        self.ftp_host_var = tk.StringVar(value="")
        self.ftp_port_var = tk.StringVar(value="2121")
        self.ftp_user_var = tk.StringVar(value="")
        self.ftp_pass_var = tk.StringVar(value="")
        self.ftp_remote_dir_var = tk.StringVar(value="/data/ps5_texfat_explorer")
        self.ftp_passive_var = tk.BooleanVar(value=True)
        self.ftp_keep_raw_on_error_var = tk.BooleanVar(value=True)
        self.ftp_status_var = tk.StringVar(value="PS5 FTP: disabled")

        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def _apply_dark_theme(self):
        """Apply a consistent dark palette to Tk and ttk widgets."""
        bg = "#15171a"
        panel = "#1d2024"
        field = "#24282d"
        field_alt = "#2a2f35"
        fg = "#e8eaed"
        muted = "#aeb4bc"
        accent = "#4f8cff"
        select = "#315f9e"
        border = "#343a40"
        disabled = "#737980"

        self._dark = {
            "bg": bg,
            "panel": panel,
            "field": field,
            "field_alt": field_alt,
            "fg": fg,
            "muted": muted,
            "accent": accent,
            "select": select,
            "border": border,
            "disabled": disabled,
        }

        self.configure(background=bg)
        try:
            self.option_add("*TCombobox*Listbox.background", field)
            self.option_add("*TCombobox*Listbox.foreground", fg)
            self.option_add("*TCombobox*Listbox.selectBackground", select)
            self.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")
        except Exception:
            pass

        style = ttk.Style(self)
        # 'clam' allows field/background colors to be controlled reliably on Windows.
        if "clam" in style.theme_names():
            style.theme_use("clam")

        style.configure(".", background=bg, foreground=fg)
        style.configure("TFrame", background=bg)
        style.configure("TLabel", background=bg, foreground=fg)
        style.configure("Muted.TLabel", background=bg, foreground=muted)
        style.configure("TLabelFrame", background=bg, foreground=fg, bordercolor=border)
        style.configure("TLabelFrame.Label", background=bg, foreground=fg)

        style.configure(
            "TButton",
            background=field_alt,
            foreground=fg,
            bordercolor=border,
            focusthickness=1,
            focuscolor=accent,
            padding=(8, 5),
        )
        style.map(
            "TButton",
            background=[("active", "#343a42"), ("pressed", "#20242a"), ("disabled", panel)],
            foreground=[("disabled", disabled)],
        )

        style.configure(
            "TCheckbutton",
            background=bg,
            foreground=fg,
            indicatorbackground=field,
            indicatorforeground=fg,
            bordercolor=border,
        )
        style.map(
            "TCheckbutton",
            background=[("active", bg)],
            foreground=[("disabled", disabled)],
            indicatorbackground=[("selected", accent), ("!selected", field)],
        )

        style.configure(
            "TEntry",
            fieldbackground=field,
            foreground=fg,
            insertcolor=fg,
            bordercolor=border,
            lightcolor=border,
            darkcolor=border,
        )
        style.map(
            "TEntry",
            fieldbackground=[("readonly", panel), ("disabled", panel)],
            foreground=[("readonly", fg), ("disabled", disabled)],
        )

        style.configure(
            "Treeview",
            background=field,
            fieldbackground=field,
            foreground=fg,
            bordercolor=border,
            rowheight=25,
        )
        style.map(
            "Treeview",
            background=[("selected", select)],
            foreground=[("selected", "#ffffff")],
        )
        style.configure(
            "Treeview.Heading",
            background=panel,
            foreground=fg,
            bordercolor=border,
            relief="flat",
            padding=(6, 5),
        )
        style.map("Treeview.Heading", background=[("active", field_alt)])

        style.configure("TPanedwindow", background=bg)
        style.configure("TSeparator", background=border)
        style.configure(
            "Horizontal.TProgressbar",
            background=accent,
            troughcolor=field,
            bordercolor=border,
            lightcolor=accent,
            darkcolor=accent,
        )
        style.configure(
            "Vertical.TScrollbar",
            background=field_alt,
            troughcolor=panel,
            bordercolor=border,
            arrowcolor=fg,
        )
        style.configure(
            "Horizontal.TScrollbar",
            background=field_alt,
            troughcolor=panel,
            bordercolor=border,
            arrowcolor=fg,
        )

    def _style_toplevel(self, win: tk.Toplevel) -> None:
        win.configure(background=self._dark["bg"])

    def _build_ui(self):
        toolbar = ttk.Frame(self, padding=(6, 6, 6, 3))
        toolbar.pack(fill="x")

        ttk.Button(toolbar, text="Open image", command=self.open_image).pack(side="left")
        ttk.Separator(toolbar, orient="vertical").pack(side="left", fill="y", padx=6)
        self.back_btn = ttk.Button(toolbar, text="← Back", command=self.go_back, state="disabled")
        self.back_btn.pack(side="left")
        self.up_btn = ttk.Button(toolbar, text="↑ Up", command=self.go_up, state="disabled")
        self.up_btn.pack(side="left", padx=(4, 0))

        ttk.Separator(toolbar, orient="vertical").pack(side="left", fill="y", padx=6)
        ttk.Button(toolbar, text="Extract selected", command=self.extract_selection).pack(side="left")
        ttk.Button(toolbar, text="Extract current folder", command=self.extract_current).pack(side="left", padx=(4, 0))
        ttk.Button(toolbar, text="Extract all", command=self.extract_all).pack(side="left", padx=(4, 0))
        ttk.Button(toolbar, text="Preview", command=self.preview_selected).pack(side="left", padx=(4, 0))
        ttk.Button(toolbar, text="Info", command=self.show_image_info).pack(side="left", padx=(4, 0))

        address = ttk.Frame(self, padding=(6, 3))
        address.pack(fill="x")
        ttk.Label(address, text="Location:").pack(side="left")
        entry = ttk.Entry(address, textvariable=self.path_var, state="readonly")
        entry.pack(side="left", fill="x", expand=True, padx=(6, 12))

        ttk.Label(address, text="Filter:").pack(side="left")
        search = ttk.Entry(address, textvariable=self.search_var, width=28)
        search.pack(side="left", padx=(6, 0))
        self.search_var.trace_add("write", lambda *_: self.refresh_file_list())

        # Dedicated FTP/SELF panel. Kept on its own row so Windows DPI/scaling
        # cannot hide it beyond the edge of the main toolbar.
        ftp_bar = ttk.LabelFrame(self, text="PS5 FTP / SELF → ELF", padding=(8, 5))
        ftp_bar.pack(fill="x", padx=6, pady=(2, 4))

        def sync_ftp_status(*_args):
            host = self.ftp_host_var.get().strip() or "IP not configured"
            port = self.ftp_port_var.get().strip() or "?"
            if self.ftp_decrypt_var.get():
                self.ftp_status_var.set(f"ENABLED — {host}:{port} — temp: {self.ftp_remote_dir_var.get()}")
            else:
                self.ftp_status_var.set(f"disabled — {host}:{port}")

        ttk.Checkbutton(
            ftp_bar,
            text="Decrypt .ELF/.SPRX through PS5 during extraction",
            variable=self.ftp_decrypt_var,
            command=sync_ftp_status,
        ).pack(side="left")

        ttk.Separator(ftp_bar, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(ftp_bar, text="IP:").pack(side="left")
        ttk.Entry(ftp_bar, textvariable=self.ftp_host_var, width=16).pack(side="left", padx=(4, 8))
        ttk.Label(ftp_bar, text="Port:").pack(side="left")
        ttk.Entry(ftp_bar, textvariable=self.ftp_port_var, width=7).pack(side="left", padx=(4, 8))
        ttk.Button(ftp_bar, text="Configure / Test FTP...", command=self.show_ftp_settings).pack(side="left")
        ttk.Label(ftp_bar, textvariable=self.ftp_status_var).pack(side="left", padx=(12, 0), fill="x", expand=True)

        self.ftp_host_var.trace_add("write", sync_ftp_status)
        self.ftp_port_var.trace_add("write", sync_ftp_status)
        self.ftp_remote_dir_var.trace_add("write", sync_ftp_status)
        sync_ftp_status()

        pane = ttk.Panedwindow(self, orient="horizontal")
        pane.pack(fill="both", expand=True, padx=6, pady=4)

        left = ttk.Frame(pane)
        right = ttk.Frame(pane)
        pane.add(left, weight=1)
        pane.add(right, weight=3)

        ttk.Label(left, text="Folders").pack(anchor="w", pady=(0, 4))
        tree_frame = ttk.Frame(left)
        tree_frame.pack(fill="both", expand=True)
        self.folder_tree = ttk.Treeview(tree_frame, show="tree", selectmode="browse")
        ty = ttk.Scrollbar(tree_frame, orient="vertical", command=self.folder_tree.yview)
        self.folder_tree.configure(yscrollcommand=ty.set)
        self.folder_tree.pack(side="left", fill="both", expand=True)
        ty.pack(side="right", fill="y")
        self.folder_tree.bind("<<TreeviewOpen>>", self.on_tree_open)
        self.folder_tree.bind("<<TreeviewSelect>>", self.on_tree_select)

        ttk.Label(right, text="Contents").pack(anchor="w", pady=(0, 4))
        list_frame = ttk.Frame(right)
        list_frame.pack(fill="both", expand=True)

        columns = ("type", "size", "cluster", "layout")
        self.file_list = ttk.Treeview(
            list_frame,
            columns=columns,
            show="tree headings",
            selectmode="extended",
        )
        self.file_list.heading("#0", text="Name")
        self.file_list.heading("type", text="Type")
        self.file_list.heading("size", text="Size")
        self.file_list.heading("cluster", text="First cluster")
        self.file_list.heading("layout", text="Layout")

        self.file_list.column("#0", width=390, minwidth=180)
        self.file_list.column("type", width=115, minwidth=80)
        self.file_list.column("size", width=120, minwidth=90, anchor="e")
        self.file_list.column("cluster", width=105, minwidth=80, anchor="e")
        self.file_list.column("layout", width=110, minwidth=90)

        ly = ttk.Scrollbar(list_frame, orient="vertical", command=self.file_list.yview)
        lx = ttk.Scrollbar(list_frame, orient="horizontal", command=self.file_list.xview)
        self.file_list.configure(yscrollcommand=ly.set, xscrollcommand=lx.set)

        self.file_list.grid(row=0, column=0, sticky="nsew")
        ly.grid(row=0, column=1, sticky="ns")
        lx.grid(row=1, column=0, sticky="ew")
        list_frame.rowconfigure(0, weight=1)
        list_frame.columnconfigure(0, weight=1)

        self.file_list.bind("<Double-1>", self.on_double_click)
        self.file_list.bind("<Return>", self.on_enter)
        self.file_list.bind("<BackSpace>", lambda _e: self.go_up())

        status = ttk.Frame(self, padding=(6, 3, 6, 6))
        status.pack(fill="x")
        ttk.Label(status, textvariable=self.status_var).pack(side="left", fill="x", expand=True)

    def show_ftp_settings(self):
        win = tk.Toplevel(self)
        self._style_toplevel(win)
        win.title("PS5 FTP — SELF → ELF")
        win.geometry("560x390")
        win.resizable(False, False)
        win.transient(self)

        frame = ttk.Frame(win, padding=12)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(1, weight=1)

        ttk.Checkbutton(
            frame,
            text="Automatically decrypt .elf/.sprx during extraction",
            variable=self.ftp_decrypt_var,
        ).grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 12))

        fields = [
            ("PS5 IP / host:", self.ftp_host_var),
            ("FTP port:", self.ftp_port_var),
            ("Username:", self.ftp_user_var),
            ("Password:", self.ftp_pass_var),
            ("Temporary folder on PS5:", self.ftp_remote_dir_var),
        ]
        for row, (label, var) in enumerate(fields, start=1):
            ttk.Label(frame, text=label).grid(row=row, column=0, sticky="w", pady=4)
            show = "*" if label == "Password:" else ""
            ttk.Entry(frame, textvariable=var, show=show).grid(
                row=row, column=1, columnspan=2, sticky="ew", padx=(10, 0), pady=4
            )

        ttk.Checkbutton(frame, text="Passive FTP", variable=self.ftp_passive_var).grid(
            row=6, column=1, sticky="w", pady=(8, 2)
        )
        ttk.Checkbutton(
            frame,
            text="If decryption fails, preserve the raw SELF as .self",
            variable=self.ftp_keep_raw_on_error_var,
        ).grid(row=7, column=0, columnspan=3, sticky="w", pady=(2, 10))

        note = (
            "Current ftpsrv builds use port 2121 by default. SELF→ELF is already enabled on "
            "each new connection; the Explorer does not send the SELF command because it toggles the state."
        )
        ttk.Label(frame, text=note, wraplength=520, style="Muted.TLabel").grid(
            row=8, column=0, columnspan=3, sticky="w", pady=(4, 12)
        )

        result_var = tk.StringVar(value="")
        ttk.Label(frame, textvariable=result_var).grid(
            row=9, column=0, columnspan=3, sticky="w", pady=(0, 8)
        )

        def test_connection():
            result_var.set("Connecting...")
            win.update_idletasks()
            client = None
            try:
                client = self._make_ftp_client()
                welcome = client.connect()
                try:
                    pwd = client._require().pwd()
                except Exception:
                    pwd = "?"
                result_var.set(f"OK — connected. PWD={pwd}")
            except Exception as e:
                result_var.set(f"Failed: {e}")
            finally:
                if client:
                    client.close()

        buttons = ttk.Frame(frame)
        buttons.grid(row=10, column=0, columnspan=3, sticky="e")
        ttk.Button(buttons, text="Test connection", command=test_connection).pack(side="left")
        ttk.Button(buttons, text="Close", command=win.destroy).pack(side="left", padx=(8, 0))

    def _make_ftp_client(self) -> Ps5FtpRoundTrip:
        host = self.ftp_host_var.get().strip()
        if not host:
            raise ValueError("Enter the PS5 IP address/host in PS5 FTP settings.")
        try:
            port = int(self.ftp_port_var.get().strip())
        except ValueError:
            raise ValueError("Invalid FTP port")
        if not (1 <= port <= 65535):
            raise ValueError("FTP port must be between 1 and 65535")
        return Ps5FtpRoundTrip(
            host=host,
            port=port,
            username=self.ftp_user_var.get(),
            password=self.ftp_pass_var.get(),
            remote_dir=self.ftp_remote_dir_var.get(),
            passive=self.ftp_passive_var.get(),
        )

    @staticmethod
    def _local_file_magic(path: str) -> bytes:
        with open(path, "rb") as f:
            return f.read(4)

    @staticmethod
    def _needs_ps5_self_roundtrip(entry: FsEntry, raw_path: str) -> bool:
        if Path(entry.name).suffix.lower() not in SELF_EXTENSIONS:
            return False
        try:
            magic = ExplorerApp._local_file_magic(raw_path)
        except Exception:
            return False
        return magic in (SELF_PS5_MAGIC, SELF_PS4_MAGIC)

    def on_close(self):
        if self.image:
            self.image.close()
        self.destroy()

    def open_image(self):
        path = filedialog.askopenfilename(
            title="Open TexFAT/exFAT image",
            filetypes=[
                ("Raw images", "*.img *.bin"),
                ("All files", "*.*"),
            ],
        )
        if not path:
            return

        try:
            img = ExfatImage(path)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not open the image:\n\n{e}")
            return

        if self.image:
            self.image.close()
        self.image = img
        self.current_dir = img.root
        self.history = [img.root]
        self.history_pos = 0

        self.tree_nodes.clear()
        self.list_nodes.clear()
        self.folder_tree.delete(*self.folder_tree.get_children())

        root_iid = self.folder_tree.insert("", "end", text="/", open=True)
        self.tree_nodes[root_iid] = img.root
        self._populate_tree_node(root_iid, img.root)
        self.folder_tree.selection_set(root_iid)

        self._show_directory(img.root, add_history=False)
        self._update_nav()
        self.status_var.set(
            f"{os.path.basename(path)} — {human_size(img.file_size)} — "
            f"TexFAT/exFAT — active FAT #{img.boot.active_fat + 1}"
        )

    def _populate_tree_node(self, iid: str, entry: FsEntry):
        if not self.image:
            return
        # Clear dummy or old children.
        for child_iid in self.folder_tree.get_children(iid):
            self.folder_tree.delete(child_iid)
            self.tree_nodes.pop(child_iid, None)

        try:
            children = self.image.list_dir(entry)
        except Exception as e:
            self.status_var.set(f"Error reading {entry.path}: {e}")
            return

        for child in children:
            if not child.is_dir:
                continue
            ci = self.folder_tree.insert(iid, "end", text=child.name)
            self.tree_nodes[ci] = child
            # Lazy-load marker.
            self.folder_tree.insert(ci, "end", text="...")

    def on_tree_open(self, _event=None):
        iid = self.folder_tree.focus()
        entry = self.tree_nodes.get(iid)
        if entry:
            self._populate_tree_node(iid, entry)

    def on_tree_select(self, _event=None):
        sel = self.folder_tree.selection()
        if not sel:
            return
        entry = self.tree_nodes.get(sel[0])
        if entry and entry is not self.current_dir:
            self._show_directory(entry, add_history=True)

    def _show_directory(self, entry: FsEntry, add_history: bool = True):
        if not self.image:
            return
        try:
            self.image.list_dir(entry)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Could not read folder:\n{entry.path}\n\n{e}")
            return

        self.current_dir = entry
        self.path_var.set(entry.path)
        if add_history:
            if self.history_pos + 1 < len(self.history):
                self.history = self.history[: self.history_pos + 1]
            self.history.append(entry)
            self.history_pos = len(self.history) - 1
        self.refresh_file_list()
        self._select_tree_for_entry(entry)
        self._update_nav()

    def refresh_file_list(self):
        self.file_list.delete(*self.file_list.get_children())
        self.list_nodes.clear()

        if not self.image or not self.current_dir:
            return

        try:
            children = self.image.list_dir(self.current_dir)
        except Exception as e:
            self.status_var.set(str(e))
            return

        needle = self.search_var.get().casefold().strip()
        shown = 0
        total_size = 0

        for child in children:
            if needle and needle not in child.name.casefold():
                continue
            size_text = "" if child.is_dir else human_size(child.size)
            cluster_text = f"0x{child.first_cluster:X}" if child.first_cluster else "-"
            iid = self.file_list.insert(
                "",
                "end",
                text=child.name,
                values=(child.type_text, size_text, cluster_text, child.layout),
            )
            self.list_nodes[iid] = child
            shown += 1
            if not child.is_dir:
                total_size += child.size

        self.status_var.set(
            f"{shown} item(s) — visible files: {human_size(total_size)} — "
            f"{self.current_dir.path}"
        )

    def _select_tree_for_entry(self, target: FsEntry):
        for iid, entry in self.tree_nodes.items():
            if entry is target:
                try:
                    self.folder_tree.selection_set(iid)
                    self.folder_tree.see(iid)
                except tk.TclError:
                    pass
                return

    def _update_nav(self):
        self.back_btn.configure(state=("normal" if self.history_pos > 0 else "disabled"))
        self.up_btn.configure(
            state=("normal" if self.current_dir and self.current_dir.parent else "disabled")
        )

    def go_back(self):
        if self.history_pos <= 0:
            return
        self.history_pos -= 1
        self._show_directory(self.history[self.history_pos], add_history=False)
        self._update_nav()

    def go_up(self):
        if self.current_dir and self.current_dir.parent:
            self._show_directory(self.current_dir.parent, add_history=True)

    def on_double_click(self, _event=None):
        sel = self.file_list.selection()
        if not sel:
            return
        entry = self.list_nodes.get(sel[0])
        if not entry:
            return
        if entry.is_dir:
            self._show_directory(entry, add_history=True)
        else:
            self.preview_entry(entry)

    def on_enter(self, _event=None):
        self.on_double_click()

    def selected_entries(self) -> List[FsEntry]:
        result = []
        for iid in self.file_list.selection():
            entry = self.list_nodes.get(iid)
            if entry:
                result.append(entry)
        return result

    def preview_selected(self):
        entries = self.selected_entries()
        if len(entries) != 1 or entries[0].is_dir:
            messagebox.showinfo(APP_TITLE, "Select exactly one file to preview.")
            return
        self.preview_entry(entries[0])

    def preview_entry(self, entry: FsEntry):
        if not self.image:
            return
        try:
            data = self.image.read_entry_bytes(entry, limit=256 * 1024)
        except Exception as e:
            messagebox.showerror(APP_TITLE, f"Failed to read {entry.path}:\n\n{e}")
            return

        win = tk.Toplevel(self)
        self._style_toplevel(win)
        win.title(f"Preview — {entry.name}")
        win.geometry("900x650")

        info = ttk.Label(
            win,
            text=(
                f"{entry.path}    |    {human_size(entry.size)}    |    "
                f"cluster 0x{entry.first_cluster:X}    |    {entry.layout}"
            ),
            padding=6,
        )
        info.pack(fill="x")

        text = tk.Text(
            win, wrap="none", font=("Consolas", 10),
            background=self._dark["field"], foreground=self._dark["fg"],
            insertbackground=self._dark["fg"], selectbackground=self._dark["select"],
            selectforeground="#ffffff", relief="flat", borderwidth=0,
        )
        y = ttk.Scrollbar(win, orient="vertical", command=text.yview)
        x = ttk.Scrollbar(win, orient="horizontal", command=text.xview)
        text.configure(yscrollcommand=y.set, xscrollcommand=x.set)
        text.pack(side="left", fill="both", expand=True)
        y.pack(side="right", fill="y")
        x.pack(side="bottom", fill="x")

        printable = sum(1 for b in data if b in (9, 10, 13) or 0x20 <= b <= 0x7E)
        ratio = printable / max(1, len(data))

        if ratio >= 0.85:
            try:
                content = data.decode("utf-8")
            except UnicodeDecodeError:
                content = data.decode("latin-1", errors="replace")
            text.insert("1.0", content)
        else:
            lines = []
            for off in range(0, len(data), 16):
                chunk = data[off : off + 16]
                hx = " ".join(f"{b:02X}" for b in chunk)
                asc = "".join(chr(b) if 0x20 <= b <= 0x7E else "." for b in chunk)
                lines.append(f"{off:08X}  {hx:<47}  {asc}")
            text.insert("1.0", "\n".join(lines))

        if entry.size > len(data):
            text.insert(
                "end",
                f"\n\n--- Preview limited to the first {human_size(len(data))} "
                f"of {human_size(entry.size)} ---",
            )
        text.configure(state="disabled")

    def extract_selection(self):
        entries = self.selected_entries()
        if not entries:
            messagebox.showinfo(APP_TITLE, "Select one or more files/folders.")
            return
        dest = filedialog.askdirectory(title="Choose destination folder")
        if not dest:
            return
        self._extract_entries(entries, dest)

    def extract_current(self):
        if not self.current_dir:
            return
        dest = filedialog.askdirectory(title="Extract current folder to...")
        if not dest:
            return
        base = os.path.join(dest, safe_windows_name(
            self.current_dir.name if self.current_dir.parent else "root"
        ))
        os.makedirs(base, exist_ok=True)
        try:
            entries = self.image.list_dir(self.current_dir) if self.image else []
            self._extract_entries(entries, base)
        except Exception as e:
            messagebox.showerror(APP_TITLE, str(e))

    def extract_all(self):
        if not self.image:
            return
        dest = filedialog.askdirectory(title="Extract entire image to...")
        if not dest:
            return
        base = os.path.join(dest, Path(self.image.path).stem + "_extracted")
        os.makedirs(base, exist_ok=True)
        try:
            entries = self.image.list_dir(self.image.root)
            self._extract_entries(entries, base)
        except Exception as e:
            messagebox.showerror(APP_TITLE, str(e))

    def _extract_entries(self, entries: List[FsEntry], dest_root: str):
        if not self.image:
            return

        errors: List[str] = []
        file_count = 0
        decrypted_count = 0
        already_plain_count = 0
        raw_fallback_count = 0
        ftp_retry_count = 0
        ftp_enabled = bool(self.ftp_decrypt_var.get())

        # IMPORTANT FOR BULK EXTRACTION:
        #
        # Older versions kept one FTP connection alive for the complete recursive
        # extraction. If ftpsrv rejected/aborted one SELF transfer, that shared
        # control session could be left unusable and every later SELF would fail
        # on the same stale connection.
        #
        # V4 only validates the configuration here. Every actual SELF conversion
        # below gets its OWN fresh connection. This also guarantees ftpsrv starts
        # each file with its default SELF->ELF state enabled.
        if ftp_enabled:
            test_client: Optional[Ps5FtpRoundTrip] = None
            try:
                test_client = self._make_ftp_client()
                test_client.connect()
                test_client.noop()
            except Exception as e:
                messagebox.showerror(
                    APP_TITLE,
                    "PS5-assisted extraction is enabled, but the FTP connection failed:\n\n"
                    f"{e}\n\nOpen 'Configure / Test FTP...' and check the IP/port.",
                )
                return
            finally:
                if test_client:
                    test_client.close()

        progress_win = tk.Toplevel(self)
        self._style_toplevel(progress_win)
        progress_win.title("Extracting")
        progress_win.geometry("680x175")
        progress_win.transient(self)
        progress_win.grab_set()

        label_var = tk.StringVar(value="Preparing...")
        detail_var = tk.StringVar(value="")
        ttk.Label(progress_win, textvariable=label_var, padding=(10, 10, 10, 4)).pack(fill="x")
        bar = ttk.Progressbar(progress_win, maximum=100)
        bar.pack(fill="x", padx=10, pady=4)
        ttk.Label(progress_win, textvariable=detail_var, padding=(10, 3, 10, 8)).pack(fill="x")

        cancelled = {"value": False}

        def cancel():
            cancelled["value"] = True

        ttk.Button(progress_win, text="Cancel", command=cancel).pack(pady=(0, 8))

        def extract_one(entry: FsEntry, parent_dir: str):
            nonlocal file_count, decrypted_count, already_plain_count
            nonlocal raw_fallback_count, ftp_retry_count

            if cancelled["value"]:
                return

            name = safe_windows_name(entry.name)
            target = os.path.join(parent_dir, name)

            if entry.is_dir:
                os.makedirs(target, exist_ok=True)
                try:
                    children = self.image.list_dir(entry)
                except Exception as e:
                    errors.append(f"{entry.path}: {e}")
                    return
                for child in children:
                    extract_one(child, target)
                    if cancelled["value"]:
                        return
                return

            label_var.set(f"Extracting: {entry.path}")
            detail_var.set(f"{human_size(entry.size)} — {entry.layout}")
            bar["value"] = 0
            progress_win.update_idletasks()

            def local_prog(done: int, total: int):
                if total:
                    bar["value"] = done * 100.0 / total
                progress_win.update_idletasks()

            # We only need a temporary raw file for extensions that *might* be a
            # SELF. Magic is checked locally before opening a PS5 FTP connection.
            use_ftp_candidate = (
                ftp_enabled and Path(entry.name).suffix.lower() in SELF_EXTENSIONS
            )

            raw_path = target
            temp_raw = None
            if use_ftp_candidate:
                fd, temp_raw = tempfile.mkstemp(
                    prefix="ps5_texfat_self_", suffix=Path(entry.name).suffix.lower()
                )
                os.close(fd)
                raw_path = temp_raw

            try:
                self.image.write_entry_to_file(entry, raw_path, local_prog)

                if not use_ftp_candidate:
                    file_count += 1
                    return

                magic = self._local_file_magic(raw_path)

                if magic == ELF_MAGIC:
                    # Some files may already be plaintext in the image.
                    os.makedirs(os.path.dirname(target) or ".", exist_ok=True)
                    os.replace(raw_path, target)
                    temp_raw = None
                    already_plain_count += 1
                    file_count += 1
                    return

                if magic not in (SELF_PS5_MAGIC, SELF_PS4_MAGIC):
                    # Extension looks executable but it is neither SELF nor ELF.
                    # Preserve it exactly as stored in the image. Crucially, this
                    # does NOT touch the FTP state for any later file.
                    os.makedirs(os.path.dirname(target) or ".", exist_ok=True)
                    os.replace(raw_path, target)
                    temp_raw = None
                    file_count += 1
                    return

                label_var.set(f"PS5 SELF→ELF: {entry.path}")

                last_error: Optional[Exception] = None
                converted = False

                # One fresh connection per SELF. Retry once with another completely
                # new connection if the first transfer/decryption fails.
                for attempt in (1, 2):
                    if cancelled["value"]:
                        return

                    client: Optional[Ps5FtpRoundTrip] = None
                    try:
                        client = self._make_ftp_client()
                        detail_var.set(
                            f"Opening fresh FTP session for SELF "
                            f"(attempt {attempt}/2)..."
                        )
                        progress_win.update_idletasks()
                        client.connect()

                        def ftp_prog(stage: str, done: int, total: int):
                            if stage == "upload":
                                detail_var.set(
                                    f"Attempt {attempt}/2 — Uploading SELF to "
                                    f"{client.remote_dir} — "
                                    f"{human_size(done)} / {human_size(total)}"
                                )
                            else:
                                detail_var.set(
                                    f"Attempt {attempt}/2 — Downloading decrypted ELF — "
                                    f"{human_size(done)}"
                                    + (f" / {human_size(total)}" if total else "")
                                )
                            if total:
                                bar["value"] = done * 100.0 / total
                            else:
                                bar["value"] = 0
                            progress_win.update_idletasks()

                        client.roundtrip_self(raw_path, target, entry.name, ftp_prog)
                        converted = True
                        if attempt == 2:
                            ftp_retry_count += 1
                        break

                    except Exception as e:
                        last_error = e
                        if attempt == 1:
                            detail_var.set(
                                "First SELF→ELF attempt failed; retrying with a "
                                "brand-new FTP connection..."
                            )
                            progress_win.update_idletasks()
                    finally:
                        if client:
                            client.close()

                if converted:
                    decrypted_count += 1
                    file_count += 1
                    return

                # Both isolated attempts failed. Preserve only THIS file as raw;
                # the next SELF will still get its own clean FTP connection.
                if self.ftp_keep_raw_on_error_var.get():
                    fallback = target + ".self"
                    os.makedirs(os.path.dirname(fallback) or ".", exist_ok=True)
                    os.replace(raw_path, fallback)
                    temp_raw = None
                    raw_fallback_count += 1
                    file_count += 1
                    errors.append(
                        f"{entry.path}: SELF→ELF failed twice "
                        f"({last_error}); raw SELF saved as {fallback}"
                    )
                else:
                    errors.append(
                        f"{entry.path}: SELF→ELF failed twice: {last_error}"
                    )

            except Exception as e:
                errors.append(f"{entry.path}: {e}")
            finally:
                if temp_raw:
                    try:
                        os.remove(temp_raw)
                    except Exception:
                        pass

        try:
            os.makedirs(dest_root, exist_ok=True)
            for entry in entries:
                extract_one(entry, dest_root)
                if cancelled["value"]:
                    break
        finally:
            try:
                progress_win.grab_release()
                progress_win.destroy()
            except Exception:
                pass

        summary = (
            f"Files completed: {file_count}\n"
            f"SELF→ELF via PS5: {decrypted_count}\n"
            f"Already plain ELF: {already_plain_count}"
        )
        if ftp_retry_count:
            summary += f"\nSELF→ELF succeeded on retry: {ftp_retry_count}"
        if raw_fallback_count:
            summary += f"\nRaw SELF preserved after two failures: {raw_fallback_count}"

        if cancelled["value"]:
            messagebox.showwarning(APP_TITLE, f"Extraction cancelled.\n\n{summary}")
        elif errors:
            sample = "\n".join(errors[:12])
            more = "" if len(errors) <= 12 else f"\n... and {len(errors)-12} more error(s)"
            messagebox.showwarning(
                APP_TITLE,
                f"Extraction completed with warnings/errors.\n\n{summary}\n"
                f"Errors: {len(errors)}\n\n{sample}{more}",
            )
        else:
            messagebox.showinfo(APP_TITLE, f"Extraction completed.\n\n{summary}")


    def show_image_info(self):
        if not self.image:
            messagebox.showinfo(APP_TITLE, "No image is open.")
            return

        img = self.image
        b = img.boot
        short = max(0, b.declared_bytes - img.file_size)

        text = (
            f"File:\n{img.path}\n\n"
            f"Physical size: 0x{img.file_size:X} ({human_size(img.file_size)})\n"
            f"Declared size: 0x{b.declared_bytes:X} ({human_size(b.declared_bytes)})\n"
            f"Omitted tail: 0x{short:X} ({human_size(short)})\n\n"
            f"Sector: 0x{b.sector_size:X} bytes\n"
            f"Cluster: 0x{b.cluster_size:X} bytes ({human_size(b.cluster_size)})\n"
            f"Clusters: 0x{b.cluster_count:X}\n"
            f"Root cluster: 0x{b.root_cluster:X}\n\n"
            f"FATs: {b.number_of_fats}\n"
            f"Active FAT: #{b.active_fat + 1}\n"
            f"VolumeFlags: 0x{b.volume_flags:04X}\n"
            f"Serial: 0x{b.serial:08X}\n\n"
            f"Main boot checksum: {'VALID' if img.main_checksum_valid else 'INVALID'} "
            f"(0x{img.main_checksum:08X})\n"
            f"Backup boot: {'present' if img.backup_boot_valid else 'missing/invalid'}\n"
            f"Backup checksum: {'VALID' if img.backup_checksum_valid else 'INVALID'}\n"
            f"Main/Backup critical fields: {'match' if img.backup_matches_main else 'differ'}\n\n"
            f"Version: Dark FTP v4\n"
            f"Mode: READ ONLY"
        )
        messagebox.showinfo("Image information", text)


def main():
    app = ExplorerApp()

    # Optional image path on command line.
    if len(sys.argv) >= 2:
        path = sys.argv[1]
        if os.path.isfile(path):
            try:
                img = ExfatImage(path)
                app.image = img
                app.current_dir = img.root
                app.history = [img.root]
                app.history_pos = 0

                root_iid = app.folder_tree.insert("", "end", text="/", open=True)
                app.tree_nodes[root_iid] = img.root
                app._populate_tree_node(root_iid, img.root)
                app.folder_tree.selection_set(root_iid)
                app._show_directory(img.root, add_history=False)
                app._update_nav()
            except Exception:
                traceback.print_exc()

    app.mainloop()


if __name__ == "__main__":
    main()
