"""Structural loader for `.mmb` files."""
from __future__ import annotations

from dataclasses import dataclass

from .io import BR, check_ptr


@dataclass
class TermEntry:
    """Term metadata entry (mm0-rs `TermEntry`)."""

    num_args: int
    sort: int
    p_args: int


@dataclass
class ThmEntry:
    """Theorem metadata entry (mm0-rs `ThmEntry`)."""

    num_args: int
    p_args: int


@dataclass
class Format:
    """Top-level structure information extracted from an MMB file."""

    num_sorts: int
    num_terms: int
    num_thms: int
    p_terms: int
    p_thms: int
    p_proof: int
    sorts: list[int]
    strings: list[str]
    terms: list[TermEntry]
    thms: list[ThmEntry]


def _cstr(data: bytes, off: int) -> str:
    end = data.find(b"\0", off)
    if end == -1:
        raise ValueError("unterminated string")
    return data[off:end].decode("utf-8")


def load_mmb(data: bytes) -> Format:
    """Parse header, index and declaration tables.

    Mirrors `mm0-rs/src/mmb/import.rs` structure loader.
    """

    n = len(data)
    r = BR(data)
    if r.take(4).tobytes() != b"MM0B":
        raise ValueError("bad magic")
    version = r.u8()
    if version != 1:
        raise ValueError(f"unsupported version {version}")
    num_sorts = r.u8()
    r.take(2)
    num_terms = r.u32()
    num_thms = r.u32()
    p_terms = r.u32()
    p_thms = r.u32()
    p_proof = r.u32()
    r.u32()
    p_index = r.u64()

    sorts = list(r.take(num_sorts).tobytes())

    base = 40 + num_sorts
    if not (base <= p_terms <= p_thms <= p_proof <= n):
        raise ValueError("section offsets out of range")
    for ptr in (p_terms, p_thms, p_proof):
        check_ptr(ptr, 4, 0, n)
    if p_index:
        check_ptr(p_index, 8, 0, n)

    terms: list[TermEntry] = []
    if num_terms:
        check_ptr(p_terms, 4, 8 * num_terms, n)
        tr = BR(data[p_terms:p_thms])
        for _ in range(num_terms):
            num_args = tr.u16()
            sort = tr.u8()
            tr.u8()
            p_args = tr.u32()
            check_ptr(p_args, 8, 8 * (num_args + 1), n)
            terms.append(TermEntry(num_args, sort, p_args))

    thms: list[ThmEntry] = []
    if num_thms:
        check_ptr(p_thms, 4, 8 * num_thms, n)
        tr = BR(data[p_thms:p_proof])
        for _ in range(num_thms):
            num_args = tr.u16()
            tr.u16()
            p_args = tr.u32()
            check_ptr(p_args, 8, 8 * num_args, n)
            thms.append(ThmEntry(num_args, p_args))

    strings: list[str] = []
    if p_index:
        ir = BR(data[p_index:])
        ir.take(8)  # p_root
        name_ptr = 0
        while ir.i + 16 <= ir.n:
            idb = ir.take(4).tobytes()
            ir.u32()
            ptr = ir.u64()
            if idb == b"Name":
                name_ptr = ptr
        if name_ptr:
            count = num_sorts + num_terms + num_thms
            check_ptr(name_ptr, 8, 16 * count, n)
            off = name_ptr
            for _ in range(count):
                off += 8
                p_name = int.from_bytes(data[off:off+8], "little")
                off += 8
                check_ptr(p_name, 1, 1, n)
                strings.append(_cstr(data, p_name))

    return Format(
        num_sorts=num_sorts,
        num_terms=num_terms,
        num_thms=num_thms,
        p_terms=p_terms,
        p_thms=p_thms,
        p_proof=p_proof,
        sorts=sorts,
        strings=strings,
        terms=terms,
        thms=thms,
    )

