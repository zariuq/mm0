"""Structural loader for `.mmb` files."""
from __future__ import annotations

from dataclasses import dataclass

from .io import BR


@dataclass
class Format:
    """Basic metadata extracted from an MMB file."""

    strings: list[str]
    num_sorts: int
    num_terms: int
    num_thms: int


def _cstr(data: bytes, off: int) -> str:
    end = data.find(b"\0", off)
    if end == -1:
        raise ValueError("unterminated string")
    return data[off:end].decode("utf-8")


def load_mmb(data: bytes) -> Format:
    """Parse the MMB header and index names.

    Mirrors `mm0-rs/components/mm0b_parser/src/lib.rs` header parsing.
    """

    r = BR(data)
    if r.take(4).tobytes() != b"MM0B":
        raise ValueError("bad magic")
    version = r.u8()
    if version != 1:
        raise ValueError(f"unsupported version {version}")
    num_sorts = r.u8()
    r.take(2)  # reserved
    num_terms = r.u32()
    num_thms = r.u32()
    p_terms = r.u32()
    p_thms = r.u32()
    p_proof = r.u32()
    r.u32()  # reserved2
    p_index = int.from_bytes(r.take(8), "little")

    n = len(data)
    if not (40 + num_sorts <= p_terms <= p_thms <= p_proof <= n):
        raise ValueError("section offsets out of range")
    if p_index and p_index > n:
        raise ValueError("index out of range")

    strings: list[str] = []
    if p_index:
        ir = BR(data[p_index:])
        ir.take(8)  # p_root, unused
        entries = []
        while ir.i + 16 <= ir.n:
            idb = ir.take(4).tobytes()
            ir.u32()  # data field
            ptr = int.from_bytes(ir.take(8), "little")
            entries.append((idb, ptr))
        name_ptr = next((ptr for (idb, ptr) in entries if idb == b"Name"), 0)
        if name_ptr:
            count = num_sorts + num_terms + num_thms
            end = name_ptr + 16 * count
            if end > n:
                raise ValueError("name table out of range")
            strings = []
            off = name_ptr
            for _ in range(count):
                off += 8  # skip p_proof
                p_name = int.from_bytes(data[off : off + 8], "little")
                off += 8
                if p_name >= n:
                    raise ValueError("name pointer out of range")
                strings.append(_cstr(data, p_name))
    return Format(strings, num_sorts, num_terms, num_thms)

