"""Opcode decoding for MMB streams.

Mirrors command encoding described in `mm0-c/mmb.md`.
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum

from .io import BR


@dataclass(frozen=True)
class Cmd:
    """A decoded command `(op,data)` pair.

    The two high bits of the first byte specify the size of the
    little-endian `data` field (0,8,16,32 bits) while the low six bits
    give the opcode. See `mm0-c/mmb.md` "Encoding and types" table."""

    op: int
    data: int


def read_cmd(r: BR) -> Cmd:
    """Read a single command from ``r``.

    Mirrors `mm0-c/mmb.md` command encoding."""

    b = r.u8()
    tag = (b >> 6) & 0b11
    op = b & 0x3F
    if tag == 0:
        data = 0
    elif tag == 1:
        data = r.u8()
    elif tag == 2:
        data = r.u16()
    else:
        data = r.u32()
    return Cmd(op, data)


class StmtOp(IntEnum):
    END = 0x00
    AXIOM = 0x02
    SORT = 0x04
    TERM = 0x05
    DEF = 0x05  # same value, distinguished by term table
    THM = 0x06
    LOCAL_DEF = 0x0D
    LOCAL_THM = 0x0E


class ProofOp(IntEnum):
    END = 0x00
    TERM = 0x10
    TERM_SAVE = 0x11
    REF = 0x12
    DUMMY = 0x13
    THM = 0x14
    THM_SAVE = 0x15
    HYP = 0x16
    CONV = 0x17
    REFL = 0x18
    SYM = 0x19
    CONG = 0x1A
    UNFOLD = 0x1B
    CONV_CUT = 0x1C
    CONV_SAVE = 0x1E
    SAVE = 0x1F
    SORRY = 0x20


class UnifyOp(IntEnum):
    END = 0x00
    TERM = 0x30
    TERM_SAVE = 0x31
    REF = 0x32
    DUMMY = 0x33
    HYP = 0x36
