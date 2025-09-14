"""High level interface for verifying .mmb files."""
from __future__ import annotations

from pathlib import Path

from .format import load_mmb


def verify_mmb(mm0_path: str, mmb_path: str) -> None:
    data = Path(mmb_path).read_bytes()
    load_mmb(data, strict_align=False)
    # Proof checking not yet implemented
