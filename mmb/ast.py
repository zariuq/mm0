"""Simple in-memory representation of MMB expressions."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple


@dataclass(frozen=True)
class Expr:
    """An expression in the minimal kernel."""
    kind: str  # 'var', 'dummy', or 'app'
    index: int
    args: Tuple['Expr', ...]
    sort: int


@dataclass
class Term:
    name: str
    args: Tuple[int, ...]  # sorts for arguments
    ret: int
    def_body: Expr | None = None
    dummy_sorts: Tuple[int, ...] = ()


@dataclass
class Theorem:
    name: str
    params: Tuple[int, ...]
    hyps: Tuple[Expr, ...]
    concl: Expr
