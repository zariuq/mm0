"""Proof bytecode interpreter for MMB proofs.

This is a very small subset implementing only enough for structural tests.
"""
from __future__ import annotations

from .ast import Expr, Term, Theorem


class VM:
    def __init__(self, terms: list[Term], theorems: list[Theorem]):
        self.terms = terms
        self.theorems = theorems
        self.stack: list[Expr] = []
        self.heap: list[Expr] = []

    def exec(self, cmd: int, data: int) -> None:
        raise NotImplementedError
