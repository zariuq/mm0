"""Minimal proof VM enforcing stack discipline and a small saved heap.

This VM is purposely lightweight; it checks stack effects for TERM/THM/HYP/
DUMMY/REF/SAVE and provides stubs for basic convertibility commands. Commands
that are not yet implemented raise ``VMError`` so tests can assert failure.
"""
from __future__ import annotations

from .ast import Expr
from .cmd import ProofOp, Cmd


class VMError(Exception):
    """Raised when the proof VM encounters a structural error."""


class Equality:
    """Simple equality pair used for convertibility goals."""

    __slots__ = ("lhs", "rhs", "sort")

    def __init__(self, lhs: Expr, rhs: Expr, sort: int):
        self.lhs, self.rhs, self.sort = lhs, rhs, sort


class ProofVM:
    """Very small interpreter tracking stack depth and saved terms."""

    def __init__(self, sym):
        self.sym = sym
        self.stack: list[Expr] = []
        self.saved: list[Expr] = []
        self.conv: list[Equality] = []

    # ------------------------------------------------------------------
    def step(self, c: Cmd) -> None:
        op, k = c.op, c.data
        if op in (ProofOp.TERM, ProofOp.TERM_SAVE):
            n = self.sym.term_arity[k]
            args = self._pop(n)
            e = Expr("app", k, tuple(args), 0)
            self._push(e)
            if op == ProofOp.TERM_SAVE:
                self.saved.append(e)
        elif op in (ProofOp.THM, ProofOp.THM_SAVE):
            n = self.sym.thm_arity[k]
            args = self._pop(n)
            e = Expr("app", k, tuple(args), 0)
            self._push(e)
            if op == ProofOp.THM_SAVE:
                self.saved.append(e)
        elif op == ProofOp.REF:
            try:
                self._push(self.saved[k])
            except IndexError as exc:  # pragma: no cover - tested
                raise VMError("ref oob") from exc
        elif op in (ProofOp.HYP, ProofOp.DUMMY):
            self._push(Expr("var", -1, (), 0))
        elif op == ProofOp.SAVE:
            if not self.stack:
                raise VMError("dup on empty stack")
            self.saved.append(self.stack[-1])
        elif op == ProofOp.REFL:
            e = self._pop1()
            self.conv.append(Equality(e, e, e.sort))
        elif op == ProofOp.SYM:
            eq = self._conv_pop()
            self.conv.append(Equality(eq.rhs, eq.lhs, eq.sort))
        elif op == ProofOp.CONG:
            raise VMError("CONG not implemented")
        elif op == ProofOp.UNFOLD:
            raise VMError("UNFOLD not implemented")
        elif op == ProofOp.CONV_SAVE:
            eq = self._conv_pop()
            self.saved.append(Expr("app", -2, (), eq.sort))
        elif op == ProofOp.CONV_CUT:
            raise VMError("CONV_CUT not implemented")
        elif op == ProofOp.CONV:
            raise VMError("CONV not implemented")
        elif op == ProofOp.END:
            return
        else:  # pragma: no cover - defensive
            raise VMError(f"unsupported opcode {int(op):#x}")

    # ------------------------------------------------------------------
    def _pop(self, n: int) -> list[Expr]:
        if n > len(self.stack):
            raise VMError("stack underflow")
        res = self.stack[-n:]
        del self.stack[-n:]
        return res

    def _pop1(self) -> Expr:
        return self._pop(1)[0]

    def _push(self, e: Expr) -> None:
        self.stack.append(e)

    def _conv_pop(self) -> Equality:
        if not self.conv:
            raise VMError("no conv goal")
        return self.conv.pop()
