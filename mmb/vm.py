"""Minimal proof VM enforcing stack discipline.

Mirrors the stack shape rules in `mm0-c/mmb.md` for TERM/THM/HYP/DUMMY/REF/SAVE.
Convertibility semantics are deferred to later milestones.
"""
from __future__ import annotations

from .cmd import ProofOp, Cmd


class VMError(Exception):
    """Raised when the proof VM encounters a structural error."""


class ProofVM:
    """Very small interpreter tracking stack depth only."""

    def __init__(self, sym):
        self.sym = sym
        self.stack: list[object] = []

    def step(self, c: Cmd) -> None:
        op, k = c.op, c.data
        if op in (ProofOp.TERM, ProofOp.TERM_SAVE):
            n = self.sym.term_arity[k]
            self._pop(n)
            self._push(1)
        elif op in (ProofOp.THM, ProofOp.THM_SAVE):
            n = self.sym.thm_arity[k]
            self._pop(n)
            self._push(1)
        elif op == ProofOp.REF:
            if k >= len(self.stack):
                raise VMError("ref oob")
            self._push(1)
        elif op == ProofOp.HYP or op == ProofOp.DUMMY:
            self._push(1)
        elif op == ProofOp.SAVE:
            self._dup()
        elif op == ProofOp.END:
            return
        else:
            raise VMError(f"unsupported opcode {int(op):#x}")

    def _pop(self, n: int) -> None:
        if n > len(self.stack):
            raise VMError("stack underflow")
        del self.stack[-n:]

    def _push(self, n: int) -> None:
        self.stack.extend([None] * n)

    def _dup(self) -> None:
        if not self.stack:
            raise VMError("dup on empty stack")
        self.stack.append(self.stack[-1])
