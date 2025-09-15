"""Proof VM with basic convertibility handling."""
from __future__ import annotations

from dataclasses import dataclass
from typing import List

from .ast import Expr
from .cmd import ProofOp, Cmd
from .kernel import Eq, refl, sym as ksym, trans as ktrans, cong as kcong, unfold as kunfold


class VMError(Exception):
    """Raised when the proof VM encounters a structural error."""


@dataclass
class SavedTerm:
    expr: Expr


@dataclass
class SavedEq:
    eq: Eq


Saved = SavedTerm | SavedEq


class ProofVM:
    """Interpreter for proof commands enforcing stack and convertibility rules."""

    def __init__(self, sym):
        self.sym = sym
        self.tstack: List[Expr] = []
        self.cstack: List[Eq] = []
        self.saved: List[Saved] = []
        self.goal: Eq | None = None

    # ---------------------------------------------------------------
    def step(self, c: Cmd) -> None:
        op, k = c.op, c.data
        if op in (ProofOp.TERM, ProofOp.TERM_SAVE):
            n = self.sym.term_arity[k]
            args = self._pop_terms(n)
            e = Expr("app", k, tuple(args), 0)
            self.tstack.append(e)
            if op == ProofOp.TERM_SAVE:
                self.saved.append(SavedTerm(e))
        elif op in (ProofOp.THM, ProofOp.THM_SAVE):
            n = self.sym.thm_arity[k]
            args = self._pop_terms(n)
            e = Expr("app", k, tuple(args), 0)
            self.tstack.append(e)
            if op == ProofOp.THM_SAVE:
                self.saved.append(SavedTerm(e))
        elif op == ProofOp.REF:
            try:
                s = self.saved[k]
            except IndexError as exc:  # pragma: no cover - tested
                raise VMError("ref oob") from exc
            if isinstance(s, SavedTerm):
                self.tstack.append(s.expr)
            else:
                self.cstack.append(s.eq)
        elif op in (ProofOp.HYP, ProofOp.DUMMY):
            self.tstack.append(Expr("var", -1, (), 0))
        elif op == ProofOp.SAVE:
            if not self.tstack:
                raise VMError("dup on empty stack")
            top = self.tstack[-1]
            self.saved.append(SavedTerm(top))
        elif op == ProofOp.REFL:
            e = self._pop_term()
            self.cstack.append(refl(e))
        elif op == ProofOp.SYM:
            self.cstack.append(ksym(self._pop_eq()))
        elif op == ProofOp.CONG:
            n = self.sym.term_arity[k]
            eqs = self._pop_eqs(n)
            self.cstack.append(kcong(k, 0, eqs))
        elif op == ProofOp.UNFOLD:
            n = self.sym.term_arity[k]
            args = self._pop_terms(n)
            body = self.sym.term_defs[k]
            if body is None:
                raise VMError("UNFOLD on non-def")
            self.cstack.append(kunfold(k, 0, body, args))
        elif op == ProofOp.CONV_SAVE:
            self.saved.append(SavedEq(self._pop_eq()))
        elif op == ProofOp.CONV_CUT:
            p2 = self._pop_eq()
            p1 = self._pop_eq()
            self.cstack.append(ktrans(p1, p2))
        elif op == ProofOp.CONV:
            eq = self._pop_eq()
            if self.goal is None:
                self.goal = eq
            else:
                self.goal = ktrans(self.goal, eq)
        elif op == ProofOp.END:
            return
        else:  # pragma: no cover - defensive
            raise VMError(f"unsupported opcode {int(op):#x}")

    # ---------------------------------------------------------------
    def finish(self, require_goal: bool = True) -> None:
        if self.cstack:
            raise VMError("pending conv goals")
        if require_goal and (self.goal is None or self.goal.lhs != self.goal.rhs):
            raise VMError("goal not discharged")

    # Helpers -------------------------------------------------------
    def _pop_terms(self, n: int) -> List[Expr]:
        if n > len(self.tstack):
            raise VMError("stack underflow")
        res = self.tstack[-n:]
        del self.tstack[-n:]
        return res

    def _pop_term(self) -> Expr:
        return self._pop_terms(1)[0]

    def _pop_eq(self) -> Eq:
        if not self.cstack:
            raise VMError("no conv goal")
        return self.cstack.pop()

    def _pop_eqs(self, n: int) -> List[Eq]:
        if n > len(self.cstack):
            raise VMError("no conv goal")
        res = self.cstack[-n:]
        del self.cstack[-n:]
        return res

