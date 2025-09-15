"""Minimal equality kernel used by the MMB verifier."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Dict

from .ast import Expr


@dataclass
class Eq:
    """A simple equality pair ``lhs ≈ rhs`` of a given sort."""

    lhs: Expr
    rhs: Expr
    sort: int


def refl(e: Expr) -> Eq:
    """Reflexivity."""

    return Eq(e, e, e.sort)


def sym(eq: Eq) -> Eq:
    """Symmetry."""

    return Eq(eq.rhs, eq.lhs, eq.sort)


def trans(p: Eq, q: Eq) -> Eq:
    """Transitivity.``p.rhs`` must equal ``q.lhs``."""

    if p.rhs != q.lhs:
        raise ValueError("trans mismatch")
    return Eq(p.lhs, q.rhs, p.sort)


def cong(term: int, sort: int, eqs: Iterable[Eq]) -> Eq:
    """Congruence for an application of ``term``."""

    lhs_args = [e.lhs for e in eqs]
    rhs_args = [e.rhs for e in eqs]
    lhs = Expr("app", term, tuple(lhs_args), sort)
    rhs = Expr("app", term, tuple(rhs_args), sort)
    return Eq(lhs, rhs, sort)


def unfold(term: int, sort: int, body: Expr, args: Iterable[Expr]) -> Eq:
    """Unfold a definition using the stored body."""

    subst: Dict[int, Expr] = {i: a for i, a in enumerate(args)}
    rhs = _instantiate(body, subst)
    lhs = Expr("app", term, tuple(args), sort)
    return Eq(lhs, rhs, sort)


def _instantiate(expr: Expr, subst: Dict[int, Expr]) -> Expr:
    if expr.kind in ("var", "dummy"):
        return subst.get(expr.index, expr)
    return Expr(
        "app",
        expr.index,
        tuple(_instantiate(a, subst) for a in expr.args),
        expr.sort,
    )

