#!/usr/bin/env python3
"""Exact symbolic checks for the low-degree element-bubble maps.

On the reference tetrahedron with barycentric coordinates

    lambda = (1-x-y-z, x, y, z),

the paper uses, for s=0,1,

    D_s p = div(x*y*z*(1-x-y-z) p),    p in P_s^3.

This script independently verifies that every output has zero integral and
zero trace on all six edges, assembles the exact monomial coefficient matrix,
and proves its ranks are 3 and 12.  It also enumerates the corresponding
edge-vanishing Bernstein monomials to check target dimensions 3 and 12 after
the single mean constraint.
"""

from __future__ import annotations

from itertools import combinations
from math import factorial

import sympy as sp


x, y, z, tau = sp.symbols("x y z tau")
variables = (x, y, z)
lambdas = (1 - x - y - z, x, y, z)
bubble = sp.prod(lambdas)

vertices = (
    (sp.Integer(0), sp.Integer(0), sp.Integer(0)),
    (sp.Integer(1), sp.Integer(0), sp.Integer(0)),
    (sp.Integer(0), sp.Integer(1), sp.Integer(0)),
    (sp.Integer(0), sp.Integer(0), sp.Integer(1)),
)
edges = tuple(combinations(vertices, 2))


def weak_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, parts - 1):
            yield (first,) + tail


def monomials_upto(degree: int) -> list[sp.Expr]:
    return [
        x**i * y**j * z**k
        for total in range(degree + 1)
        for i in range(total + 1)
        for j in range(total - i + 1)
        for k in (total - i - j,)
    ]


def tetrahedron_integral(poly: sp.Expr) -> sp.Rational:
    result = sp.Rational(0)
    for (i, j, k), coefficient in sp.Poly(sp.expand(poly), x, y, z).terms():
        result += coefficient * sp.Rational(
            factorial(i) * factorial(j) * factorial(k),
            factorial(i + j + k + 3),
        )
    return sp.factor(result)


def edge_trace(
    poly: sp.Expr, start: tuple[sp.Expr, ...], end: tuple[sp.Expr, ...]
) -> sp.Expr:
    substitution = {
        variable: (1 - tau) * a + tau * b
        for variable, a, b in zip(variables, start, end, strict=True)
    }
    return sp.factor(sp.expand(poly.subs(substitution)))


def edge_vanishing_bernstein_count(degree: int) -> int:
    """Number of degree-d barycentric monomials supported on >=3 lambdas."""

    return sum(
        sum(entry > 0 for entry in alpha) >= 3
        for alpha in weak_compositions(degree, 4)
    )


def check(s: int, expected_target_dimension: int) -> None:
    scalar_basis = monomials_upto(s)
    output_basis = monomials_upto(s + 3)
    outputs: list[sp.Expr] = []

    for component in range(3):
        for monomial in scalar_basis:
            output = sp.expand(sp.diff(bubble * monomial, variables[component]))
            assert tetrahedron_integral(output) == 0
            assert all(
                edge_trace(output, start, end) == 0 for start, end in edges
            )
            outputs.append(output)

    matrix = sp.Matrix(
        [
            [
                sp.Poly(output, x, y, z).coeff_monomial(row_monomial)
                for output in outputs
            ]
            for row_monomial in output_basis
        ]
    )
    _, pivot_columns = matrix.rref()
    exact_rank = len(pivot_columns)

    # Before imposing zero mean, the edge-vanishing target has one extra
    # dimension.  The integral functional is nonzero (e.g. on the product of
    # any three distinct barycentric coordinates), hence its kernel has
    # codimension one.
    edge_vanishing_dimension = edge_vanishing_bernstein_count(s + 3)
    assert edge_vanishing_dimension - 1 == expected_target_dimension
    assert tetrahedron_integral(lambdas[0] * lambdas[1] * lambdas[2]) != 0

    assert len(outputs) == expected_target_dimension
    assert exact_rank == expected_target_dimension
    print(
        f"s={s}: matrix={matrix.rows}x{matrix.cols}, domain={len(outputs)}, "
        f"edge-zero target before mean={edge_vanishing_dimension}, "
        f"zero-mean target={expected_target_dimension}, exact rank={exact_rank}"
    )


def main() -> None:
    if not __debug__:
        raise RuntimeError("run certificates without Python -O so assertions remain active")
    check(0, 3)
    check(1, 12)
    print("all output edge traces and tetrahedron integrals: exactly zero")


if __name__ == "__main__":
    main()
