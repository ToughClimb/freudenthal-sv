#!/usr/bin/env python3
"""Exact symbolic certificate for the quintic two-tetrahedron transfer.

The two Freudenthal tetrahedra are

    K_H = {0 <= x <= y <= z <= 1},
    K_F = {0 <= y <= x <= z <= 1}.

The script verifies, with exact SymPy arithmetic, polynomial degree,
continuity, zero exterior trace, every broken edge-divergence trace, the two
signed divergence integrals, and the exact squared H1 seminorm.
It also exhausts the interior face pairs of a 2x2x2 Freudenthal grid and
checks the distinguished-edge geometry used to transport the formula.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations, permutations, product

import sympy as sp


x, y, z, tau = sp.symbols("x y z tau")
coordinates = (x, y, z)

K_H = ((0, 0, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1))
K_F = ((0, 0, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1))

direction = sp.Matrix((1, -1, 0))
scalar_h = 630 * (1 - z) * (z - y) ** 2 * x**2
scalar_f = 630 * (1 - z) * (z - x) ** 2 * y**2
psi_h = direction * scalar_h
psi_f = direction * scalar_f


def freudenthal_tetrahedra(shape: tuple[int, int, int] = (2, 2, 2)):
    """Integer-coordinate tetrahedra used to exhaust interior face types."""

    tetrahedra = []
    for cell in product(*(range(length) for length in shape)):
        for order in permutations(range(3)):
            point = list(cell)
            vertices = [tuple(point)]
            for axis in order:
                point = point.copy()
                point[axis] += 1
                vertices.append(tuple(point))
            tetrahedra.append(tuple(vertices))
    return tuple(tetrahedra)


def determinant3(first, second, third) -> int:
    return (
        first[0] * (second[1] * third[2] - second[2] * third[1])
        - first[1] * (second[0] * third[2] - second[2] * third[0])
        + first[2] * (second[0] * third[1] - second[1] * third[0])
    )


def subtract(first, second):
    return tuple(a - b for a, b in zip(first, second, strict=True))


def check_distinguished_edge_geometry() -> int:
    """Check every interior face has exactly one coplanar opposite-face edge."""

    tetrahedra = freudenthal_tetrahedra()
    incidences = defaultdict(list)
    for tet_index, tet in enumerate(tetrahedra):
        for face_vertices in combinations(tet, 3):
            incidences[tuple(sorted(face_vertices))].append(tet_index)

    checked = 0
    for face_vertices, incident in incidences.items():
        if len(incident) != 2:
            continue
        opposite = [
            next(vertex for vertex in tetrahedra[index] if vertex not in face_vertices)
            for index in incident
        ]
        distinguished = []
        for first, second in combinations(face_vertices, 2):
            if determinant3(
                subtract(second, first),
                subtract(opposite[0], first),
                subtract(opposite[1], first),
            ) == 0:
                distinguished.append((first, second))
        assert len(distinguished) == 1
        checked += 1
    assert checked == 72
    return checked


def divergence(vector: sp.Matrix) -> sp.Expr:
    return sp.factor(sum(sp.diff(vector[i], coordinates[i]) for i in range(3)))


div_h = divergence(psi_h)
div_f = divergence(psi_f)


def total_degree(poly: sp.Expr) -> int:
    return sp.Poly(sp.expand(poly), *coordinates).total_degree()


def edge_trace(
    poly: sp.Expr, first: tuple[int, ...], second: tuple[int, ...]
) -> sp.Expr:
    point = tuple(
        first[i] + tau * (second[i] - first[i]) for i in range(3)
    )
    return sp.factor(
        poly.subs({x: point[0], y: point[1], z: point[2]}, simultaneous=True)
    )


def integrate_h(poly: sp.Expr) -> sp.Expr:
    return sp.factor(sp.integrate(poly, (x, 0, y), (y, 0, z), (z, 0, 1)))


def integrate_f(poly: sp.Expr) -> sp.Expr:
    return sp.factor(sp.integrate(poly, (y, 0, x), (x, 0, z), (z, 0, 1)))


def squared_gradient_norm(vector: sp.Matrix) -> sp.Expr:
    return sp.expand(
        sum(
            sp.diff(vector[i], coordinates[j]) ** 2
            for i in range(3)
            for j in range(3)
        )
    )


def main() -> None:
    if not __debug__:
        raise RuntimeError("run certificates without Python -O so assertions remain active")

    # The construction lies in piecewise P5^3 and its divergence in P4.
    assert max(total_degree(component) for component in psi_h) == 5
    assert max(total_degree(component) for component in psi_f) == 5
    assert total_degree(div_h) == 4
    assert total_degree(div_f) == 4

    expected_h = 1260 * x * (1 - z) * (z - y) * (x - y + z)
    expected_f = -1260 * y * (1 - z) * (z - x) * (-x + y + z)
    assert sp.expand(div_h - expected_h) == 0
    assert sp.expand(div_f - expected_f) == 0

    # The vector traces agree on their common face x=y.
    assert all(
        sp.factor((psi_h[i] - psi_f[i]).subs(y, x)) == 0 for i in range(3)
    )

    # Zero trace on every exterior face of the two-tetrahedron patch.
    exterior_substitutions = (
        (psi_h, {x: 0}),
        (psi_h, {z: y}),
        (psi_h, {z: 1}),
        (psi_f, {y: 0}),
        (psi_f, {z: x}),
        (psi_f, {z: 1}),
    )
    for vector, substitution in exterior_substitutions:
        assert all(
            sp.factor(vector[i].subs(substitution)) == 0 for i in range(3)
        )

    # All six edge incidences of each tetrahedron are checked independently.
    checked_edge_incidences = 0
    for tet_vertices, broken_divergence in ((K_H, div_h), (K_F, div_f)):
        for first, second in combinations(tet_vertices, 2):
            assert edge_trace(broken_divergence, first, second) == 0
            checked_edge_incidences += 1
    assert checked_edge_incidences == 12

    mean_h = integrate_h(div_h)
    mean_f = integrate_f(div_f)
    norm_squared = sp.factor(
        integrate_h(squared_gradient_norm(psi_h))
        + integrate_f(squared_gradient_norm(psi_f))
    )
    assert mean_h == 1
    assert mean_f == -1
    assert mean_h + mean_f == 0
    assert norm_squared == sp.Rational(504, 11)
    interior_faces = check_distinguished_edge_geometry()

    print("piecewise velocity degree: 5")
    print("piecewise divergence degree: 4")
    print("divergence on K_H:", div_h)
    print("divergence on K_F:", div_f)
    print("continuity and all six exterior zero traces: exact")
    print("broken edge incidences checked:", checked_edge_incidences)
    print("interior Freudenthal face pairs checked:", interior_faces)
    print("tetrahedron divergence integrals:", mean_h, mean_f)
    print("squared H1 seminorm:", norm_squared)


if __name__ == "__main__":
    main()
