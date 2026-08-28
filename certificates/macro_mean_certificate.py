#!/usr/bin/env python3
"""Exact verification of the quartic two-cube macro lemma.

This file is intentionally self-contained and uses only Python's standard
library.  It assembles the actual map on

    [C^0 P_4([0,2] x [0,1]^2)]^3 intersect H^1_0

over the twelve-tetrahedron Freudenthal mesh.  ``E`` evaluates the broken
divergence at all P3 edge-skeleton nodes (tetrahedron incidences are kept
separate), and ``M`` contains the twelve element integrals of the divergence.

Two unrelated scalar bases are assembled:

* globally glued Bernstein coefficients; and
* globally glued equispaced Lagrange nodal values.

All entries, eliminations, nullspaces, and determinants are over Q using
``fractions.Fraction``.  In Bernstein coordinates the script verifies the
eleven explicit three-coefficient fields and their determinant -6 from the
manuscript.  It also constructs a basis of ker(E) and checks the full image.
"""

from __future__ import annotations

import json
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
from math import factorial
from typing import Dict, Iterable, Iterator, List, Mapping, Sequence, Tuple


Point = Tuple[int, int, int]
RationalPoint = Tuple[Fraction, Fraction, Fraction]
MultiIndex = Tuple[int, int, int, int]
SparseRow = Dict[int, Fraction]

SHAPE: Point = (2, 1, 1)
K = 4


def weak_compositions(total: int, parts: int) -> Iterator[Tuple[int, ...]]:
    """Weak compositions in the fixed order used throughout the assembly."""

    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, parts - 1):
            yield (first,) + tail


def tetrahedra(shape: Point) -> Iterator[Tuple[Point, Tuple[int, int, int]]]:
    """The six monotone-chain tetrahedra in every Cartesian cube."""

    for cell in product(*(range(n) for n in shape)):
        for sigma in permutations(range(3)):
            yield tuple(cell), tuple(sigma)  # type: ignore[misc]


def vertices(cell: Point, sigma: Tuple[int, int, int]) -> Tuple[Point, ...]:
    current = list(cell)
    result = [tuple(current)]
    for axis in sigma:
        current = current.copy()
        current[axis] += 1
        result.append(tuple(current))
    return tuple(result)  # type: ignore[return-value]


def gradients(sigma: Tuple[int, int, int]) -> Tuple[RationalPoint, ...]:
    """Exact gradients of the four barycentric coordinates.

    On a translated Freudenthal tetrahedron they are obtained from
    lambda=(1-x_s0, x_s0-x_s1, x_s1-x_s2, x_s2).
    """

    result = [[Fraction(0) for _ in range(3)] for _ in range(4)]
    result[0][sigma[0]] = -1
    result[1][sigma[0]] = 1
    result[1][sigma[1]] = -1
    result[2][sigma[1]] = 1
    result[2][sigma[2]] = -1
    result[3][sigma[2]] = 1
    return tuple(tuple(row) for row in result)  # type: ignore[return-value]


def physical_node(
    tet_vertices: Sequence[Point], alpha: Sequence[int], degree: int
) -> RationalPoint:
    return tuple(
        Fraction(
            sum(alpha[local] * tet_vertices[local][axis] for local in range(4)),
            degree,
        )
        for axis in range(3)
    )  # type: ignore[return-value]


def on_boundary(point: RationalPoint, shape: Point) -> bool:
    return any(
        point[axis] == 0 or point[axis] == shape[axis] for axis in range(3)
    )


def scalar_nodes(degree: int, shape: Point) -> Dict[RationalPoint, int]:
    """Global interior coefficient/node labels for conforming H0 P_degree."""

    indices = tuple(weak_compositions(degree, 4))
    nodes: Dict[RationalPoint, int] = {}
    for cell, sigma in tetrahedra(shape):
        tet_vertices = vertices(cell, sigma)
        for alpha in indices:
            point = physical_node(tet_vertices, alpha, degree)
            if not on_boundary(point, shape):
                nodes.setdefault(point, len(nodes))
    return nodes


def bernstein_derivatives(
    alpha: Sequence[int], lambdas: Sequence[Fraction], degree: int
) -> Tuple[Fraction, ...]:
    """Partial derivatives d B_alpha^degree / d lambda_i."""

    multinomial = Fraction(factorial(degree))
    for value in alpha:
        multinomial /= factorial(value)
    derivatives: List[Fraction] = []
    for differentiated in range(4):
        if alpha[differentiated] == 0:
            derivatives.append(Fraction(0))
            continue
        value = multinomial * alpha[differentiated]
        for index in range(4):
            exponent = alpha[index] - (index == differentiated)
            value *= lambdas[index] ** exponent
        derivatives.append(value)
    return tuple(derivatives)


def add_scaled(
    target: SparseRow, source: Mapping[int, Fraction], scale: Fraction
) -> None:
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        else:
            target.pop(column, None)


def assemble_bernstein() -> Tuple[List[SparseRow], List[SparseRow], int]:
    """Assemble E and M in conforming Bernstein coordinates.

    A Bernstein face trace is determined by its face coefficients, so gluing
    coefficients with the same physical barycentric lattice point enforces
    precisely C0 conformity.  Removing all box-boundary coefficients enforces
    zero trace.
    """

    velocity_indices = tuple(weak_compositions(K, 4))
    pressure_indices = tuple(weak_compositions(K - 1, 4))
    nodes = scalar_nodes(K, SHAPE)
    edge_rows: List[SparseRow] = []
    mean_rows: List[SparseRow] = []

    for cell, sigma in tetrahedra(SHAPE):
        tet_vertices = vertices(cell, sigma)
        barycentric_gradients = gradients(sigma)

        # The element integral of grad(B_alpha^k) is
        #   [sum_{i:alpha_i>0} grad(lambda_i)] / ((k+1)(k+2))
        # on every unit-determinant Freudenthal tetrahedron.
        mean: SparseRow = {}
        for alpha in velocity_indices:
            point = physical_node(tet_vertices, alpha, K)
            if point not in nodes:
                continue
            for component in range(3):
                value = sum(
                    (
                        barycentric_gradients[i][component]
                        for i in range(4)
                        if alpha[i]
                    ),
                    Fraction(0),
                ) / ((K + 1) * (K + 2))
                if value:
                    mean[3 * nodes[point] + component] = value
        mean_rows.append(mean)

        for beta in pressure_indices:
            if sum(value > 0 for value in beta) > 2:
                continue
            lambdas = tuple(Fraction(value, K - 1) for value in beta)
            row: SparseRow = {}
            for alpha in velocity_indices:
                point = physical_node(tet_vertices, alpha, K)
                if point not in nodes:
                    continue
                derivatives = bernstein_derivatives(alpha, lambdas, K)
                for component in range(3):
                    value = sum(
                        derivatives[i] * barycentric_gradients[i][component]
                        for i in range(4)
                    )
                    if value:
                        row[3 * nodes[point] + component] = value
            edge_rows.append(row)

    return edge_rows, mean_rows, 3 * len(nodes)


def univariate_lagrange_coefficients(
    alpha: int, degree: int
) -> Tuple[Fraction, ...]:
    """Coefficients of prod_{j=0}^{alpha-1}(degree*t-j)/alpha!."""

    coefficients = [Fraction(1)]
    for root_index in range(alpha):
        updated = [Fraction(0)] * (len(coefficients) + 1)
        for power, value in enumerate(coefficients):
            updated[power] -= root_index * value
            updated[power + 1] += degree * value
        coefficients = updated
    scale = factorial(alpha)
    return tuple(value / scale for value in coefficients)


def evaluate_and_differentiate(
    coefficients: Sequence[Fraction], point: Fraction
) -> Tuple[Fraction, Fraction]:
    value = sum(
        (coefficient * point**power for power, coefficient in enumerate(coefficients)),
        Fraction(0),
    )
    derivative = sum(
        (
            power * coefficient * point ** (power - 1)
            for power, coefficient in enumerate(coefficients)
            if power
        ),
        Fraction(0),
    )
    return value, derivative


def lagrange_factor(alpha: int, degree: int, point: Fraction) -> Tuple[Fraction, Fraction]:
    return evaluate_and_differentiate(
        univariate_lagrange_coefficients(alpha, degree), point
    )


def product_factorials(values: Iterable[int]) -> int:
    result = 1
    for value in values:
        result *= factorial(value)
    return result


def nodal_integration_weights(degree: int) -> Tuple[Fraction, ...]:
    """Exact integrals of the tetrahedral equispaced nodal basis."""

    weights: List[Fraction] = []
    for alpha in weak_compositions(degree, 4):
        factors = [univariate_lagrange_coefficients(alpha[i], degree) for i in range(4)]
        total = Fraction(0)
        for powers in product(*(range(len(coefficients)) for coefficients in factors)):
            coefficient = Fraction(1)
            for i in range(4):
                coefficient *= factors[i][powers[i]]
            # Unit Freudenthal tetrahedra have volume 1/6.
            total += coefficient * Fraction(
                product_factorials(powers), factorial(sum(powers) + 3)
            )
        weights.append(total)
    return tuple(weights)


def assemble_nodal_lagrange() -> Tuple[List[SparseRow], List[SparseRow], int]:
    """Independent assembly of E and M in equispaced nodal coordinates."""

    velocity_indices = tuple(weak_compositions(K, 4))
    pressure_indices = tuple(weak_compositions(K - 1, 4))
    nodes = scalar_nodes(K, SHAPE)
    weights = nodal_integration_weights(K - 1)
    factor_cache = {
        (alpha, beta): lagrange_factor(alpha, K, Fraction(beta, K - 1))
        for alpha in range(K + 1)
        for beta in range(K)
    }
    edge_rows: List[SparseRow] = []
    mean_rows: List[SparseRow] = []

    for cell, sigma in tetrahedra(SHAPE):
        tet_vertices = vertices(cell, sigma)
        barycentric_gradients = gradients(sigma)
        local_rows: List[SparseRow] = []
        for beta in pressure_indices:
            row: SparseRow = {}
            for alpha in velocity_indices:
                point = physical_node(tet_vertices, alpha, K)
                if point not in nodes:
                    continue
                derivatives: List[Fraction] = []
                for differentiated in range(4):
                    derivative = factor_cache[(alpha[differentiated], beta[differentiated])][1]
                    for other in range(4):
                        if other != differentiated:
                            derivative *= factor_cache[(alpha[other], beta[other])][0]
                    derivatives.append(derivative)
                for component in range(3):
                    value = sum(
                        derivatives[i] * barycentric_gradients[i][component]
                        for i in range(4)
                    )
                    if value:
                        row[3 * nodes[point] + component] = value
            local_rows.append(row)
            if sum(value > 0 for value in beta) <= 2:
                edge_rows.append(dict(row))

        mean: SparseRow = {}
        for weight, row in zip(weights, local_rows):
            if weight:
                add_scaled(mean, row, weight)
        mean_rows.append(mean)

    return edge_rows, mean_rows, 3 * len(nodes)


def echelon(rows: Sequence[Mapping[int, Fraction]]) -> Dict[int, SparseRow]:
    """Exact sparse row echelon form, normalized at each leading column."""

    pivots: Dict[int, SparseRow] = {}
    for source in rows:
        row = dict(source)
        while row:
            column = min(row)
            if column not in pivots:
                inverse = 1 / row[column]
                pivots[column] = {
                    j: value * inverse for j, value in row.items() if value
                }
                break
            add_scaled(row, pivots[column], -row[column])
    return pivots


def right_nullspace(
    rows: Sequence[Mapping[int, Fraction]], ncols: int
) -> Tuple[SparseRow, ...]:
    pivots = echelon(rows)
    basis: List[SparseRow] = []
    for free in range(ncols):
        if free in pivots:
            continue
        vector: SparseRow = {free: Fraction(1)}
        for pivot in reversed(sorted(pivots)):
            value = -sum(
                (
                    coefficient * vector.get(column, Fraction(0))
                    for column, coefficient in pivots[pivot].items()
                    if column != pivot
                ),
                Fraction(0),
            )
            if value:
                vector[pivot] = value
        basis.append(vector)
    return tuple(basis)


def dot(row: Mapping[int, Fraction], vector: Mapping[int, Fraction]) -> Fraction:
    if len(row) > len(vector):
        row, vector = vector, row
    return sum(
        (value * vector.get(column, Fraction(0)) for column, value in row.items()),
        Fraction(0),
    )


EXPLICIT_SCALED_MEAN_MATRIX = (
    (-1, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0),
    (1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    (0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0),
    (0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0),
    (0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1),
    (0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, 1, -1, 0, -1, 1, 0),
    (0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0),
    (0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0),
    (-1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0),
    (0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1),
)


def explicit_macro_generators(
    nodes: Mapping[RationalPoint, int],
) -> Tuple[SparseRow, ...]:
    """Return the eleven three-coefficient Bernstein fields in the paper."""

    # Each entry is ((4*x, 4*y, 4*z), vector component, coefficient).
    specifications = (
        (((4, 2, 2), 2, -1), ((4, 2, 1), 1, 1), ((4, 2, 3), 1, 1)),
        (((2, 2, 1), 1, 1), ((2, 1, 1), 0, -1), ((2, 1, 2), 2, 1)),
        (((4, 3, 2), 0, 1), ((3, 3, 2), 0, 1), ((2, 3, 2), 0, 1)),
        (((2, 2, 1), 0, 1), ((1, 2, 1), 1, -1), ((1, 2, 2), 2, 1)),
        (((4, 2, 3), 0, 1), ((3, 2, 3), 0, 1), ((2, 2, 3), 0, 1)),
        (((6, 2, 1), 1, 1), ((6, 1, 1), 0, -1), ((6, 1, 2), 2, 1)),
        (((7, 3, 2), 2, -1), ((7, 2, 2), 1, 1), ((6, 3, 2), 0, 1)),
        (((4, 3, 1), 0, 1), ((3, 3, 1), 0, 1), ((5, 3, 1), 0, 1)),
        (((4, 2, 1), 0, 1), ((6, 2, 1), 0, 1), ((5, 2, 1), 0, 1)),
        (((7, 2, 2), 2, 1), ((7, 2, 3), 1, -1), ((6, 2, 3), 0, 1)),
        (((4, 1, 3), 0, 1), ((3, 1, 3), 0, 1), ((5, 1, 3), 0, 1)),
    )
    fields: List[SparseRow] = []
    for specification in specifications:
        field: SparseRow = {}
        for scaled_point, component, coefficient in specification:
            point = tuple(Fraction(value, 4) for value in scaled_point)
            if point not in nodes:
                raise AssertionError(("missing Bernstein control point", point))
            field[3 * nodes[point] + component] = Fraction(coefficient)
        assert len(field) == 3
        fields.append(field)
    return tuple(fields)


def dense_pivot_columns(matrix: Sequence[Sequence[Fraction]]) -> Tuple[int, ...]:
    work = [list(row) for row in matrix]
    rows, columns = len(work), len(work[0])
    pivot_columns: List[int] = []
    pivot_row = 0
    for column in range(columns):
        source = next(
            (row for row in range(pivot_row, rows) if work[row][column]), None
        )
        if source is None:
            continue
        work[pivot_row], work[source] = work[source], work[pivot_row]
        inverse = 1 / work[pivot_row][column]
        work[pivot_row] = [value * inverse for value in work[pivot_row]]
        for row in range(rows):
            if row == pivot_row or not work[row][column]:
                continue
            multiplier = work[row][column]
            work[row] = [
                work[row][j] - multiplier * work[pivot_row][j]
                for j in range(columns)
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == rows:
            break
    return tuple(pivot_columns)


def determinant(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    work = [list(row) for row in matrix]
    size = len(work)
    if any(len(row) != size for row in work):
        raise ValueError("determinant requires a square matrix")
    result = Fraction(1)
    for column in range(size):
        source = next(
            (row for row in range(column, size) if work[row][column]), None
        )
        if source is None:
            return Fraction(0)
        if source != column:
            work[column], work[source] = work[source], work[column]
            result = -result
        pivot = work[column][column]
        result *= pivot
        for row in range(column + 1, size):
            if not work[row][column]:
                continue
            multiplier = work[row][column] / pivot
            for j in range(column + 1, size):
                work[row][j] -= multiplier * work[column][j]
            work[row][column] = 0
    return result


def sparse_hash(rows: Sequence[Mapping[int, Fraction]], ncols: int) -> str:
    digest = sha256()
    digest.update(f"{len(rows)} {ncols}\n".encode("ascii"))
    for row_index, row in enumerate(rows):
        for column in sorted(row):
            value = row[column]
            digest.update(
                f"{row_index} {column} {value.numerator} {value.denominator}\n".encode(
                    "ascii"
                )
            )
    return digest.hexdigest()


def certify() -> dict[str, object]:
    edge_rows, mean_rows, ncols = assemble_bernstein()
    assert ncols == 189
    assert len(edge_rows) == 192
    assert len(mean_rows) == 12

    nodes = scalar_nodes(K, SHAPE)
    explicit_fields = explicit_macro_generators(nodes)
    assert all(
        not dot(row, field) for row in edge_rows for field in explicit_fields
    )
    explicit_means = [
        [dot(mean, field) for field in explicit_fields] for mean in mean_rows
    ]
    scaled_first_eleven = tuple(
        tuple(30 * value for value in row) for row in explicit_means[:11]
    )
    assert scaled_first_eleven == EXPLICIT_SCALED_MEAN_MATRIX
    assert determinant(scaled_first_eleven) == -6
    assert all(sum(column) == 0 for column in zip(*explicit_means))

    rank_edge = len(echelon(edge_rows))
    rank_coupled = len(echelon(edge_rows + mean_rows))
    assert rank_edge == 122
    assert rank_coupled == 133

    total_mean: SparseRow = {}
    for row in mean_rows:
        add_scaled(total_mean, row, Fraction(1))
    assert not total_mean  # divergence theorem for zero patch trace

    kernel = right_nullspace(edge_rows, ncols)
    assert len(kernel) == 67
    mean_on_kernel = [
        [dot(mean, vector) for vector in kernel] for mean in mean_rows
    ]
    selected = dense_pivot_columns(mean_on_kernel)
    assert selected == (0, 4, 5, 7, 13, 14, 18, 36, 40, 41, 42)
    minor = [
        [mean_on_kernel[row][column] for column in selected] for row in range(11)
    ]
    minor_determinant = determinant(minor)
    assert minor_determinant == Fraction(1, 984_150_000_000_000)

    edge_hash = sparse_hash(edge_rows, ncols)
    coupled_hash = sparse_hash(edge_rows + mean_rows, ncols)
    assert edge_hash == "c29acfff4fa9f4c232651c871a4ebdb00dc6735614775946d1901260060049b7"
    assert coupled_hash == "99cb227705b244a4d73011d82e23a3d52d9a63acbb48490f0c9e0e857453abff"

    nodal_edges, nodal_means, nodal_ncols = assemble_nodal_lagrange()
    assert nodal_ncols == ncols
    nodal_rank_edge = len(echelon(nodal_edges))
    nodal_rank_coupled = len(echelon(nodal_edges + nodal_means))
    assert nodal_rank_edge == rank_edge
    assert nodal_rank_coupled == rank_coupled
    nodal_edge_hash = sparse_hash(nodal_edges, nodal_ncols)
    nodal_coupled_hash = sparse_hash(nodal_edges + nodal_means, nodal_ncols)
    assert nodal_edge_hash == "11f4468ef504489019fe3a508dbd45ceb1e433db92ee413803afbcf1383e3c63"
    assert nodal_coupled_hash == "a286bd0fa3cb8f4ec0d7f2fd820f21cb803f27b5196476a9e4a0e40bfc08f5d6"

    return {
        "arithmetic": "fractions.Fraction (exact Q)",
        "patch": [2, 1, 1],
        "tetrahedra": 12,
        "velocity_columns": ncols,
        "edge_rows": len(edge_rows),
        "explicit_macro_fields": len(explicit_fields),
        "explicit_coefficients_per_field": [len(field) for field in explicit_fields],
        "explicit_scaled_mean_determinant": "-6",
        "rank_E": rank_edge,
        "rank_E_stacked_M": rank_coupled,
        "dimension_M_of_kernel_E": rank_coupled - rank_edge,
        "sum_of_mean_rows_is_zero": True,
        "kernel_E_dimension": len(kernel),
        "selected_kernel_basis_columns": list(selected),
        "induced_11x11_determinant": str(minor_determinant),
        "bernstein_edge_matrix_sha256": edge_hash,
        "bernstein_coupled_matrix_sha256": coupled_hash,
        "nodal_crosscheck_rank_E": nodal_rank_edge,
        "nodal_crosscheck_rank_E_stacked_M": nodal_rank_coupled,
        "nodal_edge_matrix_sha256": nodal_edge_hash,
        "nodal_coupled_matrix_sha256": nodal_coupled_hash,
    }


def main() -> None:
    if not __debug__:
        raise RuntimeError("run certificates without Python -O so assertions remain active")
    print(json.dumps(certify(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
