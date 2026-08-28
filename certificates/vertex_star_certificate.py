#!/usr/bin/env python3
"""Exact certificate for the independent Freudenthal vertex lift.

The mathematical statement is local and degree independent on the data side.
For a mesh vertex ``a``, let ``A_a`` map the componentwise directional
derivatives along the non-boundary mesh edges issuing from ``a`` to the broken
values of the divergence at ``a``.  Elementary trace continuity proves that
``image(A_a)`` is exactly the set of vertex data attainable by a conforming
velocity (for every polynomial degree at least two).

On the tetrahedral star of ``a`` this program assembles the continuous cubic
velocity space with zero trace on the complete star boundary.  It imposes

* zero divergence integral on every tetrahedron, and
* zero divergence at every tetrahedron vertex other than ``a``.

Exact rational elimination proves that the remaining target image equals
``image(A_a)``.  Thus the resulting cubic field extends by zero, writes only
the chosen broken vertex, and preserves all element means.  The program checks
every vertex placement on the 1^3, 2^3, and 3^3 grids.  The accompanying
finite-coverage lemma in the manuscript proves that their six local types are
all types for arbitrary N.

For one representative of each type the JSON also contains an explicit
rational right inverse: a basis of attainable target vectors, cubic nodal
coefficient vectors lifting that basis, and the small coordinate inverse that
turns arbitrary compatible data into basis coefficients.

Only the Python standard library is used.  All primary ranks and relations are
computed over fractions.Fraction.  Nonzero minors modulo the verified prime
1,000,003 are recorded as independent lower-rank witnesses.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
from math import factorial, isqrt
from pathlib import Path


Point = tuple[int, int, int]
RPoint = tuple[Fraction, Fraction, Fraction]

SCHEMA_VERSION = "freudenthal-vertex-star-v1"
GRIDS = (1, 2, 3)
LIFT_DEGREE = 3
TARGET_DEGREES = (4, 5)
MODULUS = 1_000_003
EXPECTED_VERTEX_COUNTS = {1: 8, 2: 27, 3: 64}
EXPECTED_CONFIGURATION_COUNTS = {1: 2, 2: 6, 3: 6}
EXPECTED_TYPE_COUNTS = {
    1: {
        "corner_six_tet": 2,
        "corner_two_tet": 6,
    },
    2: {
        "boundary_edge_eight_tet": 6,
        "boundary_edge_four_tet": 6,
        "boundary_face_twelve_tet": 6,
        "corner_six_tet": 2,
        "corner_two_tet": 6,
        "interior_twenty_four_tet": 1,
    },
    3: {
        "boundary_edge_eight_tet": 12,
        "boundary_edge_four_tet": 12,
        "boundary_face_twelve_tet": 24,
        "corner_six_tet": 2,
        "corner_two_tet": 6,
        "interior_twenty_four_tet": 8,
    },
}
TYPE_BY_STAR = {
    2: ("corner_two_tet", 0),
    4: ("boundary_edge_four_tet", 0),
    6: ("corner_six_tet", 3),
    8: ("boundary_edge_eight_tet", 5),
    12: ("boundary_face_twelve_tet", 8),
    24: ("interior_twenty_four_tet", 18),
}


def compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


@dataclass(frozen=True)
class Tet:
    vertices: tuple[Point, Point, Point, Point]


def mesh(shape: Point) -> tuple[Tet, ...]:
    tets = []
    for cell in product(*(range(n) for n in shape)):
        for order in permutations(range(3)):
            current = list(cell)
            vertices = [tuple(current)]
            for direction in order:
                current = current.copy()
                current[direction] += 1
                vertices.append(tuple(current))
            tets.append(Tet(tuple(vertices)))
    return tuple(tets)


def det3(matrix) -> int:
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def barycentric_gradients(vertices):
    matrix = [
        [vertices[j + 1][i] - vertices[0][i] for j in range(3)]
        for i in range(3)
    ]
    determinant = det3(matrix)
    inverse = []
    for i in range(3):
        row = []
        for j in range(3):
            minor = [
                [matrix[x][y] for y in range(3) if y != i]
                for x in range(3) if x != j
            ]
            cofactor = ((-1) ** (i + j)) * (
                minor[0][0] * minor[1][1] - minor[0][1] * minor[1][0]
            )
            row.append(Fraction(cofactor, determinant))
        inverse.append(tuple(row))
    return (
        tuple(-sum(inverse[i][d] for i in range(3)) for d in range(3)),
    ) + tuple(inverse)


def edge(vertices) -> tuple[Point, Point]:
    return tuple(sorted(vertices))


def face(vertices):
    return tuple(sorted(vertices))


def node(vertices, multiindex, degree: int) -> RPoint:
    return tuple(
        Fraction(sum(multiindex[i] * vertices[i][d] for i in range(4)), degree)
        for d in range(3)
    )


def lagrange_factor(order: int, degree: int, value: Fraction):
    coefficients = [Fraction(1)]
    for shift in range(order):
        updated = [Fraction(0)] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            updated[i] -= shift * coefficient
            updated[i + 1] += degree * coefficient
        coefficients = updated
    coefficients = [coefficient / factorial(order) for coefficient in coefficients]
    function_value = sum(
        coefficient * value**power
        for power, coefficient in enumerate(coefficients)
    )
    derivative = sum(
        power * coefficient * value ** (power - 1)
        for power, coefficient in enumerate(coefficients)
        if power
    )
    return function_value, derivative


def exterior_faces(tets):
    counts = defaultdict(int)
    for tet in tets:
        for omitted in range(4):
            counts[face(tet.vertices[i] for i in range(4) if i != omitted)] += 1
    return {triangle for triangle, count in counts.items() if count == 1}


def face_nodes(triangle, degree: int):
    for multiindex in compositions(degree, 3):
        yield tuple(
            Fraction(
                sum(multiindex[i] * triangle[i][d] for i in range(3)),
                degree,
            )
            for d in range(3)
        )


def assemble_supported_cubic(global_tets, selected):
    """Assemble div(CG_3^3) at all broken P2 Lagrange nodes on a star.

    Cubic velocity nodes on the complete exterior of the selected star are
    removed, so every column is the zero extension of a conforming H1_0 field.
    Nodes are sorted exactly; column 3*i+d is component d at nodes[i].
    """
    tets = tuple(global_tets[i] for i in selected)
    velocity_indices = tuple(compositions(3, 4))
    pressure_indices = tuple(compositions(2, 4))
    forbidden = {
        point
        for triangle in exterior_faces(tets)
        for point in face_nodes(triangle, 3)
    }
    nodes = sorted({
        node(tet.vertices, multiindex, 3)
        for tet in tets
        for multiindex in velocity_indices
        if node(tet.vertices, multiindex, 3) not in forbidden
    })
    node_ids = {point: i for i, point in enumerate(nodes)}
    cache = {
        (order, value): lagrange_factor(order, 3, Fraction(value, 2))
        for order in range(4)
        for value in range(3)
    }
    rows = []
    for tet in tets:
        gradients = barycentric_gradients(tet.vertices)
        for pressure_index in pressure_indices:
            row = {}
            for velocity_index in velocity_indices:
                point = node(tet.vertices, velocity_index, 3)
                if point not in node_ids:
                    continue
                barycentric_derivatives = []
                for i in range(4):
                    value = cache[velocity_index[i], pressure_index[i]][1]
                    for j in range(4):
                        if i != j:
                            value *= cache[velocity_index[j], pressure_index[j]][0]
                    barycentric_derivatives.append(value)
                for component in range(3):
                    value = sum(
                        barycentric_derivatives[i] * gradients[i][component]
                        for i in range(4)
                    )
                    if value:
                        row[3 * node_ids[point] + component] = value
            rows.append(row)
    return tets, pressure_indices, rows, tuple(nodes)


def p2_integral_weights(pressure_indices):
    """Exact P2 Lagrange weights on every determinant-one tetrahedron."""
    weights = tuple(
        Fraction(-1, 120) if max(index) == 2 else Fraction(1, 30)
        for index in pressure_indices
    )
    if sum(weights) != Fraction(1, 6):
        raise AssertionError(weights)
    return weights


def add_scaled(target, source, scale):
    for column, value in source.items():
        updated = target.get(column, Fraction(0)) + scale * value
        if updated:
            target[column] = updated
        else:
            target.pop(column, None)


def supported_maps(vertex, star, global_tets):
    tets, pressure_indices, rows, nodes = assemble_supported_cubic(
        global_tets, tuple(sorted(star))
    )
    block = len(pressure_indices)
    weights = p2_integral_weights(pressure_indices)
    mean_rows = []
    off_target_rows = []
    target_rows = []
    target_tets = []
    for tet_number, tet in enumerate(tets):
        mean_row = {}
        for local_row, weight in enumerate(weights):
            add_scaled(mean_row, rows[tet_number * block + local_row], weight)
        mean_rows.append(mean_row)
        for local_vertex, geometric_vertex in enumerate(tet.vertices):
            pressure_index = tuple(
                2 if i == local_vertex else 0 for i in range(4)
            )
            row = rows[
                tet_number * block + pressure_indices.index(pressure_index)
            ]
            if geometric_vertex == vertex:
                target_rows.append(row)
                target_tets.append(tet)
            else:
                off_target_rows.append(row)
    constraints = mean_rows + off_target_rows
    return constraints, target_rows, mean_rows, off_target_rows, nodes, target_tets


def boundary_edge(first: Point, second: Point, shape: Point) -> bool:
    return any(
        first[d] == second[d] == 0
        or first[d] == second[d] == shape[d]
        for d in range(3)
    )


def jet_matrix(shape, vertex, star, global_tets):
    incident_edges = sorted({
        edge((vertex, other))
        for tet_number in star
        for other in global_tets[tet_number].vertices
        if other != vertex
    })
    active_edges = tuple(
        item for item in incident_edges if not boundary_edge(*item, shape)
    )
    column_ids = {
        (item, component): 3 * i + component
        for i, item in enumerate(active_edges)
        for component in range(3)
    }
    rows = []
    target_tets = []
    for tet_number in sorted(star):
        tet = global_tets[tet_number]
        gradients = barycentric_gradients(tet.vertices)
        row = {}
        for local_vertex, other in enumerate(tet.vertices):
            if other == vertex:
                continue
            item = edge((vertex, other))
            if item not in active_edges:
                continue
            for component in range(3):
                value = gradients[local_vertex][component]
                if value:
                    row[column_ids[(item, component)]] = value
        rows.append(row)
        target_tets.append(tet)
    return rows, tuple(incident_edges), active_edges, tuple(target_tets)


def rank_q(rows) -> int:
    pivots = {}
    for original in rows:
        row = dict(original)
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = {
                    column: coefficient / value
                    for column, coefficient in row.items()
                }
                break
            value = row[pivot]
            add_scaled(row, pivots[pivot], -value)
    return len(pivots)


def row_basis_indices(rows):
    pivots = {}
    selected = []
    for row_number, original in enumerate(rows):
        row = dict(original)
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = {
                    column: coefficient / value
                    for column, coefficient in row.items()
                }
                selected.append(row_number)
                break
            value = row[pivot]
            add_scaled(row, pivots[pivot], -value)
    return selected


def pivot_columns(rows):
    pivots = {}
    for original in rows:
        row = dict(original)
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = {
                    column: coefficient / value
                    for column, coefficient in row.items()
                }
                break
            value = row[pivot]
            add_scaled(row, pivots[pivot], -value)
    return sorted(pivots)


def left_relations(rows):
    """Return an exact basis of the left nullspace of a sparse matrix."""
    pivots = {}
    relations = []
    for row_number, original in enumerate(rows):
        row = dict(original)
        combination = {row_number: Fraction(1)}
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = (
                    {column: coefficient / value for column, coefficient in row.items()},
                    {index: coefficient / value for index, coefficient in combination.items()},
                )
                break
            value = row[pivot]
            pivot_row, pivot_combination = pivots[pivot]
            add_scaled(row, pivot_row, -value)
            add_scaled(combination, pivot_combination, -value)
        else:
            relations.append(combination)
    return relations


def target_annihilator(rows, constraint_count, target_count):
    """Canonical RREF of relations on target values after constraints vanish."""
    if target_count != len(rows) - constraint_count:
        raise ValueError((target_count, len(rows), constraint_count))
    pivots = {}
    for relation in left_relations(rows):
        row = {
            index - constraint_count: coefficient
            for index, coefficient in relation.items()
            if index >= constraint_count and coefficient
        }
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = {
                    column: coefficient / value
                    for column, coefficient in row.items()
                }
                break
            value = row[pivot]
            add_scaled(row, pivots[pivot], -value)
    for pivot in sorted(pivots, reverse=True):
        for other in sorted(pivots):
            if other == pivot or pivot not in pivots[other]:
                continue
            value = pivots[other][pivot]
            add_scaled(pivots[other], pivots[pivot], -value)
    return tuple(
        tuple(sorted(row.items())) for _, row in sorted(pivots.items())
    )


def solve_consistent(rows, right_hand_side, column_count):
    """Lexicographic exact solve with every free variable fixed to zero."""
    if len(rows) != len(right_hand_side):
        raise ValueError((len(rows), len(right_hand_side)))
    pivots = {}
    for original, original_rhs in zip(rows, right_hand_side):
        row = dict(original)
        rhs = original_rhs
        while row:
            pivot = min(row)
            if pivot not in pivots:
                value = row[pivot]
                pivots[pivot] = (
                    {column: coefficient / value for column, coefficient in row.items()},
                    rhs / value,
                )
                break
            value = row[pivot]
            pivot_row, pivot_rhs = pivots[pivot]
            add_scaled(row, pivot_row, -value)
            rhs -= value * pivot_rhs
        else:
            if rhs:
                raise ArithmeticError("inconsistent exact system")
    solution = {}
    for pivot in sorted(pivots, reverse=True):
        row, rhs = pivots[pivot]
        value = rhs - sum(
            coefficient * solution.get(column, Fraction(0))
            for column, coefficient in row.items()
            if column != pivot
        )
        if value:
            solution[pivot] = value
    if any(not 0 <= column < column_count for column in solution):
        raise AssertionError(solution)
    return solution


def row_action(row, vector):
    return sum(
        coefficient * vector.get(column, Fraction(0))
        for column, coefficient in row.items()
    )


def is_prime(number: int) -> bool:
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    return all(number % divisor for divisor in range(3, isqrt(number) + 1, 2))


def fraction_mod(value: Fraction, prime: int) -> int:
    denominator = value.denominator % prime
    if denominator == 0:
        raise ArithmeticError(
            f"denominator {value.denominator} is not invertible modulo {prime}"
        )
    return value.numerator % prime * pow(denominator, prime - 2, prime) % prime


def check_denominators(rows, prime=MODULUS):
    for row in rows:
        for value in row.values():
            if value.denominator % prime == 0:
                raise ArithmeticError((value, prime))


def modular_minor(rows, prime=MODULUS):
    if not is_prime(prime):
        raise ValueError(f"modular witness modulus is not prime: {prime}")
    pivots = {}
    selected_rows = []
    selected_columns = []
    for row_number, original in enumerate(rows):
        row = {}
        for column, value in original.items():
            residue = fraction_mod(value, prime)
            if residue:
                row[column] = residue
        while row:
            pivot = min(row)
            if pivot not in pivots:
                inverse = pow(row[pivot], prime - 2, prime)
                pivots[pivot] = {
                    column: value * inverse % prime
                    for column, value in row.items()
                    if value * inverse % prime
                }
                selected_rows.append(row_number)
                selected_columns.append(pivot)
                break
            value = row[pivot]
            for column, coefficient in pivots[pivot].items():
                updated = (row.get(column, 0) - value * coefficient) % prime
                if updated:
                    row[column] = updated
                else:
                    row.pop(column, None)
    matrix = [
        [fraction_mod(rows[i].get(j, Fraction(0)), prime) for j in selected_columns]
        for i in selected_rows
    ]
    determinant = 1
    for column in range(len(selected_columns)):
        pivot_row = next(
            row for row in range(column, len(selected_rows))
            if matrix[row][column]
        )
        if pivot_row != column:
            matrix[pivot_row], matrix[column] = matrix[column], matrix[pivot_row]
            determinant = -determinant
        pivot = matrix[column][column]
        determinant = determinant * pivot % prime
        inverse = pow(pivot, prime - 2, prime)
        for row in range(column + 1, len(selected_rows)):
            if not matrix[row][column]:
                continue
            multiplier = matrix[row][column] * inverse % prime
            for entry in range(column + 1, len(selected_columns)):
                matrix[row][entry] = (
                    matrix[row][entry] - multiplier * matrix[column][entry]
                ) % prime
    determinant %= prime
    if selected_columns and determinant == 0:
        raise AssertionError("selected modular minor is singular")
    return {
        "prime": prime,
        "rank": len(selected_columns),
        "determinant_mod_prime": determinant,
        "row_indices": selected_rows,
        "column_indices": selected_columns,
    }


def matrix_hash(rows, column_count):
    digest = sha256(f"rows={len(rows)} columns={column_count}\n".encode())
    for row_number, row in enumerate(rows):
        digest.update(f"row={row_number}\n".encode())
        for column in sorted(row):
            value = row[column]
            digest.update(
                f"{column} {value.numerator}/{value.denominator}\n".encode()
            )
    return digest.hexdigest()


def relation_hash(relations):
    digest = sha256(f"relations={len(relations)}\n".encode())
    for row_number, row in enumerate(relations):
        digest.update(f"row={row_number}\n".encode())
        for column, value in row:
            digest.update(
                f"{column} {value.numerator}/{value.denominator}\n".encode()
            )
    return digest.hexdigest()


def geometry_hash(global_tets, star):
    payload = [
        [list(vertex) for vertex in global_tets[i].vertices]
        for i in sorted(star)
    ]
    return sha256(json.dumps(payload, separators=(",", ":")).encode()).hexdigest()


def transformed_configuration(vertex, star, global_tets, active_edges):
    """Canonical state under translations, permutations, and central inversion."""
    candidates = []
    points = [
        point for tet_number in star for point in global_tets[tet_number].vertices
    ]
    for coordinate_order in permutations(range(3)):
        for sign in (1, -1):
            transformed_points = [
                tuple(sign * point[coordinate_order[d]] for d in range(3))
                for point in points
            ]
            minima = tuple(
                min(point[d] for point in transformed_points) for d in range(3)
            )

            def transform(point):
                raw = tuple(sign * point[coordinate_order[d]] for d in range(3))
                return tuple(raw[d] - minima[d] for d in range(3))

            state = {
                "target": transform(vertex),
                "star": sorted(
                    sorted(transform(point) for point in global_tets[i].vertices)
                    for i in star
                ),
                "active_edges": sorted(
                    sorted((transform(item[0]), transform(item[1])))
                    for item in active_edges
                ),
            }
            candidates.append(json.dumps(state, sort_keys=True, separators=(",", ":")))
    return min(candidates)


def rational(value):
    return [value.numerator, value.denominator]


def rational_point(point):
    return [rational(value) for value in point]


def explicit_operator(jet_rows, constraints, targets, column_count, nodes,
                      target_tets, active_edges):
    selected_jet_columns = pivot_columns(jet_rows)
    rank = len(selected_jet_columns)
    target_basis_rows = [
        {
            basis_column: row.get(jet_column, Fraction(0))
            for basis_column, jet_column in enumerate(selected_jet_columns)
            if row.get(jet_column, Fraction(0))
        }
        for row in jet_rows
    ]
    system_rows = constraints + targets
    lift_basis = []
    for basis_column, jet_column in enumerate(selected_jet_columns):
        rhs = [Fraction(0)] * len(constraints) + [
            row.get(jet_column, Fraction(0)) for row in jet_rows
        ]
        solution = solve_consistent(system_rows, rhs, column_count)
        if any(row_action(row, solution) != value for row, value in zip(system_rows, rhs)):
            raise AssertionError("explicit lift basis failed exact verification")
        lift_basis.append(solution)

    selected_target_rows = row_basis_indices(target_basis_rows)
    if len(selected_target_rows) != rank:
        raise AssertionError((len(selected_target_rows), rank))
    square_rows = [target_basis_rows[i] for i in selected_target_rows]
    inverse_columns = []
    for column in range(rank):
        rhs = [Fraction(i == column) for i in range(rank)]
        inverse_columns.append(solve_consistent(square_rows, rhs, rank))
    coordinate_inverse = [
        [inverse_columns[column].get(row, Fraction(0)) for column in range(rank)]
        for row in range(rank)
    ]
    for i in range(rank):
        for j in range(rank):
            value = sum(
                coordinate_inverse[i][ell]
                * square_rows[ell].get(j, Fraction(0))
                for ell in range(rank)
            )
            if value != Fraction(i == j):
                raise AssertionError("target-coordinate inverse failed")

    return {
        "velocity_coordinate_contract": "column 3*i+d is component d at velocity_nodes[i]",
        "velocity_nodes": [rational_point(point) for point in nodes],
        "target_tetrahedra": [
            [list(point) for point in tet.vertices] for tet in target_tets
        ],
        "active_edge_jet_contract": "active_edges[i] stores unordered endpoints; column 3*i+d is the component-d directional derivative from target_vertex toward the other endpoint",
        "active_edges": [[list(point) for point in item] for item in active_edges],
        "selected_jet_columns": selected_jet_columns,
        "target_basis": [
            [rational(row.get(column, Fraction(0))) for column in range(rank)]
            for row in target_basis_rows
        ],
        "selected_target_rows": selected_target_rows,
        "coordinate_inverse": [
            [rational(value) for value in row] for row in coordinate_inverse
        ],
        "lift_basis": [
            [
                [column, value.numerator, value.denominator]
                for column, value in sorted(vector.items())
            ]
            for vector in lift_basis
        ],
        "verification": {
            "constraint_equations": len(constraints),
            "target_equations": len(targets),
            "velocity_columns": column_count,
            "basis_dimension": rank,
            "identity": "O X = 0, target_map X = target_basis, coordinate_inverse * selected_rows(target_basis) = I",
        },
    }


def vertex_record_id(shape, vertex):
    coordinates = ",".join(str(value) for value in vertex)
    return f"N{shape[0]}:a({coordinates})"


def boundary_planes(shape, vertex):
    planes = []
    for direction, name in enumerate("xyz"):
        if vertex[direction] == 0:
            planes.append(f"{name}=0")
        if vertex[direction] == shape[direction]:
            planes.append(f"{name}={shape[direction]}")
    return planes


def certify(shape, vertex, star, global_tets):
    kind, expected_dimension = TYPE_BY_STAR[len(star)]
    jet_rows, incident_edges, active_edges, jet_tets = jet_matrix(
        shape, vertex, star, global_tets
    )
    constraints, targets, means, off_targets, nodes, target_tets = supported_maps(
        vertex, star, global_tets
    )
    if [tet.vertices for tet in jet_tets] != [tet.vertices for tet in target_tets]:
        raise AssertionError("jet and supported target order differ")
    jet_columns = 3 * len(active_edges)
    velocity_columns = 3 * len(nodes)
    check_denominators(jet_rows + constraints + targets)
    jet_rank = rank_q(jet_rows)
    constraint_rank = rank_q(constraints)
    augmented_rank = rank_q(constraints + targets)
    lift_dimension = augmented_rank - constraint_rank
    jet_relations = target_annihilator(jet_rows, 0, len(jet_rows))
    lift_relations = target_annihilator(
        constraints + targets, len(constraints), len(targets)
    )
    if jet_rank != expected_dimension:
        raise AssertionError((kind, vertex, jet_rank, expected_dimension))
    if lift_dimension != expected_dimension:
        raise AssertionError((kind, vertex, lift_dimension, expected_dimension))
    if jet_relations != lift_relations:
        raise AssertionError((kind, vertex, "target annihilators differ"))
    canonical_state = transformed_configuration(
        vertex, star, global_tets, active_edges
    )
    configuration_id = "vcfg-" + sha256(canonical_state.encode()).hexdigest()[:16]
    jet_witness = modular_minor(jet_rows)
    constraint_witness = modular_minor(constraints)
    augmented_witness = modular_minor(constraints + targets)
    for witness, exact_rank in (
        (jet_witness, jet_rank),
        (constraint_witness, constraint_rank),
        (augmented_witness, augmented_rank),
    ):
        if witness["rank"] != exact_rank:
            raise AssertionError((witness["rank"], exact_rank))
    relation_json = [
        [[column, value.numerator, value.denominator] for column, value in row]
        for row in jet_relations
    ]
    record = {
        "record_id": vertex_record_id(shape, vertex),
        "schema_version": SCHEMA_VERSION,
        "grid_shape": list(shape),
        "target_vertex": list(vertex),
        "kind": kind,
        "configuration_id": configuration_id,
        "physical_boundary_planes_at_vertex": boundary_planes(shape, vertex),
        "star_tetrahedra": len(star),
        "star_geometry_sha256": geometry_hash(global_tets, star),
        "incident_edges": len(incident_edges),
        "active_nonboundary_edges": len(active_edges),
        "jet_columns": jet_columns,
        "target_rows": len(jet_rows),
        "jet_rank": jet_rank,
        "compatibility_dimension": jet_rank,
        "compatibility_codimension": len(jet_rows) - jet_rank,
        "jet_matrix_sha256": matrix_hash(jet_rows, jet_columns),
        "compatibility_relations_rref": relation_json,
        "compatibility_relations_sha256": relation_hash(jet_relations),
        "jet_matrix_minor": jet_witness,
        "lift_degree": LIFT_DEGREE,
        "target_degrees": list(TARGET_DEGREES),
        "velocity_columns": velocity_columns,
        "mean_constraint_rows": len(means),
        "off_target_vertex_rows": len(off_targets),
        "constraint_rows": len(constraints),
        "constraint_rank": constraint_rank,
        "augmented_rank": augmented_rank,
        "supported_image_dimension": lift_dimension,
        "constraint_matrix_sha256": matrix_hash(constraints, velocity_columns),
        "augmented_matrix_sha256": matrix_hash(
            constraints + targets, velocity_columns
        ),
        "constraint_matrix_minor": constraint_witness,
        "augmented_matrix_minor": augmented_witness,
        "target_annihilators_equal": True,
    }
    operator = explicit_operator(
        jet_rows, constraints, targets, velocity_columns, nodes,
        target_tets, active_edges,
    )
    operator["configuration_id"] = configuration_id
    operator["kind"] = kind
    operator["representative_record_id"] = record["record_id"]
    operator["target_vertex"] = list(vertex)
    return record, operator, canonical_state


def main():
    if sys.version_info < (3, 10):
        raise RuntimeError("Python 3.10 or newer is required")
    if not __debug__:
        raise RuntimeError("run without Python -O so assertions remain active")
    if not is_prime(MODULUS):
        raise RuntimeError(f"configured modulus is not prime: {MODULUS}")
    parser = argparse.ArgumentParser(
        description="Generate the exact Freudenthal vertex-star certificate."
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="override certificates/vertex_star_certificate.json",
    )
    args = parser.parse_args()
    source = Path(__file__).resolve()
    output = (args.output or source.with_suffix(".json")).resolve()
    if output == source:
        raise ValueError("refusing to overwrite the generator source")
    started = time.perf_counter()
    records = []
    canonical_states = {}
    canonical_operators = {}
    placement_counts = {}
    type_counts = {}
    configuration_counts = {}

    for grid_size in GRIDS:
        shape = (grid_size, grid_size, grid_size)
        global_tets = mesh(shape)
        vertices = sorted({
            vertex for tet in global_tets for vertex in tet.vertices
        })
        placement_counts[grid_size] = len(vertices)
        if len(vertices) != EXPECTED_VERTEX_COUNTS[grid_size]:
            raise AssertionError((grid_size, len(vertices)))
        local_types = Counter()
        local_configurations = set()
        for vertex in vertices:
            star = {
                tet_number for tet_number, tet in enumerate(global_tets)
                if vertex in tet.vertices
            }
            record, operator, canonical_state = certify(
                shape, vertex, star, global_tets
            )
            records.append(record)
            local_types[record["kind"]] += 1
            local_configurations.add(record["configuration_id"])
            configuration_id = record["configuration_id"]
            if configuration_id in canonical_states \
                    and canonical_states[configuration_id] != canonical_state:
                raise AssertionError(f"configuration hash collision: {configuration_id}")
            canonical_states[configuration_id] = canonical_state
            canonical_operators.setdefault(configuration_id, operator)
        type_counts[grid_size] = local_types
        configuration_counts[grid_size] = len(local_configurations)
        if dict(sorted(local_types.items())) != EXPECTED_TYPE_COUNTS[grid_size]:
            raise AssertionError((grid_size, dict(local_types)))
        if len(local_configurations) != EXPECTED_CONFIGURATION_COUNTS[grid_size]:
            raise AssertionError((grid_size, len(local_configurations)))
        print(
            f"N={grid_size}: checked {len(vertices)} vertex placements, "
            f"{len(local_configurations)} configurations",
            flush=True,
        )

    if len(canonical_states) != 6:
        raise AssertionError(("configuration union", len(canonical_states)))
    if len(records) != 99:
        raise AssertionError(("record count", len(records)))
    record_ids = [record["record_id"] for record in records]
    if len(record_ids) != len(set(record_ids)):
        raise AssertionError("duplicate record IDs")
    if {operator["kind"] for operator in canonical_operators.values()} != {
        value[0] for value in TYPE_BY_STAR.values()
    }:
        raise AssertionError("missing canonical operator type")

    configurations = []
    for configuration_id, operator in sorted(canonical_operators.items()):
        configurations.append({
            "configuration_id": configuration_id,
            "kind": operator["kind"],
            "representative_record_id": operator["representative_record_id"],
            "placement_count_by_grid": {
                str(grid_size): sum(
                    record["configuration_id"] == configuration_id
                    and record["grid_shape"][0] == grid_size
                    for record in records
                )
                for grid_size in GRIDS
            },
        })

    payload = {
        "schema_version": SCHEMA_VERSION,
        "provenance": {
            "generator": source.name,
            "generator_sha256": sha256(source.read_bytes()).hexdigest(),
            "python_minimum": "3.10",
            "external_packages": [],
            "deterministic": True,
        },
        "mathematical_input": {
            "grids_exhaustively_checked": list(GRIDS),
            "target_degrees": list(TARGET_DEGREES),
            "lift_degree": LIFT_DEGREE,
            "source_compatibility_map": "edge directional jets -> broken divergence values at the target vertex",
            "supported_space": "continuous piecewise P3 vector fields on the target vertex star, zero on the complete star exterior",
            "constraints": [
                "zero divergence integral on every incident tetrahedron",
                "zero divergence at all non-target tetrahedron vertices",
            ],
            "certified_identity": "D_a(ker M_a intersect ker B_a) = image(A_a)",
        },
        "arithmetic": {
            "primary": "fractions.Fraction exact rational elimination",
            "modulus": MODULUS,
            "modulus_verified_prime": True,
            "modular_role": "independent nonzero-minor lower-rank witnesses; never a probabilistic test",
            "p2_integral_weights_on_determinant_one_tet": {
                "vertex": [-1, 120],
                "edge_midpoint": [1, 30],
            },
        },
        "classification": {
            "definition": "local star plus the set of incident edges not contained in the physical boundary, modulo translation, coordinate permutation, and simultaneous reversal of all coordinates",
            "record_count": len(records),
            "canonical_operator_count": len(canonical_operators),
            "configuration_union_count": 6,
            "configuration_count_by_grid": {
                str(grid_size): configuration_counts[grid_size]
                for grid_size in GRIDS
            },
            "vertex_placement_count_by_grid": {
                str(grid_size): placement_counts[grid_size]
                for grid_size in GRIDS
            },
            "vertex_placement_count_by_grid_and_kind": {
                str(grid_size): dict(sorted(type_counts[grid_size].items()))
                for grid_size in GRIDS
            },
            "configurations": configurations,
        },
        "canonical_operators": dict(sorted(canonical_operators.items())),
        "records": records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    elapsed = time.perf_counter() - started
    print(
        f"vertex-star certificate passed: {len(records)} exact records, "
        f"6 explicit operators ({elapsed:.2f}s)",
        flush=True,
    )
    print(f"wrote {output}", flush=True)


if __name__ == "__main__":
    main()
