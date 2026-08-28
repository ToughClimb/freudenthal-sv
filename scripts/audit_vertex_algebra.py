#!/usr/bin/env python3
"""Independent Bernstein-basis audit of the six vertex-star rank rows.

This script imports nothing from the Lagrange-basis certificate generator.  It
uses closed-form Freudenthal barycentric gradients, globally identified cubic
Bernstein coefficients, and direct integrals of differentiated Bernstein
polynomials.  Agreement checks nodal differentiation, mean quadrature, patch
boundary elimination, and the reported exact ranks by a second assembly.
It is a redundant audit, not an additional proof dependency.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
from math import factorial


EXPECTED = {
    2: (0, 3, 1, 1),
    4: (0, 9, 3, 3),
    6: (3, 24, 8, 11),
    8: (5, 39, 13, 18),
    12: (8, 69, 23, 31),
    24: (18, 195, 65, 83),
}


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def tets(size=2):
    result = []
    for cell in product(range(size), repeat=3):
        for sigma in permutations(range(3)):
            point = list(cell)
            vertices = [tuple(point)]
            for direction in sigma:
                point = point.copy()
                point[direction] += 1
                vertices.append(tuple(point))
            result.append((tuple(sigma), tuple(vertices)))
    return result


def gradients(sigma):
    """grad lambda for a coordinate-order tetrahedron, without matrix inversion."""
    result = [[Fraction(0) for _ in range(3)] for _ in range(4)]
    result[0][sigma[0]] = Fraction(-1)
    result[1][sigma[0]] = Fraction(1)
    result[1][sigma[1]] = Fraction(-1)
    result[2][sigma[1]] = Fraction(1)
    result[2][sigma[2]] = Fraction(-1)
    result[3][sigma[2]] = Fraction(1)
    return tuple(tuple(row) for row in result)


def control_point(vertices, alpha):
    return tuple(
        Fraction(sum(alpha[i] * vertices[i][d] for i in range(4)), 3)
        for d in range(3)
    )


def face(vertices):
    return tuple(sorted(vertices))


def exterior_faces(star):
    counts = Counter()
    for _, vertices in star:
        for omitted in range(4):
            counts[face(vertices[i] for i in range(4) if i != omitted)] += 1
    return {item for item, count in counts.items() if count == 1}


def point_on_triangle(point, triangle):
    """Exact membership for the axis-aligned/unimodular triangles used here."""
    a, b, c = triangle
    u = tuple(b[d] - a[d] for d in range(3))
    v = tuple(c[d] - a[d] for d in range(3))
    normal = (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )
    offset = tuple(point[d] - a[d] for d in range(3))
    if sum(normal[d] * offset[d] for d in range(3)) != 0:
        return False
    # A degree-three control point belongs to the triangle iff it is generated
    # by a cubic barycentric index on its three vertices.
    return any(
        point == tuple(
            Fraction(beta[0] * a[d] + beta[1] * b[d] + beta[2] * c[d], 3)
            for d in range(3)
        )
        for beta in compositions(3, 3)
    )


def bernstein_lambda_derivatives(alpha, lambdas):
    coefficient = Fraction(factorial(3))
    for value in alpha:
        coefficient /= factorial(value)
    derivatives = []
    for differentiated in range(4):
        if alpha[differentiated] == 0:
            derivatives.append(Fraction(0))
            continue
        value = coefficient * alpha[differentiated]
        for i in range(4):
            value *= lambdas[i] ** (alpha[i] - (i == differentiated))
        derivatives.append(value)
    return derivatives


def add(row, column, value):
    updated = row.get(column, Fraction(0)) + value
    if updated:
        row[column] = updated
    else:
        row.pop(column, None)


def rank(rows):
    pivots = {}
    for source in rows:
        row = dict(source)
        while row:
            pivot = min(row)
            if pivot not in pivots:
                scale = row[pivot]
                pivots[pivot] = {
                    column: value / scale for column, value in row.items()
                }
                break
            multiplier = row[pivot]
            for column, value in pivots[pivot].items():
                add(row, column, -multiplier * value)
    return len(pivots)


def boundary_edge(first, second, size=2):
    return any(
        first[d] == second[d] == 0
        or first[d] == second[d] == size
        for d in range(3)
    )


def edge(first, second):
    return tuple(sorted((first, second)))


def audit(vertex, all_tets):
    star = [tet for tet in all_tets if vertex in tet[1]]
    outside = exterior_faces(star)
    indices = tuple(compositions(3, 4))
    all_points = {
        control_point(vertices, alpha)
        for _, vertices in star
        for alpha in indices
    }
    boundary_points = {
        point for point in all_points
        if any(point_on_triangle(point, triangle) for triangle in outside)
    }
    nodes = sorted(all_points - boundary_points)
    node_id = {point: i for i, point in enumerate(nodes)}

    constraints = []
    targets = []
    for sigma, vertices in star:
        grad = gradients(sigma)
        mean = {}
        for alpha in indices:
            point = control_point(vertices, alpha)
            if point not in node_id:
                continue
            for component in range(3):
                # Integral of d(B_alpha^3)/d(lambda_i) is 1/20 whenever
                # alpha_i>0 on a determinant-one tetrahedron.
                value = sum(
                    grad[i][component] for i in range(4) if alpha[i]
                ) / 20
                if value:
                    mean[3 * node_id[point] + component] = value
        constraints.append(mean)
        for local_vertex, geometric_vertex in enumerate(vertices):
            lambdas = tuple(
                Fraction(i == local_vertex) for i in range(4)
            )
            row = {}
            for alpha in indices:
                point = control_point(vertices, alpha)
                if point not in node_id:
                    continue
                derivatives = bernstein_lambda_derivatives(alpha, lambdas)
                for component in range(3):
                    value = sum(
                        derivatives[i] * grad[i][component]
                        for i in range(4)
                    )
                    if value:
                        row[3 * node_id[point] + component] = value
            (targets if geometric_vertex == vertex else constraints).append(row)

    incident_edges = sorted({
        edge(vertex, other)
        for _, vertices in star for other in vertices if other != vertex
    })
    active = [item for item in incident_edges if not boundary_edge(*item)]
    jet_id = {
        (item, component): 3 * i + component
        for i, item in enumerate(active) for component in range(3)
    }
    jet_rows = []
    for sigma, vertices in star:
        grad = gradients(sigma)
        row = {}
        for local_vertex, other in enumerate(vertices):
            if other == vertex:
                continue
            item = edge(vertex, other)
            if item not in active:
                continue
            for component in range(3):
                value = grad[local_vertex][component]
                if value:
                    row[jet_id[(item, component)]] = value
        jet_rows.append(row)

    result = (
        rank(jet_rows),
        3 * len(nodes),
        rank(constraints),
        rank(constraints + targets),
    )
    if result != EXPECTED[len(star)]:
        raise AssertionError((vertex, len(star), result, EXPECTED[len(star)]))
    return len(star), len(active), result


def main():
    all_tets = tets(2)
    representatives = {}
    for vertex in product(range(3), repeat=3):
        star_size = sum(vertex in vertices for _, vertices in all_tets)
        representatives.setdefault(star_size, vertex)
    if set(representatives) != set(EXPECTED):
        raise AssertionError(representatives)
    for star_size in sorted(representatives):
        vertex = representatives[star_size]
        _, active, result = audit(vertex, all_tets)
        print(
            f"star={star_size:2d} vertex={vertex} active_edges={active:2d} "
            f"jet_rank={result[0]:2d} columns={result[1]:3d} "
            f"constraint_rank={result[2]:2d} augmented_rank={result[3]:2d}"
        )
    print("independent Bernstein vertex-algebra audit passed")


if __name__ == "__main__":
    main()
