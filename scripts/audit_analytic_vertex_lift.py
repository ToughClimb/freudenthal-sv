#!/usr/bin/env python3
"""Exact, rank-free check of the analytic cubic vertex-star construction.

The check is independent of the certificate generator.  It uses only the
coordinate-chain definition of the Freudenthal mesh and exact rational
simplex integration formulas.  No row reduction or rank computation occurs.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from fractions import Fraction
from itertools import combinations, permutations, product


Point = tuple[int, int, int]
Tet = tuple[Point, Point, Point, Point]
Face = tuple[Point, Point, Point]
Edge = tuple[Point, Point]
Vector = tuple[Fraction, Fraction, Fraction]


def mesh(size: int = 2) -> tuple[Tet, ...]:
    out: list[Tet] = []
    for cell in product(range(size), repeat=3):
        for order in permutations(range(3)):
            point = list(cell)
            vertices = [tuple(point)]
            for direction in order:
                point = point.copy()
                point[direction] += 1
                vertices.append(tuple(point))
            out.append(tuple(vertices))
    return tuple(out)


def det3(matrix) -> int:
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def gradients(vertices: Tet) -> tuple[Vector, ...]:
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
            cofactor = (-1) ** (i + j) * (
                minor[0][0] * minor[1][1] - minor[0][1] * minor[1][0]
            )
            row.append(Fraction(cofactor, determinant))
        inverse.append(tuple(row))
    return (
        tuple(-sum(inverse[i][d] for i in range(3)) for d in range(3)),
    ) + tuple(inverse)


def volume(vertices: Tet) -> Fraction:
    matrix = [
        [vertices[j + 1][i] - vertices[0][i] for j in range(3)]
        for i in range(3)
    ]
    return Fraction(abs(det3(matrix)), 6)


def add(left: Vector, right: Vector) -> Vector:
    return tuple(left[i] + right[i] for i in range(3))


def scale(value: Fraction, vector: Vector) -> Vector:
    return tuple(value * entry for entry in vector)


def dot(left: Vector, right: Vector) -> Fraction:
    return sum((left[i] * right[i] for i in range(3)), Fraction(0))


def edge(first: Point, second: Point) -> Edge:
    return tuple(sorted((first, second)))


def face(vertices) -> Face:
    return tuple(sorted(vertices))


def boundary_edge(item: Edge, size: int = 2) -> bool:
    return any(
        item[0][direction] == item[1][direction] == 0
        or item[0][direction] == item[1][direction] == size
        for direction in range(3)
    )


def star_dual(star: tuple[Tet, ...]):
    incidence: dict[Face, list[int]] = defaultdict(list)
    for tet_number, vertices in enumerate(star):
        for omitted in range(4):
            incidence[face(vertices[i] for i in range(4) if i != omitted)].append(
                tet_number
            )
    adjacency: dict[int, list[tuple[int, Face]]] = defaultdict(list)
    for triangle, pair in incidence.items():
        if len(pair) == 2:
            first, second = pair
            adjacency[first].append((second, triangle))
            adjacency[second].append((first, triangle))
    return adjacency, incidence


def face_transfer(star: tuple[Tet, ...], triangle: Face, first: int, second: int):
    """Return a constant vector whose face bubble has means (+1,-1)."""
    mean_vectors = []
    for tet_number in (first, second):
        vertices = star[tet_number]
        grad = gradients(vertices)
        local = [vertices.index(vertex) for vertex in triangle]
        # Integral_T grad(lambda_i lambda_j lambda_k)
        # = |T|/20 * (grad lambda_i + grad lambda_j + grad lambda_k).
        vector = (Fraction(0), Fraction(0), Fraction(0))
        for index in local:
            vector = add(vector, grad[index])
        mean_vectors.append(scale(volume(vertices) / 20, vector))
    if add(mean_vectors[0], mean_vectors[1]) != (0, 0, 0):
        raise AssertionError((triangle, mean_vectors))
    norm_square = dot(mean_vectors[0], mean_vectors[0])
    coefficient = scale(Fraction(1, 1) / norm_square, mean_vectors[0])
    if dot(coefficient, mean_vectors[0]) != 1:
        raise AssertionError("failed to normalize face transfer")
    if dot(coefficient, mean_vectors[1]) != -1:
        raise AssertionError("face transfer has incorrect opposite mean")
    return coefficient


def raw_mean(vertices: Tet, target: Point, other: Point, component: int) -> Fraction:
    if target not in vertices or other not in vertices:
        return Fraction(0)
    grad = gradients(vertices)
    i = vertices.index(target)
    j = vertices.index(other)
    # Integral_T grad(lambda_i^2 lambda_j)
    # = |T|/10 * (grad lambda_i + grad lambda_j).
    return volume(vertices) / 10 * (grad[i][component] + grad[j][component])


def raw_vertex_divergence(
    vertices: Tet,
    evaluation_vertex: Point,
    target: Point,
    other: Point,
    component: int,
) -> Fraction:
    if target not in vertices or other not in vertices:
        return Fraction(0)
    i = vertices.index(target)
    j = vertices.index(other)
    r = vertices.index(evaluation_vertex)
    lambdas = [Fraction(index == r) for index in range(4)]
    grad = gradients(vertices)
    return (
        2 * lambdas[i] * lambdas[j] * grad[i][component]
        + lambdas[i] ** 2 * grad[j][component]
    )


def verify_state(target: Point, global_tets: tuple[Tet, ...], size: int = 2):
    star = tuple(vertices for vertices in global_tets if target in vertices)
    incident = sorted({
        edge(target, other)
        for vertices in star
        for other in vertices
        if other != target
    })
    active = [item for item in incident if not boundary_edge(item, size)]
    adjacency, incidence = star_dual(star)

    parent = {0: None}
    parent_face: dict[int, Face] = {}
    order = []
    queue = deque([0])
    while queue:
        current = queue.popleft()
        order.append(current)
        for neighbour, triangle in adjacency[current]:
            if neighbour in parent:
                continue
            parent[neighbour] = current
            parent_face[neighbour] = triangle
            queue.append(neighbour)
    if len(parent) != len(star):
        raise AssertionError((target, "disconnected dual graph", len(parent), len(star)))

    for triangle, pair in incidence.items():
        if len(pair) == 2:
            if target not in triangle:
                raise AssertionError((target, triangle, "interior face omits target"))
            face_transfer(star, triangle, pair[0], pair[1])

    generators = 0
    for item in active:
        other = item[1] if item[0] == target else item[0]
        for component in range(3):
            generators += 1
            means = [raw_mean(vertices, target, other, component) for vertices in star]
            if sum(means, Fraction(0)) != 0:
                raise AssertionError((target, item, component, means))

            # Check D_a W = A_a s and B_a W = 0 directly at every vertex.
            for vertices in star:
                expected = Fraction(0)
                if other in vertices:
                    expected = gradients(vertices)[vertices.index(other)][component]
                actual = raw_vertex_divergence(
                    vertices, target, target, other, component
                )
                if actual != expected:
                    raise AssertionError((target, item, component, actual, expected))
                for vertex in vertices:
                    if vertex == target:
                        continue
                    value = raw_vertex_divergence(
                        vertices, vertex, target, other, component
                    )
                    if value:
                        raise AssertionError((target, item, component, vertex, value))

            # Route the raw means to zero on the fixed dual spanning tree.
            routed = means[:]
            for child in reversed(order[1:]):
                current = routed[child]
                if current:
                    triangle = parent_face[child]
                    parent_tet = parent[child]
                    if parent_tet is None:
                        raise AssertionError("non-root child without parent")
                    transfer = face_transfer(star, triangle, child, parent_tet)
                    # The normalized transfer is +1 on child and -1 on parent.
                    if not transfer:
                        raise AssertionError("empty transfer")
                    routed[child] -= current
                    routed[parent_tet] += current
            if any(routed):
                raise AssertionError((target, item, component, routed))

    return len(star), len(active), generators, len(incidence)


def canonical_check() -> None:
    global_tets = mesh(2)
    representatives: dict[int, Point] = {}
    for target in product(range(3), repeat=3):
        count = sum(target in vertices for vertices in global_tets)
        representatives.setdefault(count, target)
    if set(representatives) != {2, 4, 6, 8, 12, 24}:
        raise AssertionError(representatives)

    for star_size in sorted(representatives):
        target = representatives[star_size]
        result = verify_state(target, global_tets)
        print(
            f"star={result[0]:2d} target={target} active_edges={result[1]:2d} "
            f"edge-component_generators={result[2]:2d} faces={result[3]:2d}"
        )
    print("rank-free analytic vertex construction verified on all six states")


def all_placement_check(sizes=range(1, 7)) -> None:
    expected_sizes = {2, 4, 6, 8, 12, 24}
    total = 0
    for size in sizes:
        global_tets = mesh(size)
        counts: dict[int, int] = defaultdict(int)
        for target in product(range(size + 1), repeat=3):
            star_size, _, _, _ = verify_state(target, global_tets, size)
            if star_size not in expected_sizes:
                raise AssertionError((size, target, star_size))
            counts[star_size] += 1
            total += 1

        expected = {
            2: 6,
            4: 6 * (size - 1),
            6: 2,
            8: 6 * (size - 1),
            12: 6 * (size - 1) ** 2,
            24: (size - 1) ** 3,
        }
        expected = {key: value for key, value in expected.items() if value}
        if dict(counts) != expected:
            raise AssertionError((size, dict(counts), expected))
        if sum(counts.values()) != (size + 1) ** 3:
            raise AssertionError((size, dict(counts)))
        print(
            f"N={size}: analytic formulas verified on "
            f"{sum(counts.values())} vertex placements"
        )
    print(f"all-placement vertex check passed on {total} vertices")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--all-placements",
        action="store_true",
        help="also check every vertex on the N=1,...,6 grids",
    )
    args = parser.parse_args()
    canonical_check()
    if args.all_placements:
        all_placement_check()


if __name__ == "__main__":
    main()
