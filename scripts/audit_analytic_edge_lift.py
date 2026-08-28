#!/usr/bin/env python3
"""Exact, rank-free check of the analytic face-bubble edge construction.

The script is independent of the certificate generator.  It reconstructs the
Freudenthal mesh from coordinate chains, evaluates every displayed bubble on
every tetrahedron edge using Fraction arithmetic, and checks explicit spanning
identities.  It performs no elimination, nullspace, determinant, or rank
calculation.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product


Point = tuple[int, int, int]
Vector = tuple[int, int, int]
Tet = tuple[Point, Point, Point, Point]
Face = tuple[Point, Point, Point]
Edge = tuple[Point, Point]
Pattern = tuple[int, ...]


def point(code: str) -> Point:
    return tuple(int(value) for value in code)


def vector(x: int, y: int, z: int) -> Vector:
    return (x, y, z)


def face(*vertices: Point) -> Face:
    return tuple(sorted(vertices))


def edge(*vertices: Point) -> Edge:
    return tuple(sorted(vertices))


def mesh(size: int = 3) -> tuple[Tet, ...]:
    result = []
    for cell in product(range(size), repeat=3):
        for order in permutations(range(3)):
            current = list(cell)
            vertices = [tuple(current)]
            for direction in order:
                current = current.copy()
                current[direction] += 1
                vertices.append(tuple(current))
            result.append(tuple(vertices))
    return tuple(result)


def det3(matrix) -> int:
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


@cache
def gradients(vertices: Tet):
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


def dot(left, right) -> Fraction:
    return sum((Fraction(left[i]) * right[i] for i in range(3)), Fraction(0))


def add_pattern(*patterns: Pattern) -> Pattern:
    return tuple(sum(values) for values in zip(*patterns))


def scale_pattern(value: int, pattern: Pattern) -> Pattern:
    return tuple(value * entry for entry in pattern)


@dataclass(frozen=True)
class Term:
    triangle: Face
    coefficient: Vector


@dataclass(frozen=True)
class Generator:
    terms: tuple[Term, ...]
    target: Pattern


@dataclass(frozen=True)
class Case:
    name: str
    target_edge: Edge
    endpoint_generators: tuple[tuple[Generator, ...], tuple[Generator, ...]]
    target_basis: tuple[Pattern, ...]
    reconstruction: tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]
    middle_endpoint: int


EX = vector(1, 0, 0)
EY = vector(0, 1, 0)
EZ = vector(0, 0, 1)
ONE = vector(1, 1, 1)


def target_generator(a: Point, b: Point, c: Point, z: Vector, p: Pattern) -> Generator:
    return Generator((Term(face(a, b, c), z),), p)


def cases() -> tuple[Case, ...]:
    p000, p001, p010, p011 = map(point, ("000", "001", "010", "011"))
    p100, p101, p110, p111 = map(point, ("100", "101", "110", "111"))
    p012, p112, p121, p122 = map(point, ("012", "112", "121", "122"))

    boundary_axis_edge = edge(p001, p011)
    boundary_axis_a = (
        target_generator(p001, p011, p111, vector(1, 1, 0), (1, 1, 0)),
        target_generator(p001, p011, p111, EZ, (0, -1, 0)),
        target_generator(p001, p011, p112, ONE, (0, 1, 1)),
    )
    boundary_axis_b = (
        target_generator(p011, p001, p111, EX, (1, 1, 0)),
        target_generator(p011, p001, p112, EX, (0, 0, 1)),
        target_generator(p011, p001, p112, EZ, (0, 1, 0)),
    )

    boundary_diagonal_edge = edge(p000, p011)
    boundary_diagonal_a = (
        target_generator(p000, p011, p111, ONE, (1, 1)),
    )
    boundary_diagonal_b = (
        target_generator(p011, p000, p111, EX, (1, 1)),
    )

    cube_edge = edge(p000, p111)
    cube_a = (
        target_generator(p000, p111, p011, EY, (0, 0, 0, 0, 0, 1)),
        target_generator(p000, p111, p011, EZ, (0, 0, 0, 1, 0, 0)),
        target_generator(p000, p111, p101, EX, (0, 0, 0, 0, 1, 0)),
        target_generator(p000, p111, p101, EZ, (0, 1, 0, 0, 0, 0)),
        target_generator(p000, p111, p110, EX, (0, 0, 1, 0, 0, 0)),
        target_generator(p000, p111, p110, EY, (1, 0, 0, 0, 0, 0)),
    )
    cube_b = (
        target_generator(p111, p000, p001, EX, (0, 0, 0, 0, -1, 0)),
        target_generator(p111, p000, p001, EY, (0, 0, 0, 0, 0, -1)),
        target_generator(p111, p000, p010, EX, (0, 0, -1, 0, 0, 0)),
        target_generator(p111, p000, p010, EZ, (0, 0, 0, -1, 0, 0)),
        target_generator(p111, p000, p100, EY, (-1, 0, 0, 0, 0, 0)),
        target_generator(p111, p000, p100, EZ, (0, -1, 0, 0, 0, 0)),
    )

    interior_axis_edge = edge(p011, p111)
    interior_axis_a = (
        target_generator(p011, p111, p000, EY, (-1, 0, 0, 0, 0, 0)),
        target_generator(p011, p111, p000, EZ, (0, -1, 0, 0, 0, 0)),
        target_generator(p011, p111, p112, EY, (0, 0, 0, 0, 0, -1)),
        target_generator(p011, p111, p112, vector(1, 0, 1), (0, 0, 1, 0, 0, 1)),
        target_generator(p011, p111, p121, EZ, (0, 0, 0, 0, -1, 0)),
        target_generator(p011, p111, p121, vector(1, 1, 0), (0, 0, 0, 1, 1, 0)),
    )
    interior_axis_b = (
        target_generator(p111, p011, p001, EZ, (0, 1, 0, 0, 0, 0)),
        target_generator(p111, p011, p001, vector(1, 1, 0), (0, -1, -1, 0, 0, 0)),
        target_generator(p111, p011, p010, EY, (1, 0, 0, 0, 0, 0)),
        target_generator(p111, p011, p010, vector(1, 0, 1), (-1, 0, 0, -1, 0, 0)),
        target_generator(p111, p011, p122, EY, (0, 0, 0, 0, 0, 1)),
        target_generator(p111, p011, p122, EZ, (0, 0, 0, 0, 1, 0)),
    )

    interior_diagonal_edge = edge(p001, p111)
    interior_diagonal_a = (
        target_generator(p001, p111, p000, EZ, (-1, -1, 0, 0)),
        target_generator(p001, p111, p011, EY, (0, 1, 0, 1)),
        target_generator(p001, p111, p101, EX, (1, 0, 1, 0)),
    )
    interior_diagonal_b = (
        target_generator(p111, p001, p000, ONE, (-1, -1, 0, 0)),
        target_generator(p111, p001, p011, EX, (0, -1, 0, -1)),
        target_generator(p111, p001, p101, EY, (-1, 0, -1, 0)),
    )
    checker_basis = (
        (1, 0, 0, -1),
        (0, 1, 0, 1),
        (0, 0, 1, 1),
    )

    two_tet_edge = edge(p000, p001)
    target_face = face(p000, p001, p111)
    correction_face = face(p000, p011, p111)
    two_tet_a = (
        Generator(
            (Term(target_face, EY), Term(correction_face, EY)),
            (1, 0),
        ),
        Generator(
            (
                Term(target_face, vector(1, 0, 1)),
                Term(correction_face, vector(0, -1, 0)),
            ),
            (0, 1),
        ),
    )
    two_tet_b = (
        target_generator(p001, p000, p111, EX, (0, 1)),
        target_generator(p001, p000, p111, EY, (1, 0)),
    )

    return (
        Case(
            "boundary_face_axis",
            boundary_axis_edge,
            (boundary_axis_a, boundary_axis_b),
            ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
            (
                ((1, 1, 0), (0, -1, 0), (0, 1, 1)),
                ((1, 0, -1), (0, 0, 1), (0, 1, 0)),
            ),
            0,
        ),
        Case(
            "boundary_face_diagonal",
            boundary_diagonal_edge,
            (boundary_diagonal_a, boundary_diagonal_b),
            ((1, 1),),
            (((1,),), ((1,),)),
            0,
        ),
        Case(
            "cube_diagonal",
            cube_edge,
            (cube_a, cube_b),
            tuple(tuple(int(i == j) for i in range(6)) for j in range(6)),
            (
                (
                    (0, 0, 0, 0, 0, 1),
                    (0, 0, 0, 1, 0, 0),
                    (0, 0, 0, 0, 1, 0),
                    (0, 1, 0, 0, 0, 0),
                    (0, 0, 1, 0, 0, 0),
                    (1, 0, 0, 0, 0, 0),
                ),
                (
                    (0, 0, 0, 0, -1, 0),
                    (0, 0, 0, 0, 0, -1),
                    (0, 0, -1, 0, 0, 0),
                    (0, 0, 0, -1, 0, 0),
                    (-1, 0, 0, 0, 0, 0),
                    (0, -1, 0, 0, 0, 0),
                ),
            ),
            0,
        ),
        Case(
            "interior_axis",
            interior_axis_edge,
            (interior_axis_a, interior_axis_b),
            tuple(tuple(int(i == j) for i in range(6)) for j in range(6)),
            (
                (
                    (-1, 0, 0, 0, 0, 0),
                    (0, -1, 0, 0, 0, 0),
                    (0, 0, 1, 1, 0, 0),
                    (0, 0, 0, 0, 1, 1),
                    (0, 0, 0, 0, -1, 0),
                    (0, 0, -1, 0, 0, 0),
                ),
                (
                    (0, 0, 1, 0, 0, 0),
                    (1, 0, 0, 0, 0, 0),
                    (-1, -1, 0, 0, 0, 0),
                    (0, 0, -1, -1, 0, 0),
                    (0, 0, 0, 0, 0, 1),
                    (0, 0, 0, 0, 1, 0),
                ),
            ),
            0,
        ),
        Case(
            "interior_face_diagonal",
            interior_diagonal_edge,
            (interior_diagonal_a, interior_diagonal_b),
            checker_basis,
            (
                ((-1, -1, 0), (0, 1, 0), (1, 1, 1)),
                ((-1, 1, 0), (0, -1, 0), (1, -1, -1)),
            ),
            0,
        ),
        Case(
            "two_tet_box_edge",
            two_tet_edge,
            (two_tet_a, two_tet_b),
            ((1, 0), (0, 1)),
            (
                ((1, 0), (0, 1)),
                ((0, 1), (1, 0)),
            ),
            1,
        ),
    )


def mesh_incidence(global_tets: tuple[Tet, ...]):
    face_to_tets = defaultdict(list)
    edge_to_tets = defaultdict(list)
    for number, vertices in enumerate(global_tets):
        for omitted in range(4):
            face_to_tets[
                face(*(vertices[j] for j in range(4) if j != omitted))
            ].append(number)
        for endpoints in combinations(vertices, 2):
            edge_to_tets[edge(*endpoints)].append(number)
    neighbors = defaultdict(set)
    for adjacent in face_to_tets.values():
        if len(adjacent) == 2:
            first, second = adjacent
            neighbors[first].add(second)
            neighbors[second].add(first)
    return face_to_tets, edge_to_tets, neighbors


def face_patch(star, neighbors):
    patch = set(star)
    for tet_number in tuple(star):
        patch.update(neighbors[tet_number])
    return tuple(sorted(patch))


def monomial_divergence(
    vertices: Tet,
    exponents: dict[Point, int],
    coefficient: Vector,
    lambdas: tuple[Fraction, Fraction, Fraction, Fraction],
) -> Fraction:
    local = {vertex: i for i, vertex in enumerate(vertices)}
    alpha = [exponents.get(vertex, 0) for vertex in vertices]
    result = Fraction(0)
    gradients_here = gradients(vertices)
    for i, exponent in enumerate(alpha):
        if exponent == 0:
            continue
        value = Fraction(exponent)
        for j, other_exponent in enumerate(alpha):
            power = other_exponent - int(i == j)
            if power:
                value *= lambdas[j] ** power
        result += value * dot(coefficient, gradients_here[i])
    return result


def evaluate_generator(
    global_tets,
    face_to_tets,
    star,
    case: Case,
    center: Point,
    other: Point,
    generator: Generator,
    degree: int,
    middle: bool = False,
):
    values = defaultdict(Fraction)
    for term in generator.terms:
        adjacent = face_to_tets[term.triangle]
        if len(adjacent) != 2:
            raise AssertionError((case.name, "face is not interior", term.triangle, adjacent))
        for tet_number in adjacent:
            vertices = global_tets[tet_number]
            if middle:
                third = next(vertex for vertex in term.triangle if vertex not in case.target_edge)
                exponents = {case.target_edge[0]: 2, case.target_edge[1]: 2, third: 1}
            else:
                if center not in term.triangle:
                    raise AssertionError((case.name, "center missing from face", term))
                remaining = [vertex for vertex in term.triangle if vertex != center]
                exponents = {center: degree - 2, remaining[0]: 1, remaining[1]: 1}
            for endpoints in combinations(range(4), 2):
                carrier = edge(vertices[endpoints[0]], vertices[endpoints[1]])
                for node in range(degree):
                    lambdas = [Fraction(0)] * 4
                    lambdas[endpoints[0]] = Fraction(degree - 1 - node, degree - 1)
                    lambdas[endpoints[1]] = Fraction(node, degree - 1)
                    values[(tet_number, carrier, node)] += monomial_divergence(
                        vertices, exponents, term.coefficient, tuple(lambdas)
                    )

    star_order = {tet_number: index for index, tet_number in enumerate(sorted(star))}
    for key, actual in values.items():
        tet_number, carrier, node = key
        expected = Fraction(0)
        if carrier == case.target_edge and tet_number in star_order:
            left = Fraction(degree - 1 - node, degree - 1)
            right = Fraction(node, degree - 1)
            if carrier[0] != case.target_edge[0]:
                raise AssertionError("edge normalization changed")
            if middle:
                mode = left**2 * right**2
            else:
                center_lambda = left if center == carrier[0] else right
                other_lambda = right if center == carrier[0] else left
                mode = center_lambda ** (degree - 2) * other_lambda
            expected = generator.target[star_order[tet_number]] * mode
        if actual != expected:
            raise AssertionError(
                (case.name, center, degree, middle, key, actual, expected, generator)
            )

    # Rows absent from the sparse dictionary are zero.  Explicitly check every
    # target incidence/node so a missing target term cannot pass silently.
    for tet_number in star:
        for node in range(degree):
            key = (tet_number, case.target_edge, node)
            actual = values[key]
            left = Fraction(degree - 1 - node, degree - 1)
            right = Fraction(node, degree - 1)
            if middle:
                mode = left**2 * right**2
            else:
                center_lambda = left if center == case.target_edge[0] else right
                other_lambda = right if center == case.target_edge[0] else left
                mode = center_lambda ** (degree - 2) * other_lambda
            expected = generator.target[star_order[tet_number]] * mode
            if actual != expected:
                raise AssertionError((case.name, "missing target", key, actual, expected))


def check_spanning(case: Case, endpoint_number: int):
    generators = case.endpoint_generators[endpoint_number]
    coefficients_by_basis = case.reconstruction[endpoint_number]
    if len(coefficients_by_basis) != len(case.target_basis):
        raise AssertionError((case.name, endpoint_number, "wrong reconstruction count"))
    for target, coefficients in zip(case.target_basis, coefficients_by_basis):
        if len(coefficients) != len(generators):
            raise AssertionError((case.name, endpoint_number, target, coefficients))
        actual = tuple(
            sum(coefficients[j] * generators[j].target[i] for j in range(len(generators)))
            for i in range(len(target))
        )
        if actual != target:
            raise AssertionError(
                (case.name, endpoint_number, "bad spanning identity", actual, target)
            )


def canonical_check() -> None:
    global_tets = mesh(3)
    face_to_tets, edge_to_tets, neighbors = mesh_incidence(global_tets)
    expected_star_sizes = {
        "boundary_face_axis": 3,
        "boundary_face_diagonal": 2,
        "cube_diagonal": 6,
        "interior_axis": 6,
        "interior_face_diagonal": 4,
        "two_tet_box_edge": 2,
    }

    for case in cases():
        star = tuple(sorted(edge_to_tets[case.target_edge]))
        patch = face_patch(star, neighbors)
        if len(star) != expected_star_sizes[case.name]:
            raise AssertionError((case.name, len(star)))
        for endpoint_number, center in enumerate(case.target_edge):
            other = case.target_edge[1 - endpoint_number]
            check_spanning(case, endpoint_number)
            for generator in case.endpoint_generators[endpoint_number]:
                for degree in (4, 5):
                    evaluate_generator(
                        global_tets,
                        face_to_tets,
                        star,
                        case,
                        center,
                        other,
                        generator,
                        degree,
                    )
                for term in generator.terms:
                    if not set(face_to_tets[term.triangle]).issubset(patch):
                        raise AssertionError((case.name, "term leaves one-ring", term))

        middle_generators = case.endpoint_generators[case.middle_endpoint]
        for generator in middle_generators:
            if any(not set(case.target_edge).issubset(term.triangle) for term in generator.terms):
                raise AssertionError((case.name, "middle family uses borrowed face"))
            evaluate_generator(
                global_tets,
                face_to_tets,
                star,
                case,
                case.target_edge[0],
                case.target_edge[1],
                generator,
                5,
                middle=True,
            )
        print(
            f"{case.name:29s} star={len(star)} "
            f"endpoint_generators="
            f"{len(case.endpoint_generators[0])}/{len(case.endpoint_generators[1])} "
            f"middle={len(middle_generators)} patch={len(patch)}"
        )

    # The remaining incidence type has zero target space by the two-boundary-
    # factor argument; its canonical edge has one incident tetrahedron.
    one_tet_edge = edge(point("003"), point("013"))
    one_tet_star = edge_to_tets[one_tet_edge]
    if len(one_tet_star) != 1:
        raise AssertionError(("one_tet_box_edge", len(one_tet_star)))
    print("one_tet_box_edge              star=1 target_space=0")
    print("rank-free analytic edge construction verified on all seven types")


def edge_kind(target_edge: Edge, star, size: int) -> str:
    increment = tuple(
        sorted(abs(target_edge[1][i] - target_edge[0][i]) for i in range(3))
    )
    boundary_planes = sum(
        target_edge[0][i] == target_edge[1][i] == 0
        or target_edge[0][i] == target_edge[1][i] == size
        for i in range(3)
    )
    lookup = {
        (1, (0, 0, 1), 2): "one_tet_box_edge",
        (2, (0, 0, 1), 2): "two_tet_box_edge",
        (2, (0, 1, 1), 1): "boundary_face_diagonal",
        (3, (0, 0, 1), 1): "boundary_face_axis",
        (4, (0, 1, 1), 0): "interior_face_diagonal",
        (6, (0, 0, 1), 0): "interior_axis",
        (6, (1, 1, 1), 0): "cube_diagonal",
    }
    return lookup[(len(star), increment, boundary_planes)]


def transformed_point(
    vertex: Point, coordinate_order, sign: int, translation: Point
) -> Point:
    return tuple(
        sign * vertex[coordinate_order[d]] + translation[d] for d in range(3)
    )


def transformed_vector(value: Vector, coordinate_order, sign: int) -> Vector:
    return tuple(sign * value[coordinate_order[d]] for d in range(3))


def find_transport(
    case: Case,
    canonical_tets,
    canonical_edge_to_tets,
    target_edge: Edge,
    star,
    global_tets,
    face_to_tets,
    patch,
):
    canonical_star = tuple(sorted(canonical_edge_to_tets[case.target_edge]))
    actual_star_sets = {frozenset(global_tets[index]) for index in star}
    actual_index = {frozenset(vertices): index for index, vertices in enumerate(global_tets)}
    actual_position = {index: number for number, index in enumerate(sorted(star))}

    for coordinate_order in permutations(range(3)):
        for sign in (1, -1):
            for mapped_endpoints in (target_edge, target_edge[::-1]):
                linear_first = tuple(
                    sign * case.target_edge[0][coordinate_order[d]] for d in range(3)
                )
                translation = tuple(
                    mapped_endpoints[0][d] - linear_first[d] for d in range(3)
                )
                transform = lambda vertex: transformed_point(
                    vertex, coordinate_order, sign, translation
                )
                if transform(case.target_edge[1]) != mapped_endpoints[1]:
                    continue
                transformed_star_sets = {
                    frozenset(transform(vertex) for vertex in canonical_tets[index])
                    for index in canonical_star
                }
                if transformed_star_sets != actual_star_sets:
                    continue

                transformed_generators = []
                all_faces_valid = True
                for family in case.endpoint_generators:
                    transformed_family = []
                    for generator in family:
                        pattern = [0] * len(star)
                        for old_position, canonical_index in enumerate(canonical_star):
                            transformed_set = frozenset(
                                transform(vertex)
                                for vertex in canonical_tets[canonical_index]
                            )
                            actual_tet = actual_index[transformed_set]
                            pattern[actual_position[actual_tet]] = generator.target[old_position]
                        terms = []
                        for term in generator.terms:
                            triangle = face(*(transform(vertex) for vertex in term.triangle))
                            adjacent = face_to_tets.get(triangle, ())
                            if len(adjacent) != 2 or not set(adjacent).issubset(patch):
                                all_faces_valid = False
                                break
                            terms.append(
                                Term(
                                    triangle,
                                    transformed_vector(
                                        term.coefficient, coordinate_order, sign
                                    ),
                                )
                            )
                        if not all_faces_valid:
                            break
                        transformed_family.append(
                            Generator(tuple(terms), tuple(pattern))
                        )
                    if not all_faces_valid:
                        break
                    transformed_generators.append(tuple(transformed_family))
                if all_faces_valid:
                    return (
                        transform(case.target_edge[0]),
                        transform(case.target_edge[1]),
                        tuple(transformed_generators),
                    )
    raise AssertionError((case.name, target_edge, "no valid canonical transport"))


def all_placement_check(sizes=range(1, 7)) -> None:
    canonical_tets = mesh(3)
    _, canonical_edge_to_tets, _ = mesh_incidence(canonical_tets)
    case_by_name = {case.name: case for case in cases()}
    total = 0

    for size in sizes:
        global_tets = mesh(size)
        face_to_tets, edge_to_tets, neighbors = mesh_incidence(global_tets)
        checked = 0
        for target_edge, star_list in sorted(edge_to_tets.items()):
            star = tuple(sorted(star_list))
            name = edge_kind(target_edge, star, size)
            if name == "one_tet_box_edge":
                checked += 1
                continue
            case = case_by_name[name]
            patch = set(face_patch(star, neighbors))
            center0, center1, families = find_transport(
                case,
                canonical_tets,
                canonical_edge_to_tets,
                target_edge,
                star,
                global_tets,
                face_to_tets,
                patch,
            )
            transported_case = Case(
                name,
                target_edge,
                families,
                case.target_basis,
                case.reconstruction,
                case.middle_endpoint,
            )
            for endpoint_number, center in enumerate((center0, center1)):
                other = center1 if endpoint_number == 0 else center0
                for generator in families[endpoint_number]:
                    for degree in (4, 5):
                        evaluate_generator(
                            global_tets,
                            face_to_tets,
                            star,
                            transported_case,
                            center,
                            other,
                            generator,
                            degree,
                        )
            middle_family = families[case.middle_endpoint]
            for generator in middle_family:
                evaluate_generator(
                    global_tets,
                    face_to_tets,
                    star,
                    transported_case,
                    target_edge[0],
                    target_edge[1],
                    generator,
                    5,
                    middle=True,
                )
            checked += 1
        expected = 3 * size * (size + 1) ** 2 + 3 * size**2 * (size + 1) + size**3
        if checked != expected:
            raise AssertionError((size, checked, expected))
        total += checked
        print(f"N={size}: transported formulas verified on {checked} edge placements")
    expected_total = sum(
        3 * size * (size + 1) ** 2 + 3 * size**2 * (size + 1) + size**3
        for size in sizes
    )
    if total != expected_total:
        raise AssertionError((total, expected_total))
    print(f"all-placement transport check passed on {total} edges")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--all-placements",
        action="store_true",
        help="also transport and check every edge on the N=1,...,6 grids",
    )
    args = parser.parse_args()
    canonical_check()
    if args.all_placements:
        all_placement_check()


if __name__ == "__main__":
    main()
