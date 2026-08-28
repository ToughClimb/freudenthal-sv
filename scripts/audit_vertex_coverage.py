#!/usr/bin/env python3
"""Independent combinatorial audit of the six vertex-star types.

This script deliberately imports nothing from vertex_star_certificate.py.  It
enumerates Freudenthal tetrahedra directly on N=1,...,6, counts the stars, and
checks the closed formulas used in the manuscript's finite-coverage proof.
It is a redundant reviewer aid, not a substitute for that proof.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import permutations, product


TYPE_BY_STAR = {
    2: "corner_two_tet",
    4: "boundary_edge_four_tet",
    6: "corner_six_tet",
    8: "boundary_edge_eight_tet",
    12: "boundary_face_twelve_tet",
    24: "interior_twenty_four_tet",
}


def freudenthal_tets(size):
    for cell in product(range(size), repeat=3):
        for order in permutations(range(3)):
            current = list(cell)
            vertices = [tuple(current)]
            for direction in order:
                current = current.copy()
                current[direction] += 1
                vertices.append(tuple(current))
            yield tuple(vertices)


def expected(size):
    interior = size - 1
    counts = Counter({
        "corner_six_tet": 2,
        "corner_two_tet": 6,
    })
    if interior:
        counts.update({
            "boundary_edge_eight_tet": 6 * interior,
            "boundary_edge_four_tet": 6 * interior,
            "boundary_face_twelve_tet": 6 * interior**2,
            "interior_twenty_four_tet": interior**3,
        })
    return counts


def main():
    observed_star_sizes = set()
    for size in range(1, 7):
        stars = defaultdict(int)
        for tet in freudenthal_tets(size):
            for vertex in tet:
                stars[vertex] += 1
        if len(stars) != (size + 1) ** 3:
            raise AssertionError((size, len(stars), (size + 1) ** 3))
        counts = Counter()
        for vertex, star_size in stars.items():
            if star_size not in TYPE_BY_STAR:
                raise AssertionError((size, vertex, star_size))
            counts[TYPE_BY_STAR[star_size]] += 1
            observed_star_sizes.add(star_size)
        if counts != expected(size):
            raise AssertionError((size, counts, expected(size)))
        print(f"N={size}: {len(stars)} vertices; {dict(sorted(counts.items()))}")
    if observed_star_sizes != set(TYPE_BY_STAR):
        raise AssertionError(observed_star_sizes)
    print("vertex finite-coverage audit passed: exactly six star types")


if __name__ == "__main__":
    main()
