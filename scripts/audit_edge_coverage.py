#!/usr/bin/env python3
"""Independent finite-coverage audit for Freudenthal edge-star geometry.

This script deliberately imports nothing from edge_star_certificate.py. It
reconstructs the integer mesh, edge stars, face-neighbour rings, symmetry
identities, and span table, then checks stabilization from N=5 to N=6. The
manuscript's finite-coverage lemma is the proof; this is a fast regression and
reviewer aid for its finite case ledger.
"""

from __future__ import annotations

import json
from collections import defaultdict
from itertools import permutations, product


GRIDS = (3, 4, 5, 6)
EXPECTED_EDGES = {3: 279, 4: 604, 5: 1115, 6: 1854}
EXPECTED_SOURCE_CLASSES = {3: 64, 4: 85, 5: 85, 6: 85}
EXPECTED_COVERAGE_CLASSES = {3: 64, 4: 129, 5: 165, 6: 165}
EXPECTED_MAXIMUM_SPANS = {
    "one_tet_box_edge": ((1, 1, 1), (1, 1, 1)),
    "two_tet_box_edge": ((1, 1, 1), (1, 1, 2)),
    "boundary_face_diagonal": ((1, 1, 1), (1, 2, 2)),
    "boundary_face_axis": ((1, 1, 2), (1, 2, 2)),
    "interior_face_diagonal": ((1, 1, 2), (2, 3, 3)),
    "interior_axis": ((1, 2, 2), (2, 2, 3)),
    "cube_diagonal": ((1, 1, 1), (3, 3, 3)),
}


def mesh(n):
    tetrahedra=[]
    for cell in product(range(n), repeat=3):
        for order in permutations(range(3)):
            point=list(cell)
            vertices=[tuple(point)]
            for direction in order:
                point=point.copy()
                point[direction]+=1
                vertices.append(tuple(point))
            tetrahedra.append(tuple(vertices))
    return tuple(tetrahedra)


def incidence(n):
    tetrahedra=mesh(n)
    edge_to_tets=defaultdict(set)
    face_to_tets=defaultdict(set)
    for number,tetrahedron in enumerate(tetrahedra):
        for omitted in range(4):
            face=tuple(sorted(
                tetrahedron[i] for i in range(4) if i != omitted
            ))
            face_to_tets[face].add(number)
        for i in range(4):
            for j in range(i):
                edge=tuple(sorted((tetrahedron[i],tetrahedron[j])))
                edge_to_tets[edge].add(number)
    neighbours=defaultdict(set)
    for incident in face_to_tets.values():
        for number in incident:
            neighbours[number].update(incident-{number})
    return tetrahedra,edge_to_tets,neighbours


def one_ring(star, neighbours):
    patch=set(star)
    for number in tuple(patch):
        patch.update(neighbours[number])
    return tuple(sorted(patch))


def edge_kind(edge, star, n):
    increment=tuple(sorted(
        abs(edge[1][i]-edge[0][i]) for i in range(3)
    ))
    boundary_planes=sum(
        edge[0][i]+edge[1][i] in (0,2*n) for i in range(3)
    )
    lookup={
        (1,(0,0,1),2):"one_tet_box_edge",
        (2,(0,0,1),2):"two_tet_box_edge",
        (2,(0,1,1),1):"boundary_face_diagonal",
        (3,(0,0,1),1):"boundary_face_axis",
        (4,(0,1,1),0):"interior_face_diagonal",
        (6,(0,0,1),0):"interior_axis",
        (6,(1,1,1),0):"cube_diagonal",
    }
    return lookup[(len(star),increment,boundary_planes)]


def sorted_span(tetrahedra, selected):
    vertices=[vertex for i in selected for vertex in tetrahedra[i]]
    return tuple(sorted(
        max(vertex[d] for vertex in vertices)
        - min(vertex[d] for vertex in vertices)
        for d in range(3)
    ))


def canonical_state(n, edge, star, patch, tetrahedra, *, coverage):
    selected=patch if coverage else tuple(sorted(star))
    candidates=[]
    for order in permutations(range(3)):
        vertices=[
            tuple(vertex[order[d]] for d in range(3))
            for i in selected for vertex in tetrahedra[i]
        ]
        minima=tuple(min(vertex[d] for vertex in vertices) for d in range(3))

        def transform(vertex):
            return tuple(vertex[order[d]]-minima[d] for d in range(3))

        state={
            "edge":sorted(transform(vertex) for vertex in edge),
            "star":sorted(
                sorted(transform(vertex) for vertex in tetrahedra[i])
                for i in star
            ),
            "physical_planes":[],
        }
        if coverage:
            state["patch"]=sorted(
                sorted(transform(vertex) for vertex in tetrahedra[i])
                for i in patch
            )
        for old_direction in range(3):
            for value in (0,n):
                if any(
                    vertex[old_direction] == value
                    for i in selected for vertex in tetrahedra[i]
                ):
                    new_direction=order.index(old_direction)
                    state["physical_planes"].append(
                        [new_direction,value-minima[new_direction]]
                    )
        state["physical_planes"].sort()
        candidates.append(json.dumps(
            state,sort_keys=True,separators=(",",":"),
        ))
    return min(candidates)


def componentwise_maximum(values):
    return tuple(max(value[i] for value in values) for i in range(3))


def main():
    source_classes={}
    coverage_classes={}
    maximum_spans={}
    for n in GRIDS:
        tetrahedra,edges,neighbours=incidence(n)
        if len(edges) != EXPECTED_EDGES[n]:
            raise AssertionError((n,len(edges),EXPECTED_EDGES[n]))
        sources=set()
        coverages=set()
        spans=defaultdict(lambda: [set(),set()])
        for edge,star in edges.items():
            patch=one_ring(star,neighbours)
            kind=edge_kind(edge,star,n)
            sources.add(canonical_state(
                n,edge,star,patch,tetrahedra,coverage=False,
            ))
            coverages.add(canonical_state(
                n,edge,star,patch,tetrahedra,coverage=True,
            ))
            spans[kind][0].add(sorted_span(tetrahedra,star))
            spans[kind][1].add(sorted_span(tetrahedra,patch))
        source_classes[n]=sources
        coverage_classes[n]=coverages
        if len(sources) != EXPECTED_SOURCE_CLASSES[n]:
            raise AssertionError(("source",n,len(sources)))
        if len(coverages) != EXPECTED_COVERAGE_CLASSES[n]:
            raise AssertionError(("coverage",n,len(coverages)))
        maximum_spans={
            kind:(componentwise_maximum(values[0]),componentwise_maximum(values[1]))
            for kind,values in spans.items()
        }
        print(
            f"N={n}: edges={len(edges)}, source_classes={len(sources)}, "
            f"coverage_classes={len(coverages)}"
        )

    if source_classes[5] != source_classes[6]:
        raise AssertionError("source classes do not stabilize at N=5")
    if coverage_classes[5] != coverage_classes[6]:
        raise AssertionError("coverage classes do not stabilize at N=5")
    if len(set().union(*(coverage_classes[n] for n in (3,4,5)))) != 180:
        raise AssertionError("unexpected N=3,4,5 coverage-class union")
    if maximum_spans != EXPECTED_MAXIMUM_SPANS:
        raise AssertionError((maximum_spans,EXPECTED_MAXIMUM_SPANS))

    print("maximum sorted spans (star, one-ring):")
    for kind,spans in sorted(maximum_spans.items()):
        print(f"  {kind}: {spans[0]}, {spans[1]}")
    print("independent finite-coverage geometry audit passed")


if __name__ == "__main__":
    main()
