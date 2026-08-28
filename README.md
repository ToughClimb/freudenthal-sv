# Freudenthal–Scott–Vogelius exact verification

This directory contains the exact-arithmetic verification files accompanying
the manuscript on uniform Scott–Vogelius stability on three-dimensional
Freudenthal meshes in polynomial degrees 4 and 5. The journal-specific article
source and compiled PDF are maintained separately.

## Repository scope

This repository contains only the verification programs, deterministic
certificate data, inspection utilities, and reproduction instructions needed
to check the computations described below. It does not contain manuscript
source, author contact information, local execution logs, third-party papers,
review correspondence, or development discussions.

The software and original accompanying material are distributed under the
GNU General Public License, version 3 or any later version
(`GPL-3.0-or-later`); see `LICENSE`.
Citation metadata for the software and accompanying manuscript is provided in
`CITATION.cff`. A journal DOI and an archival software DOI may be added after
they have been assigned.

Copyright (C) 2026 Hanbing Liang and Fujun Liu. You may redistribute and/or
modify the covered material under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the License,
or (at your option) any later version. The GPL source-sharing obligations apply
when a covered work is conveyed or distributed; private execution and private
modification alone do not require publication. The license governs the
copyrightable repository contents, not the mathematical statements themselves
or an independent implementation of those statements.

## Mathematical proof

The proof in the manuscript is analytic. Its local structure is the
barycentric skeleton-bubble calculus:

| stage | analytic mechanism |
|---|---|
| element means | Bogovskii lifting, Scott–Zhang interpolation, and cubic face-flux bubbles |
| vertices | edge-jet compatibility, cubic edge-star bubbles, and dual-tree face transfers |
| edges | endpoint and middle face bubbles spanning the seven geometric incidence types |
| mean-preserving edge assembly | eleven explicit quartic Bernstein fields on a two-cube macroelement, with determinant `-6` |
| element interiors | the quartic/quintic bubble isomorphism `p ↦ div(b_T p)` |

In particular, Lemmas 2.4 and 3.3 are proved by explicit barycentric
constructions and do not depend on rank computations. The quartic macroelement
lift is also explicit: the manuscript lists all eleven fields, its integer
mean matrix, and the determinant. Zhang is cited for the established range
`k >= 6` and for historical comparison; no mesh-specific vertex or edge lemma
from Zhang is used for degrees 4 and 5.

## Exact verification

The computations are independent checks and reproducibility support; they are
not hypotheses or finite-enumeration steps in the analytic proof.

| program | exact input | verified statement |
|---|---|---|
| `scripts/audit_analytic_vertex_lift.py` | six canonical vertex stars; optionally every vertex for `N=1,...,6` | edge-jet realization, zero off-target vertex divergence, two-tetrahedron face transfers, dual-tree connectivity, and preservation of every element mean |
| `scripts/audit_analytic_edge_lift.py` | seven canonical edge types; optionally every edge for `N=1,...,6` | endpoint and middle face-bubble identities, all spill cancellations, the two-tetrahedron boundary construction, and transported placements |
| `certificates/macro_mean_certificate.py` | the `C^0 P_4` space on the twelve-tetrahedron two-cube macroelement | zero broken edge traces for the eleven displayed fields, the displayed mean matrix, determinant `-6`, and full-space rank consistency |
| `certificates/p5_two_tet_transfer.py` | the explicit quintic field on a face-adjacent tetrahedron pair | conformity, exterior-zero trace, zero divergence on all edges, means `(1,-1)`, squared seminorm `504/11`, and the distinguished-edge geometry |
| `certificates/low_degree_bubble_isomorphism.py` | the maps `p ↦ div(b_T p)` for affine degrees 0 and 1 | target dimensions 3 and 12, zero edge traces, zero mean, and bijectivity |
| `certificates/vertex_star_certificate.py` | all vertex stars on the `N=1,2,3` grids | exact image dimensions, rational annihilators, and rational nodal realizations for 99 records |
| `certificates/edge_star_certificate.py` | every edge on the `N=3,4,5` grids in degrees 4 and 5 | equality of source and supported trace images for 3996 degree-specific records |

All core assembly and elimination use `fractions.Fraction`. SymPy is used only
for exact symbolic differentiation, integration, substitution, and rational
linear algebra. The suite uses neither floating-point tolerances nor random
choices.

## Reproduce the suite

Python 3.10 or newer is required. Dependency versions and package hashes are
pinned in `certificates/requirements.txt`.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install --require-hashes \
    -r certificates/requirements.txt
.venv/bin/python scripts/run_all.py
```

An equivalent `uv` setup is:

```sh
uv venv --python 3.12 .venv
uv pip sync --require-hashes --python .venv/bin/python \
    certificates/requirements.txt
.venv/bin/python scripts/run_all.py
```

The complete single-core run takes approximately twenty minutes on the
reference system, almost entirely in the 3996 exact edge-star records. It also
checks the analytic formulas at all 783 vertices and all 3969 edges on the
grids `N=1,...,6`.

For a short environment and assembly check, run:

```sh
.venv/bin/python scripts/run_all.py --representatives
```

This evaluates the six canonical vertex states, the seven canonical edge
types, all short symbolic checks, the complete 99-record vertex payload, and
42 representative edge records. It is not the exhaustive record generation.

## Configuration identity and record navigation

The edge classifications refer to different mathematical objects:

| level | count |
|---|---:|
| geometric incidence types | 7 |
| source configurations modulo translation and coordinate permutation | 85 |
| conservative coverage states retaining patch-boundary flags | 180 |
| geometric edge placements on `N=3,4,5` | 1998 |
| degree-specific records | 3996 |

The edge payload uses schema `freudenthal-edge-star-v2`. Each record stores a
stable identifier such as `N5:e(1,2,3)-(2,2,3):k4`, the incidence and coverage
class, concrete grid/edge/degree, boundary flags, geometry and matrix hashes,
exact ranks, the rational target-annihilator RREF, and modular-minor metadata.
The companion summary maps every record to its coverage class.

Useful read-only queries are:

```sh
.venv/bin/python scripts/inspect_edge_star.py --validate
.venv/bin/python scripts/inspect_edge_star.py --list-configurations
.venv/bin/python scripts/inspect_edge_star.py \
    --record 'N5:e(1,2,3)-(2,2,3):k4'
.venv/bin/python scripts/inspect_vertex_star.py --validate
.venv/bin/python scripts/inspect_vertex_star.py --operators
.venv/bin/python scripts/audit_analytic_vertex_lift.py --all-placements
.venv/bin/python scripts/audit_analytic_edge_lift.py --all-placements
```

Generated JSON omits timestamps and runtimes, so identical source produces
byte-identical mathematical payloads. `SHA256SUMS` records the shipped source
code, scripts, and certificate data. Verify it with:

```sh
sha256sum -c SHA256SUMS
```

The preparation workspace used `uv` with CPython 3.14.4. The verification
scripts themselves support Python 3.10 or newer as stated above.
