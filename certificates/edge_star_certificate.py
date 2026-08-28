#!/usr/bin/env python3
"""Self-contained exact certificate for the k=4,5 Freudenthal edge stage.

For every one of the seven local edge types this script compares two maps.
``X_e`` is the restriction of the actual continuous P_k velocity space to the
tetrahedral star of e: artificial patch-boundary traces are free and only true
box-boundary nodes are set to zero.  ``Y_e`` consists of continuous P_k
velocities on star(e) plus its face-neighbour one-ring, zero on the *whole*
patch exterior, and therefore extendible by zero.  In X_e we impose zero broken
vertex divergence.  In Y_e we impose zero divergence at every skeleton node
except the interior nodes of e.  Exact rank equality proves that Y_e realizes
every edge trace that can arise from X_e after the vertex stage, without any
unintended skeleton write.

No package outside the Python standard library is imported.  Fraction
elimination supplies exact-Q upper bounds; a selected nonzero minor modulo
1,000,003 is recorded as an independent lower-bound witness.
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


P = tuple[int, int, int]

SCHEMA_VERSION = "freudenthal-edge-star-v2"
GRIDS = (3, 4, 5)
DEGREES = (4, 5)
MODULUS = 1_000_003
EXPECTED_EDGE_COUNTS = {3: 279, 4: 604, 5: 1115}
EXPECTED_SOURCE_CONFIGURATION_COUNTS = {3: 64, 4: 85, 5: 85}
EXPECTED_COVERAGE_CONFIGURATION_COUNTS = {3: 64, 4: 129, 5: 165}
EXPECTED_SOURCE_CONFIGURATION_UNION = 85
EXPECTED_COVERAGE_CONFIGURATION_UNION = 180
EXPECTED_TYPE_COUNTS = {
    3: {
        "boundary_face_axis": 72,
        "boundary_face_diagonal": 54,
        "cube_diagonal": 27,
        "interior_axis": 36,
        "interior_face_diagonal": 54,
        "one_tet_box_edge": 18,
        "two_tet_box_edge": 18,
    },
    4: {
        "boundary_face_axis": 144,
        "boundary_face_diagonal": 96,
        "cube_diagonal": 64,
        "interior_axis": 108,
        "interior_face_diagonal": 144,
        "one_tet_box_edge": 24,
        "two_tet_box_edge": 24,
    },
    5: {
        "boundary_face_axis": 240,
        "boundary_face_diagonal": 150,
        "cube_diagonal": 125,
        "interior_axis": 240,
        "interior_face_diagonal": 300,
        "one_tet_box_edge": 30,
        "two_tet_box_edge": 30,
    },
}


def comps(n: int, parts: int):
    if parts == 1:
        yield (n,); return
    for a in range(n + 1):
        for b in comps(n - a, parts - 1): yield (a,) + b


@dataclass(frozen=True)
class Tet:
    vertices: tuple[P, P, P, P]


def mesh(shape: P):
    out = []
    for cell in product(*(range(n) for n in shape)):
        for sig in permutations(range(3)):
            x = list(cell); vs = [tuple(x)]
            for d in sig: x = x.copy(); x[d] += 1; vs.append(tuple(x))
            out.append(Tet(tuple(vs)))
    return tuple(out)


def det3(a):
    return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])


def grads(v):
    b = [[v[j+1][i]-v[0][i] for j in range(3)] for i in range(3)]; d = det3(b)
    inv = []
    for i in range(3):
        r = []
        for j in range(3):
            m = [[b[x][y] for y in range(3) if y != i] for x in range(3) if x != j]
            r.append(Fraction(((-1)**(i+j))*(m[0][0]*m[1][1]-m[0][1]*m[1][0]), d))
        inv.append(tuple(r))
    return (tuple(-sum(inv[i][d] for i in range(3)) for d in range(3)),) + tuple(inv)


def node(v, a, k): return tuple(Fraction(sum(a[i]*v[i][d] for i in range(4)), k) for d in range(3))


def factor(a, k, x):
    c = [Fraction(1)]
    for j in range(a):
        z = [Fraction(0)]*(len(c)+1)
        for i, q in enumerate(c): z[i] -= j*q; z[i+1] += k*q
        c = z
    c = [q/factorial(a) for q in c]
    return sum(q*x**i for i,q in enumerate(c)), sum(i*q*x**(i-1) for i,q in enumerate(c) if i)


def face(v): return tuple(sorted(v))
def edge(v): return tuple(sorted(v))


def exterior_faces(tets):
    c = defaultdict(int)
    for t in tets:
        for omit in range(4): c[face(t.vertices[i] for i in range(4) if i != omit)] += 1
    return {f for f,n in c.items() if n == 1}


def face_nodes(f, k):
    for a in comps(k, 3): yield tuple(Fraction(sum(a[i]*f[i][d] for i in range(3)), k) for d in range(3))


def physical(point, shape): return any(point[d] == 0 or point[d] == shape[d] for d in range(3))


def assemble(k: int, shape: P, global_tets: tuple[Tet, ...], selected, mode: str):
    """Rows of actual CG_k^3 divergence in broken P_(k-1) nodal coordinates."""
    ts = tuple(global_tets[i] for i in selected); vi = tuple(comps(k,4)); qi = tuple(comps(k-1,4))
    outside = exterior_faces(ts)
    forbidden = set()
    for f in outside:
        for x in face_nodes(f,k):
            if mode == 'supported' or (mode == 'source' and physical(x,shape)): forbidden.add(x)
    ids = {}
    for t in ts:
        for a in vi:
            x=node(t.vertices,a,k)
            # This is the exact restriction of global H^1_0: a CG node on the
            # physical box boundary is zero, regardless of how the selected
            # local patch happens to expose it.
            if mode == 'source' and physical(x,shape): continue
            if x not in forbidden: ids.setdefault(x,len(ids))
    cache={(a,b):factor(a,k,Fraction(b,k-1)) for a in range(k+1) for b in range(k)}
    rows=[]
    for t in ts:
        g=grads(t.vertices)
        for b in qi:
            row={}
            for a in vi:
                x=node(t.vertices,a,k)
                if x not in ids: continue
                dl=[]
                for i in range(4):
                    q=cache[a[i],b[i]][1]
                    for j in range(4):
                        if i != j: q *= cache[a[j],b[j]][0]
                    dl.append(q)
                for d in range(3):
                    q=sum((dl[i]*g[i][d] for i in range(4)),Fraction(0))
                    if q: row[3*ids[x]+d]=q
            rows.append(row)
    return ts, qi, rows, 3*len(ids)


def skeleton(ts, qi, rows):
    ans=[]; b=len(qi)
    for t,T in enumerate(ts):
        for j,a in enumerate(qi):
            active=tuple(i for i,q in enumerate(a) if q)
            if len(active)<=2: ans.append((t,j,tuple(sorted(T.vertices[i] for i in active)),a,rows[t*b+j]))
    return ans


def rank_q(rows):
    piv={}; rank=0
    for original in rows:
        r=dict(original)
        while r:
            p=min(r)
            if p not in piv:
                z=r[p]; piv[p]={j:q/z for j,q in r.items()}; rank+=1; break
            z=r[p]
            for j,q in piv[p].items():
                w=r.get(j,Fraction(0))-z*q
                if w:r[j]=w
                else:r.pop(j,None)
    return rank


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def fmod(q, p):
    denominator = q.denominator % p
    if denominator == 0:
        raise ArithmeticError(
            f"rational denominator {q.denominator} is not invertible modulo {p}"
        )
    return (q.numerator % p) * pow(denominator, p - 2, p) % p


def check_denominators(rows, p=MODULUS):
    for row in rows:
        for value in row.values():
            if value.denominator % p == 0:
                raise ArithmeticError(
                    f"rational denominator {value.denominator} is not invertible modulo {p}"
                )


def minor(rows, p=MODULUS):
    if not is_prime(p):
        raise ValueError(f"modular witness modulus must be prime, got {p}")
    piv={}; sr=[]; sc=[]
    for i,orig in enumerate(rows):
        r={}
        for j, q in orig.items():
            value = fmod(q, p)
            if value:
                r[j] = value
        while r:
            c=min(r)
            if c not in piv:
                z=pow(r[c],p-2,p); piv[c]={j:q*z%p for j,q in r.items() if q*z%p}; sr.append(i);sc.append(c);break
            z=r[c]
            for j,q in piv[c].items():
                w=(r.get(j,0)-z*q)%p
                if w:r[j]=w
                else:r.pop(j,None)
    a=[[fmod(rows[i].get(j,Fraction(0)),p) for j in sc] for i in sr]; det=1
    for j in range(len(sc)):
        i=next(i for i in range(j,len(sc)) if a[i][j])
        if i!=j:a[i],a[j]=a[j],a[i];det=-det
        z=a[j][j];det=det*z%p; iz=pow(z,p-2,p)
        for i in range(j+1,len(sc)):
            if a[i][j]:
                z=a[i][j]*iz%p
                for l in range(j+1,len(sc)):a[i][l]=(a[i][l]-z*a[j][l])%p
    det %= p
    if len(sc) and det == 0:
        raise AssertionError("selected modular minor is singular")
    return {'prime':p,'rank':len(sc),'determinant_mod_prime':det,'row_indices':sr,'column_indices':sc}


def hrows(rows):
    h=sha256()
    for i,r in enumerate(rows):
        for j in sorted(r):q=r[j];h.update(f'{i} {j} {q.numerator}/{q.denominator}\n'.encode())
    return h.hexdigest()


def left_relations(rows):
    """Independent exact relations among rows, with the newest row coefficient 1."""
    piv={}; out=[]
    for i,original in enumerate(rows):
        r=dict(original); c={i:Fraction(1)}
        while r:
            p=min(r)
            if p not in piv:
                z=r[p]; piv[p]=({j:q/z for j,q in r.items()},{j:q/z for j,q in c.items()}); break
            z=r[p]; pr,pc=piv[p]
            for j,q in pr.items():
                w=r.get(j,Fraction(0))-z*q
                if w:r[j]=w
                else:r.pop(j,None)
            for j,q in pc.items():
                w=c.get(j,Fraction(0))-z*q
                if w:c[j]=w
                else:c.pop(j,None)
        else: out.append(c)
    return out


def target_annihilator(rows, number_off, target_count):
    """Canonical RREF for the target relations after off-target values are zero."""
    if not 0 <= number_off <= len(rows):
        raise ValueError((number_off, len(rows)))
    if target_count != len(rows) - number_off:
        raise ValueError((target_count, len(rows) - number_off))
    piv={}
    for rel in left_relations(rows):
        r={i-number_off:q for i,q in rel.items() if i>=number_off and q}
        if any(not 0 <= j < target_count for j in r):
            raise AssertionError((r, target_count))
        while r:
            p=min(r)
            if p not in piv:
                z=r[p]; piv[p]={j:q/z for j,q in r.items()}; break
            z=r[p]
            for j,q in piv[p].items():
                w=r.get(j,Fraction(0))-z*q
                if w:r[j]=w
                else:r.pop(j,None)
    # Eliminate upward too, making equality checks independent of discovery order.
    for p in sorted(piv,reverse=True):
        for q in sorted(piv):
            if q==p or p not in piv[q]:continue
            z=piv[q][p]
            for j,x in piv[p].items():
                w=piv[q].get(j,Fraction(0))-z*x
                if w:piv[q][j]=w
                else:piv[q].pop(j,None)
    return tuple(tuple(sorted(r.items())) for _,r in sorted(piv.items()))


def hrelations(rel):
    h=sha256()
    for i,r in enumerate(rel):
        for j,q in r:h.update(f'{i} {j} {q.numerator}/{q.denominator}\n'.encode())
    return h.hexdigest()


def incidence(shape):
    ts=mesh(shape); ee=defaultdict(set); ff=defaultdict(set)
    for n,t in enumerate(ts):
        for i in range(4):
            ff[face(t.vertices[j] for j in range(4) if j!=i)].add(n)
            for j in range(i):ee[edge((t.vertices[i],t.vertices[j]))].add(n)
    nb=defaultdict(set)
    for x in ff.values():
        for i in x:nb[i].update(x-{i})
    return ts,ee,nb


def kind(e,star,shape):
    d=tuple(sorted(abs(e[1][i]-e[0][i]) for i in range(3))); b=sum(e[0][i]+e[1][i] in (0,2*shape[i]) for i in range(3))
    T={(1,(0,0,1),2):'one_tet_box_edge',(2,(0,0,1),2):'two_tet_box_edge',(2,(0,1,1),1):'boundary_face_diagonal',(3,(0,0,1),1):'boundary_face_axis',(4,(0,1,1),0):'interior_face_diagonal',(6,(0,0,1),0):'interior_axis',(6,(1,1,1),0):'cube_diagonal'}
    return T[len(star),d,b]


def one_ring(star,nb):
    q=set(star)
    for i in tuple(q):q.update(nb[i])
    return tuple(sorted(q))


def geometry_hash(global_tets, selected):
    payload = [
        [list(vertex) for vertex in sorted(global_tets[i].vertices)]
        for i in sorted(selected)
    ]
    return sha256(json.dumps(payload, separators=(",", ":")).encode()).hexdigest()


def coordinate_span(global_tets, selected):
    vertices = [vertex for i in selected for vertex in global_tets[i].vertices]
    return [
        max(vertex[d] for vertex in vertices) - min(vertex[d] for vertex in vertices)
        for d in range(3)
    ]


def boundary_planes(shape, global_tets, selected):
    planes=[]
    for d, name in enumerate("xyz"):
        vertices = [vertex for i in selected for vertex in global_tets[i].vertices]
        if any(vertex[d] == 0 for vertex in vertices):
            planes.append(f"{name}=0")
        if any(vertex[d] == shape[d] for vertex in vertices):
            planes.append(f"{name}={shape[d]}")
    return planes


def canonical_configuration(shape, e, star, patch, global_tets, *, coverage):
    """Canonical local state under translations and coordinate permutations.

    A source state retains the edge star and the physical planes meeting it.
    A conservative coverage state additionally retains the supported one-ring
    and every physical plane meeting that one-ring.  Reflections are
    deliberately not quotiented out, so the equivalence claim uses only
    manifest symmetries of the coordinate-order Freudenthal construction.
    """
    selected = patch if coverage else tuple(sorted(star))
    plane_selected = patch if coverage else tuple(sorted(star))
    candidates=[]
    for perm in permutations(range(3)):
        vertices = [
            tuple(vertex[perm[d]] for d in range(3))
            for i in selected
            for vertex in global_tets[i].vertices
        ]
        minima = tuple(min(vertex[d] for vertex in vertices) for d in range(3))

        def transform(vertex):
            return tuple(vertex[perm[d]] - minima[d] for d in range(3))

        state = {
            "edge": sorted([transform(vertex) for vertex in e]),
            "star": sorted(
                sorted(transform(vertex) for vertex in global_tets[i].vertices)
                for i in star
            ),
            "physical_planes": [],
        }
        if coverage:
            state["patch"] = sorted(
                sorted(transform(vertex) for vertex in global_tets[i].vertices)
                for i in patch
            )
        for old_d in range(3):
            for value in (0, shape[old_d]):
                if any(
                    vertex[old_d] == value
                    for i in plane_selected
                    for vertex in global_tets[i].vertices
                ):
                    new_d = perm.index(old_d)
                    state["physical_planes"].append(
                        [new_d, value - minima[new_d]]
                    )
        state["physical_planes"].sort()
        candidates.append(json.dumps(state, sort_keys=True, separators=(",", ":")))
    return min(candidates)


def configuration_id(prefix, canonical_state):
    return f"{prefix}-{sha256(canonical_state.encode()).hexdigest()[:16]}"


def edge_record_id(shape, e, k):
    endpoint = lambda x: ",".join(str(value) for value in x)
    return f"N{shape[0]}:e({endpoint(e[0])})-({endpoint(e[1])}):k{k}"


def certify(shape,e,star,nb,k,global_tets,source_id,coverage_id):
    edge_kind = kind(e,star,shape)
    ts,qi,R,n=assemble(k,shape,global_tets,tuple(sorted(star)),'source'); S=skeleton(ts,qi,R)
    A=[x for x in S if sum(q>0 for q in x[3])==2 and x[2]==e]
    B=[x for x in S if len(x[3])==4 and sum(q>0 for q in x[3])==1] # all broken vertices
    check_denominators([x[4] for x in B+A])
    rb, rba=rank_q([x[4] for x in B]),rank_q([x[4] for x in B+A]); source_dim=rba-rb
    patch=one_ring(star,nb); ts,qi,R,nY=assemble(k,shape,global_tets,patch,'supported'); S=skeleton(ts,qi,R)
    A2=[x for x in S if sum(q>0 for q in x[3])==2 and x[2]==e]; B2=[x for x in S if x not in A2]
    check_denominators([x[4] for x in B2+A2])
    r2,r2a=rank_q([x[4] for x in B2]),rank_q([x[4] for x in B2+A2]); lift_dim=r2a-r2
    if source_dim!=lift_dim:raise AssertionError((edge_kind,k,source_dim,lift_dim))
    RX=target_annihilator([x[4] for x in B+A],len(B),len(A))
    RY=target_annihilator([x[4] for x in B2+A2],len(B2),len(A2))
    if RX!=RY:raise AssertionError(('different source/supported target row spaces',edge_kind,k,RX,RY))
    W=minor([x[4] for x in B2+A2]);
    if W['rank']!=r2a:raise AssertionError('modular lower witness disagrees with exact rank')
    return {
        'record_id': edge_record_id(shape,e,k),
        'schema_version': SCHEMA_VERSION,
        'grid_shape': list(shape),
        'kind': edge_kind,
        'source_configuration_id': source_id,
        'coverage_configuration_id': coverage_id,
        'edge':[list(x) for x in e],
        'k':k,
        'source_star_tets':len(star),
        'source_star_coordinate_span':coordinate_span(global_tets,star),
        'source_physical_boundary_planes':boundary_planes(shape,global_tets,star),
        'source_star_geometry_sha256':geometry_hash(global_tets,star),
        'source_columns':n,
        'source_vertex_rows':len(B),
        'source_target_rows':len(A),
        'source_rank_vertex':rb,
        'source_rank_vertex_augmented':rba,
        'source_trace_dimension':source_dim,
        'source_vertex_matrix_sha256':hrows([x[4] for x in B]),
        'source_augmented_matrix_sha256':hrows([x[4] for x in B+A]),
        'supported_patch_tets':len(patch),
        'supported_patch_coordinate_span':coordinate_span(global_tets,patch),
        'supported_patch_physical_boundary_planes':boundary_planes(shape,global_tets,patch),
        'supported_patch_geometry_sha256':geometry_hash(global_tets,patch),
        'supported_columns':nY,
        'supported_off_rows':len(B2),
        'supported_target_rows':len(A2),
        'supported_rank_off':r2,
        'supported_rank_augmented':r2a,
        'lift_dimension':lift_dim,
        'supported_off_matrix_sha256':hrows([x[4] for x in B2]),
        'target_annihilator_dimension':len(RX),
        'target_annihilator_sha256':hrelations(RX),
        'target_annihilator_rref':[[[j,q.numerator,q.denominator] for j,q in r] for r in RX],
        'supported_augmented_matrix_sha256':hrows([x[4] for x in B2+A2]),
        'supported_augmented_minor':W,
    }


def classification_summary(records, configuration_data, source_states, coverage_states,
                           placement_counts, type_counts):
    by_grid = Counter(record['grid_shape'][0] for record in records)
    by_kind = Counter(record['kind'] for record in records)
    by_degree = Counter(record['k'] for record in records)
    configurations=[]
    for cid, data in sorted(configuration_data.items()):
        configurations.append({
            'coverage_configuration_id': cid,
            'source_configuration_ids': sorted(data['source_ids']),
            'kind': data['kind'],
            'representative_grid': data['representative_grid'],
            'representative_edge': data['representative_edge'],
            'placement_count_by_grid': {
                str(n): data['placement_count_by_grid'].get(n,0) for n in GRIDS
            },
        })
    return {
        'incidence_type_count': len({record['kind'] for record in records}),
        'source_configuration_count_by_grid': {
            str(n): len(source_states[n]) for n in GRIDS
        },
        'source_configuration_union_count': len(set().union(*source_states.values())),
        'coverage_configuration_count_by_grid': {
            str(n): len(coverage_states[n]) for n in GRIDS
        },
        'coverage_configuration_union_count': len(set().union(*coverage_states.values())),
        'edge_placement_count_by_grid': {
            str(n): placement_counts[n] for n in GRIDS
        },
        'degree_record_count_by_grid': {str(n): by_grid[n] for n in GRIDS},
        'degree_record_count_by_degree': {str(k): by_degree[k] for k in DEGREES},
        'degree_record_count_by_kind': dict(sorted(by_kind.items())),
        'edge_placement_count_by_grid_and_kind': {
            str(n): dict(sorted(type_counts[n].items())) for n in GRIDS
        },
        'configurations': configurations,
    }


def main():
    if sys.version_info < (3, 10):
        raise RuntimeError('Python 3.10 or newer is required')
    ap=argparse.ArgumentParser(
        description="Generate the exact Freudenthal edge-star proof certificate."
    )
    ap.add_argument(
        '--representatives',
        action='store_true',
        help='fast smoke test; the default exhausts every N=3, N=4, and N=5 edge placement',
    )
    ap.add_argument(
        '--output',
        type=Path,
        help='override the full-record JSON path',
    )
    ap.add_argument(
        '--summary-output',
        type=Path,
        help='override the compact reviewer-index JSON path',
    )
    ap.add_argument(
        '--progress-every',
        type=int,
        default=50,
        metavar='COUNT',
        help='report progress every COUNT edge placements (0 disables)',
    )
    args=ap.parse_args()
    if args.progress_every < 0:
        ap.error('--progress-every must be nonnegative')
    if not is_prime(MODULUS):
        raise RuntimeError(f'configured modular witness modulus is not prime: {MODULUS}')

    source=Path(__file__).resolve()
    mode='representatives' if args.representatives else 'exhaustive'
    default_path=(
        source.with_name(source.stem+'.representatives.json')
        if args.representatives else source.with_suffix('.json')
    )
    path=(args.output or default_path).resolve()
    default_summary=(
        source.with_name(source.stem+'.representatives.summary.json')
        if args.representatives else source.with_name(source.stem+'.summary.json')
    )
    summary_path=(args.summary_output or default_summary).resolve()
    if path == summary_path:
        raise ValueError('full certificate and summary output paths must differ')
    if source in (path,summary_path):
        raise ValueError('refusing to overwrite the certificate generator source')
    source_sha256=sha256(source.read_bytes()).hexdigest()

    started=time.perf_counter()
    records=[]
    source_states={n:set() for n in GRIDS}
    coverage_states={n:set() for n in GRIDS}
    source_ids={}
    coverage_ids={}
    configuration_data={}
    placement_counts={}
    type_counts={}
    # N=3 and N=4 are checked separately because small-grid boundary
    # truncations can interact.  A star spans at most two unit layers in each
    # coordinate, and its one-face-neighbour enlargement spans at most three.
    # Hence, for N>=5, no patch can meet both opposite physical planes in one
    # coordinate, and every compatible low-boundary/high-boundary/interior
    # clipping state occurs already for N=5.  Thus these three grids exhaust
    # all local configurations for N>=3, up to translation and coordinate
    # permutation.
    for N in GRIDS:
        shape=(N,N,N); ts,ee,nb=incidence(shape); chosen={}; identities={}
        placement_counts[N]=len(ee)
        type_counts[N]=Counter(kind(e,star,shape) for e,star in ee.items())
        if placement_counts[N] != EXPECTED_EDGE_COUNTS[N]:
            raise AssertionError((N,placement_counts[N],EXPECTED_EDGE_COUNTS[N]))
        if dict(type_counts[N]) != EXPECTED_TYPE_COUNTS[N]:
            raise AssertionError((N,dict(type_counts[N]),EXPECTED_TYPE_COUNTS[N]))
        for e,star in sorted(ee.items()):
            z=kind(e,star,shape)
            patch=one_ring(star,nb)
            source_state=canonical_configuration(
                shape,e,star,patch,ts,coverage=False
            )
            coverage_state=canonical_configuration(
                shape,e,star,patch,ts,coverage=True
            )
            source_id=configuration_id('src',source_state)
            coverage_id=configuration_id('cfg',coverage_state)
            if source_id in source_ids and source_ids[source_id] != source_state:
                raise AssertionError(f'source configuration-id collision: {source_id}')
            if coverage_id in coverage_ids and coverage_ids[coverage_id] != coverage_state:
                raise AssertionError(f'coverage configuration-id collision: {coverage_id}')
            source_ids[source_id]=source_state
            coverage_ids[coverage_id]=coverage_state
            source_states[N].add(source_state)
            coverage_states[N].add(coverage_state)
            identities[e]=(source_id,coverage_id)
            data=configuration_data.setdefault(coverage_id,{
                'source_ids':set(),
                'kind':z,
                'representative_grid':N,
                'representative_edge':[list(x) for x in e],
                'placement_count_by_grid':Counter(),
            })
            if data['kind'] != z:
                raise AssertionError((coverage_id,data['kind'],z))
            data['source_ids'].add(source_id)
            data['placement_count_by_grid'][N]+=1
            if args.representatives:
                chosen.setdefault(z,(e,star))
            else:
                chosen[f'{z}:{e}']=(e,star)
        print(
            f'N={N}: {len(ee)} placements, {len(source_states[N])} source '
            f'configurations, {len(coverage_states[N])} coverage configurations; '
            f'checking {len(chosen)} placements',
            flush=True,
        )
        for number,(_selection_key,(e,star)) in enumerate(sorted(chosen.items()),1):
            source_id,coverage_id=identities[e]
            for k in DEGREES:
                records.append(
                    certify(shape,e,star,nb,k,ts,source_id,coverage_id)
                )
            if args.progress_every and number % args.progress_every == 0:
                print(f'  N={N}: checked {number}/{len(chosen)} placements',flush=True)

    for N in GRIDS:
        if len(source_states[N]) != EXPECTED_SOURCE_CONFIGURATION_COUNTS[N]:
            raise AssertionError(('source configurations',N,len(source_states[N])))
        if len(coverage_states[N]) != EXPECTED_COVERAGE_CONFIGURATION_COUNTS[N]:
            raise AssertionError(('coverage configurations',N,len(coverage_states[N])))
    if len(set().union(*source_states.values())) != EXPECTED_SOURCE_CONFIGURATION_UNION:
        raise AssertionError('unexpected source-configuration union count')
    if len(set().union(*coverage_states.values())) != EXPECTED_COVERAGE_CONFIGURATION_UNION:
        raise AssertionError('unexpected coverage-configuration union count')

    expected_records = 42 if args.representatives else 3996
    if len(records) != expected_records:
        raise AssertionError((len(records), expected_records))
    record_ids=[record['record_id'] for record in records]
    if len(set(record_ids)) != len(record_ids):
        raise AssertionError('duplicate record_id')
    degree_counts=Counter(record['k'] for record in records)
    expected_per_degree=21 if args.representatives else sum(EXPECTED_EDGE_COUNTS.values())
    if degree_counts != Counter({k:expected_per_degree for k in DEGREES}):
        raise AssertionError((degree_counts,expected_per_degree))

    classification=classification_summary(
        records,configuration_data,source_states,coverage_states,
        placement_counts,type_counts,
    )
    if sha256(source.read_bytes()).hexdigest() != source_sha256:
        raise RuntimeError('certificate generator source changed during execution')
    out={
        'schema_version':SCHEMA_VERSION,
        'provenance':{
            'generated_by':source.name,
            'generator_sha256':source_sha256,
            'mode':mode,
            'deterministic_payload':True,
            'minimum_python':'3.10',
        },
        'mathematical_input':{
            'grids':[list((n,n,n)) for n in GRIDS],
            'degrees':list(DEGREES),
            'source_object':'X_e on the tetrahedral edge star; only true box-boundary velocity nodes removed',
            'supported_object':'Y_e on the one-face-neighbour patch; all exterior velocity nodes removed',
            'certified_statement':'tau_e(ker sigma_e intersect Y_e) equals tau_e(ker gamma_e intersect X_e)',
        },
        'arithmetic':{
            'field':'fractions.Fraction over Q',
            'upper_and_exact_rank':'exact sparse Gaussian elimination',
            'lower_rank_witness':'selected full-rank minor modulo a prime',
            'modulus':MODULUS,
            'modulus_verified_prime_by_trial_division':True,
            'all_rational_denominators_checked_invertible_modulo_prime':True,
        },
        'classification_definitions':{
            'incidence_type':'one of seven coarse classes determined by edge increment, boundary incidence, and incident-tetrahedron count',
            'source_configuration':'edge, star tetrahedra, and physical planes meeting the star, modulo integer translation and coordinate permutation',
            'coverage_configuration':'source geometry plus the supported one-ring and every physical plane meeting it, modulo integer translation and coordinate permutation; reflections are not quotiented',
            'degree_record':'one concrete (grid, geometric edge placement, polynomial degree) exact matrix computation',
        },
        'classification':classification,
        'records':records,
    }
    record_index=[{
        key:record[key] for key in (
            'record_id','grid_shape','edge','k','kind',
            'source_configuration_id','coverage_configuration_id',
        )
    } for record in records]
    summary={
        key:value for key,value in out.items() if key != 'records'
    }
    summary['record_index']=record_index
    path.parent.mkdir(parents=True,exist_ok=True)
    summary_path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n')
    summary_path.write_text(json.dumps(summary,indent=2)+'\n')
    elapsed=time.perf_counter()-started
    print(
        f'edge-star certificate passed: {len(records)} exact records in '
        f'{elapsed:.1f}s using Python {sys.version.split()[0]}; wrote '
        f'{path.name} and {summary_path.name}'
    )


if __name__=='__main__':main()
