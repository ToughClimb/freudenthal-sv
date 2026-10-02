import FreudenthalSVLean.OrderedEdgeGeometry

/-!
# Geometry-derived canonical face-pattern identities

The spanning-pattern table and equations `two-tet-borrow-zero` and
`two-tet-borrow-one` in manuscript Lemma `edge-star` are encoded by their
three actual relative face nodes and integer vector coefficients.  The
incidence coefficients are regenerated from these faces and the proved
coordinate-chain barycentric gradients.  Every admissible tetrahedron
in the full first-endpoint star and every local edge is checked, including
the borrowed face's second owner outside the target edge star.

The finite identities use kernel reduction over integers.  They are not
rank assertions: the expected vectors are separately encoded, and the
identities show that the geometric face formulas produce them and have
zero coefficients on every other edge.  Actual spatial-polynomial
realization and spanning follow in separate modules.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry

noncomputable section

namespace FreudenthalSVLean.CanonicalFacePatterns

abbrev IntPoint := Coordinate → ℤ

structure FaceTerm where
  nodes : Finset IntPoint
  vector : IntPoint
  deriving DecidableEq

def patternCount (c : Fin 7) : ℕ := ![0, 2, 1, 3, 3, 6, 6] c

theorem patternCount_le_six : ∀ c : Fin 7, patternCount c ≤ 6 := by decide +kernel

def primaryThird (c : Fin 7) (side : Bool) (p : Fin 6) : IntPoint :=
  if side then
    ![fun _ => 0, fun _ => ![1, 1, 1], fun _ => ![1, 1, 1],
      ![![1, 1, 0], ![1, 1, 1], ![1, 1, 1], 0, 0, 0],
      ![![0, 0, -1], ![0, 1, 0], ![1, 0, 0], 0, 0, 0],
      ![![0, 0, 1], ![0, 0, 1], ![0, 1, 0], ![0, 1, 0], ![1, 0, 0], ![1, 0, 0]],
      ![![0, -1, 0], ![0, -1, 0], ![0, 0, -1], ![0, 0, -1], ![1, 1, 1], ![1, 1, 1]]] c p
  else
    ![fun _ => 0, fun _ => ![1, 1, 1], fun _ => ![1, 1, 1],
      ![![1, 1, 0], ![1, 1, 0], ![1, 1, 1], 0, 0, 0],
      ![![0, 0, -1], ![0, 1, 0], ![1, 0, 0], 0, 0, 0],
      ![![0, 1, 1], ![0, 1, 1], ![1, 0, 1], ![1, 0, 1], ![1, 1, 0], ![1, 1, 0]],
      ![![0, -1, -1], ![0, -1, -1], ![1, 0, 1], ![1, 0, 1], ![1, 1, 0], ![1, 1, 0]]] c p

def primaryVector (c : Fin 7) (side : Bool) (p : Fin 6) : IntPoint :=
  if side then
    ![fun _ => 0,
      ![![1, 0, 0], ![0, 1, 0], 0, 0, 0, 0], fun _ => ![1, 0, 0],
      ![![1, 0, 0], ![1, 0, 0], ![0, 0, 1], 0, 0, 0],
      ![![1, 1, 1], ![1, 0, 0], ![0, 1, 0], 0, 0, 0],
      ![![1, 0, 0], ![0, 1, 0], ![1, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 0, 1]],
      ![![0, 0, 1], ![1, 1, 0], ![0, 1, 0], ![1, 0, 1], ![0, 1, 0], ![0, 0, 1]]] c p
  else
    ![fun _ => 0,
      ![![0, 1, 0], ![1, 0, 1], 0, 0, 0, 0], fun _ => ![1, 1, 1],
      ![![1, 1, 0], ![0, 0, 1], ![1, 1, 1], 0, 0, 0],
      ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0], 0, 0, 0],
      ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0]],
      ![![0, 1, 0], ![0, 0, 1], ![0, 1, 0], ![1, 0, 1], ![0, 0, 1], ![1, 1, 0]]] c p

def patternTerm (c : Fin 7) (side : Bool) (p : Fin 6) (r : Fin 2) : FaceTerm :=
  if r = 0 then
    ⟨{0, positiveDirection (canonicalDirectionIndex c), primaryThird c side p},
      primaryVector c side p⟩
  else if c = 1 ∧ side = false then
    ⟨{0, ![0, 1, 1], ![1, 1, 1]}, if p = 0 then ![0, 1, 0] else ![0, -1, 0]⟩
  else ⟨{0, positiveDirection (canonicalDirectionIndex c), primaryThird c side p}, 0⟩

def modeEndpoint (c : Fin 7) (side : Bool) : IntPoint :=
  if side then positiveDirection (canonicalDirectionIndex c) else 0

def expectedPattern (c : Fin 7) (side : Bool) (p i : Fin 6) : ℤ :=
  if side then
    ![fun _ => 0,
      ![![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], 0, 0, 0, 0],
      fun _ => ![1, 1, 0, 0, 0, 0],
      ![![1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], 0, 0, 0],
      ![![-1, -1, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0], ![-1, 0, -1, 0, 0, 0], 0, 0, 0],
      ![![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, -1, 0, 0, 0],
        ![0, 0, 0, -1, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0]],
      ![![0, 1, 0, 0, 0, 0], ![0, -1, -1, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
        ![-1, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]] c p i
  else
    ![fun _ => 0,
      ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], 0, 0, 0, 0],
      fun _ => ![1, 1, 0, 0, 0, 0],
      ![![1, 1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0], 0, 0, 0],
      ![![-1, -1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], 0, 0, 0],
      ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
        ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]],
      ![![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1],
        ![0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 1, 0]]] c p i

def termOwners (F : FaceTerm) : Finset CatalogState :=
  Finset.univ.filter (fun s => F.nodes ⊆ catalogVertices s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Every nonzero term is an interior three-node face with exactly two
admissible owners, including the borrowed term. -/
theorem canonical_term_geometry : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (r : Fin 2),
    let F := patternTerm c side (p.castLE (patternCount_le_six c)) r
    F.vector ≠ 0 → F.nodes.card = 3 ∧ 0 ∈ F.nodes ∧ modeEndpoint c side ∈ F.nodes ∧
      (termOwners F).card = 2 ∧
      ∀ s ∈ termOwners F, catalogAdmissible (canonicalEdgeTags c) s ∧
        ∃ u : Vertex, u ≠ s.2 ∧ F.nodes = catalogFace s u := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The same two face owners are admissible for every actual boundary
word with the prescribed containing planes.  Changing endpoint tags do
not exclude either owner, including on the mesh `N=1`. -/
theorem canonical_term_admissible_reduced : ∀ (c : Fin 7) (side : Bool)
    (p : Fin (patternCount c)) (r : Fin 2) (b : Coordinate → Fin 3),
    validPositiveTags b (canonicalDirectionIndex c) →
    reducedEdgeTags b (canonicalDirectionIndex c) =
      reducedEdgeTags (canonicalEdgeTags c) (canonicalDirectionIndex c) →
    let F := patternTerm c side (p.castLE (patternCount_le_six c)) r
    F.vector ≠ 0 → ∀ s ∈ termOwners F, catalogAdmissible b s := by
  decide +kernel

def termEdgeCoefficient (F : FaceTerm) (endpoint : IntPoint)
    (s : CatalogState) (l m : Vertex) : ℤ :=
  if F.nodes ⊆ catalogVertices s ∧ endpoint ∈ ({catalogRelative s l, catalogRelative s m} : Finset IntPoint) ∧
      catalogRelative s l ∈ F.nodes ∧ catalogRelative s m ∈ F.nodes then
    ∑ a : Vertex,
      if catalogRelative s a ∈ F.nodes ∧ catalogRelative s a ≠ catalogRelative s l ∧
          catalogRelative s a ≠ catalogRelative s m then
        ∑ j : Coordinate, F.vector j * catalogGradient s a j
      else 0
  else 0

def patternEdgeCoefficient (c : Fin 7) (side : Bool) (p : Fin 6)
    (s : CatalogState) (l m : Vertex) : ℤ :=
  ∑ r : Fin 2, termEdgeCoefficient (patternTerm c side p r) (modeEndpoint c side) s l m

def expectedStatePattern (c : Fin 7) (side : Bool) (p : Fin 6) (s : CatalogState) : ℤ :=
  ∑ i : Fin (incidenceValence c),
    if (orderedIncidence c i).1 = s then
      expectedPattern c side p (i.castLE (incidenceValence_le_six c)) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Geometry-derived coefficients produce the displayed target patterns
and vanish on every other local edge of every admissible owner. -/
theorem canonical_pattern_coefficients : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (s : CatalogState), catalogAdmissible (canonicalEdgeTags c) s → ∀ (l m : Vertex), l ≠ m →
    patternEdgeCoefficient c side (p.castLE (patternCount_le_six c)) s l m =
      if ({catalogRelative s l, catalogRelative s m} : Finset IntPoint) =
          {0, positiveDirection (canonicalDirectionIndex c)} then
        expectedStatePattern c side (p.castLE (patternCount_le_six c)) s
      else 0 := by
  decide +kernel

end FreudenthalSVLean.CanonicalFacePatterns
