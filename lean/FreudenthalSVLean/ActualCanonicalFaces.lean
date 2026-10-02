import FreudenthalSVLean.ActualOrderedEdgeGeometry
import FreudenthalSVLean.CanonicalFacePatterns
import FreudenthalSVLean.ActualFaceEdgeTraces

/-!
# Physical realization of canonical and borrowed faces

For manuscript Lemma `edge-star`, each nonzero canonical face term is
realized by a fixed pair of actual tetrahedra on every admissible mesh.
The reduced boundary-word theorem guarantees both owners even when an
increasing endpoint lies on another physical plane (`N=1` included).
Their global nodal face product is conforming, homogeneous on the box
boundary, supported on these two owners, and has zero derivatives at all
mesh vertices.  The sum of the terms gives each actual endpoint pattern.

The edge traces and uniform energy estimate of the resulting patterns
are distinct obligations; this module proves their actual finite-element
membership and support without assuming those obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.RawVertexField

noncomputable section

namespace FreudenthalSVLean.ActualCanonicalFaces

structure CatalogFacePair (F : FaceTerm) where
  first : CatalogState
  second : CatalogState
  firstOmitted : Vertex
  secondOmitted : Vertex
  distinct : first ≠ second
  firstOwner : first ∈ termOwners F
  secondOwner : second ∈ termOwners F
  firstThrough : firstOmitted ≠ first.2
  secondThrough : secondOmitted ≠ second.2
  firstFace : F.nodes = catalogFace first firstOmitted
  secondFace : F.nodes = catalogFace second secondOmitted

abbrev ActiveTerm (c : Fin 7) (side : Bool) (p : Fin (patternCount c)) :=
  {r : Fin 2 // (patternTerm c side (p.castLE (patternCount_le_six c)) r).vector ≠ 0}

theorem term_pair_exists (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) :
    Nonempty (CatalogFacePair (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)) := by
  let F := patternTerm c side (p.castLE (patternCount_le_six c)) r.val
  have hg := canonical_term_geometry c side p r.val r.property
  obtain ⟨s, t, hst, he⟩ := Finset.card_eq_two.mp hg.2.2.2.1
  have hs : s ∈ termOwners F := by rw [he]; simp
  have ht : t ∈ termOwners F := by rw [he]; simp
  obtain ⟨u, hu, hfu⟩ := (hg.2.2.2.2 s hs).2
  obtain ⟨v, hv, hfv⟩ := (hg.2.2.2.2 t ht).2
  exact ⟨⟨s, t, u, v, hst, hs, ht, hu, hv, hfu, hfv⟩⟩

def termPair (c : Fin 7) (side : Bool) (p : Fin (patternCount c)) (r : ActiveTerm c side p) :
    CatalogFacePair (patternTerm c side (p.castLE (patternCount_le_six c)) r.val) :=
  Classical.choice (term_pair_exists c side p r)

def actualOwner {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (s : CatalogState)
    (hs : s ∈ termOwners (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)) :
    VertexStar a :=
  (catalogIncidenceEquiv hN a).symm ⟨s,
    canonical_term_admissible_reduced c side p r.val (boundaryTag a)
      (actual_positive_tags hN a b _ hd) hl r.property s hs⟩

theorem actualOwner_catalog {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (s : CatalogState)
    (hs : s ∈ termOwners (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)) :
    starCatalog (actualOwner hN a b c hd hl side p r s hs) = s := by
  rw [← catalogIncidenceEquiv_val hN a]
  exact congrArg Subtype.val ((catalogIncidenceEquiv hN a).apply_symm_apply _)

def firstOwner {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) : VertexStar a :=
  actualOwner hN a b c hd hl side p r (termPair c side p r).first (termPair c side p r).firstOwner

def secondOwner {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) : VertexStar a :=
  actualOwner hN a b c hd hl side p r (termPair c side p r).second (termPair c side p r).secondOwner

theorem actual_pair_geometry {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) :
    let ta := firstOwner hN a b c hd hl side p r
    let tb := secondOwner hN a b c hd hl side p r
    let w := termPair c side p r
    w.firstOmitted ≠ ta.val.2 ∧ w.secondOmitted ≠ tb.val.2 ∧ ta.val.1 ≠ tb.val.1 ∧
      gridFace ta.val.1 w.firstOmitted = gridFace tb.val.1 w.secondOmitted := by
  have hta : starCatalog (firstOwner hN a b c hd hl side p r) = (termPair c side p r).first :=
    actualOwner_catalog hN a b c hd hl side p r _ _
  have htb : starCatalog (secondOwner hN a b c hd hl side p r) = (termPair c side p r).second :=
    actualOwner_catalog hN a b c hd hl side p r _ _
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← starCatalog_cut, hta] using (termPair c side p r).firstThrough
  · simpa only [← starCatalog_cut, htb] using (termPair c side p r).secondThrough
  · intro he
    have ht := starTet_injective a he
    have hc := congrArg starCatalog ht
    rw [hta, htb] at hc
    exact (termPair c side p r).distinct hc
  · apply Finset.image_injective (displacement_injective a)
    rw [displaced_catalogFace, displaced_catalogFace, hta, htb,
      ← (termPair c side p r).firstFace, ← (termPair c side p r).secondFace]

def physicalEndpoint {N : ℕ} (a b : GridVertex N) (side : Bool) : GridVertex N :=
  if side then b else a

def termField {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) : BrokenVelocity N :=
  weightedFaceField N (firstOwner hN a b c hd hl side p r).val.1
    (termPair c side p r).firstOmitted (physicalEndpoint a b side) (physicalEndpoint a b side) e 0
    (fun j => meshScale N *
      ((patternTerm c side (p.castLE (patternCount_le_six c)) r.val).vector j : ℝ))

theorem termField_mem {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) (hk : 3 + e ≤ k) :
    termField hN a b c hd hl side p r e ∈ velocitySpace N k := by
  have hg := actual_pair_geometry hN a b c hd hl side p r
  exact weightedFaceField_mem_velocitySpace hN _ _
    (shared_face_active hN _ _ _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2)
    _ _ e 0 (by simpa only [add_zero] using hk) _

theorem termField_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i (termField hN a b c hd hl side p r e t j)) = 0 := by
  have hg := actual_pair_geometry hN a b c hd hl side p r
  exact weightedFaceField_protects_vertices hN _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2
    _ _ _ _ _ t l i j

theorem termField_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) : termField hN a b c hd hl side p r e t = 0 := by
  have hg := actual_pair_geometry hN a b c hd hl side p r
  have hfirst : t ≠ (firstOwner hN a b c hd hl side p r).val.1 := by
    intro he
    exact ht (firstOwner hN a b c hd hl side p r).val.2
      (he ▸ (firstOwner hN a b c hd hl side p r).property)
  have hsecond : t ≠ (secondOwner hN a b c hd hl side p r).val.1 := by
    intro he
    exact ht (secondOwner hN a b c hd hl side p r).val.2
      (he ▸ (secondOwner hN a b c hd hl side p r).property)
  funext j
  exact weightedFaceField_zero_off_pair _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2
    _ _ _ _ _ t hfirst hsecond j

def patternField {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) : BrokenVelocity N :=
  ∑ r : ActiveTerm c side p, termField hN a b c hd hl side p r e

theorem patternField_mem {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (hk : 3 + e ≤ k) :
    patternField hN a b c hd hl side p e ∈ velocitySpace N k :=
  Submodule.sum_mem _ (fun r _ => termField_mem hN a b c hd hl side p r e hk)

theorem patternField_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i (patternField hN a b c hd hl side p e t j)) = 0 := by
  simp only [patternField, Finset.sum_apply, map_sum,
    termField_vertex_derivative hN a b c hd hl side p, Finset.sum_const_zero]

theorem patternField_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (t : Tet N) (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    patternField hN a b c hd hl side p e t = 0 := by
  simp only [patternField, Finset.sum_apply, termField_off_star hN a b c hd hl side p _ e t ht,
    Finset.sum_const_zero]

end FreudenthalSVLean.ActualCanonicalFaces
