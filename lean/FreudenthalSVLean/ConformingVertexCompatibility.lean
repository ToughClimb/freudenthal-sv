import FreudenthalSVLean.MeanPreservingVertexLift
import FreudenthalSVLean.ConformingEdgeJets

/-!
# Complete compatibility for actual finite-element vertex data

For manuscript Lemma `vertex-jets`, a common geometric edge has one
issuing jet and a boundary edge has zero jet.  These statements are
applied to the exact arbitrary-mesh catalog, with representatives chosen
from geometry before the velocity field.  Derivative reconstruction then
identifies the actual divergence-vertex image with the explicitly defined
compatibility image.  The converse uses the actual conforming cubic nodal
fields, not a dimension or rank assertion.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.RawVertexTrace
open FreudenthalSVLean.EdgeJetContinuity
open FreudenthalSVLean.ConformingEdgeJets
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.ConformingVertexCompatibility

theorem edgeRepresentative_exists {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) :
    ∃ r : Tet N × Vertex × Vertex,
      gridVertexOfTet r.1 r.2.1 = n ∧ r.2.2 ≠ r.2.1 ∧
        integerGrid (gridVertexOfTet r.1 r.2.2) = endpoint n d := by
  obtain ⟨t, a, l, ha, hl, he⟩ := endpoint_realizes hN n d
  exact ⟨(t, a, l), ha, hl, he⟩

def edgeRepresentative {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) : Tet N × Vertex × Vertex :=
  Classical.choose (edgeRepresentative_exists hN n d)

theorem edgeRepresentative_spec {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) :
    gridVertexOfTet (edgeRepresentative hN n d).1 (edgeRepresentative hN n d).2.1 = n ∧
      (edgeRepresentative hN n d).2.2 ≠ (edgeRepresentative hN n d).2.1 ∧
        integerGrid (gridVertexOfTet (edgeRepresentative hN n d).1
          (edgeRepresentative hN n d).2.2) = endpoint n d :=
  Classical.choose_spec (edgeRepresentative_exists hN n d)

def extractJets {N k : ℕ} (hN : 0 < N) (n : GridVertex N) :
    velocitySpace N k →ₗ[ℝ] JetSpace (boundaryTag n) where
  toFun v d j := directionalJet
    (vertex (edgeRepresentative hN n d).1 (edgeRepresentative hN n d).2.1)
    (vertex (edgeRepresentative hN n d).1 (edgeRepresentative hN n d).2.2)
    (v.val (edgeRepresentative hN n d).1 j)
  map_add' v w := by
    funext d j
    simp [directionalJet, Submodule.coe_add, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' c v := by
    funext d j
    simp [directionalJet, Pi.smul_apply, smul_eq_C_mul,
      map_mul, eval_C, Finset.mul_sum, mul_assoc]

theorem extractJets_common {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (v : velocitySpace N k) (ta : VertexStar n) (a : Vertex)
    (ha : catalogRelative (starCatalog ta) a ∈ catalogActiveEdges (boundaryTag n))
    (j : Coordinate) :
    directionalJet (vertex ta.val.1 ta.val.2) (vertex ta.val.1 a) (v.val ta.val.1 j) =
      extractJets hN n v ⟨catalogRelative (starCatalog ta) a, ha⟩ j := by
  let d : ActiveEdge (boundaryTag n) := ⟨catalogRelative (starCatalog ta) a, ha⟩
  let r := edgeRepresentative hN n d
  have hr := edgeRepresentative_spec hN n d
  have hn : vertex ta.val.1 ta.val.2 = vertex r.1 r.2.1 := by
    rw [← gridVertexOfTet_point, ← gridVertexOfTet_point, ta.property, hr.1]
  have he : integerGrid (gridVertexOfTet ta.val.1 a) =
      integerGrid (gridVertexOfTet r.1 r.2.2) := by
    rw [hr.2.2, integer_vertex_displacement]
    rfl
  have hm : vertex ta.val.1 a = vertex r.1 r.2.2 := by
    rw [← gridVertexOfTet_point, ← gridVertexOfTet_point, integerGrid_injective he]
  exact common_edge_jet hN v ta.val.1 r.1 ta.val.2 a r.2.1 r.2.2 hn hm j

theorem gridPoint_lower {N : ℕ} (n : GridVertex N) (j : Coordinate)
    (hn : (n j).val = 0) : gridPoint n j = 0 := by
  simp [gridPoint, hn]

theorem gridPoint_upper {N : ℕ} (hN : 0 < N) (n : GridVertex N) (j : Coordinate)
    (hn : (n j).val = N) : gridPoint n j = 1 := by
  simp only [gridPoint, Pi.smul_apply, smul_eq_mul, hn, meshScale]
  exact inv_mul_cancel₀ (Nat.cast_pos.mpr hN).ne'

/-- Every omitted local edge is either the zero issuing direction or an
edge lying in an actual physical boundary plane. -/
theorem inactive_edge_jet_zero {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (v : velocitySpace N k) (ta : VertexStar n) (a : Vertex)
    (ha : catalogRelative (starCatalog ta) a ∉ catalogActiveEdges (boundaryTag n))
    (j : Coordinate) :
    directionalJet (vertex ta.val.1 ta.val.2) (vertex ta.val.1 a) (v.val ta.val.1 j) = 0 := by
  classical
  by_cases hself : a = ta.val.2
  · subst a
    simp [directionalJet]
  · have he : catalogRelative (starCatalog ta) a ∈ catalogEdges (boundaryTag n) := by
      apply Finset.mem_image.mpr
      refine ⟨(starCatalog ta, a), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, starCatalog_admissible hN ta, ?_⟩, rfl⟩
      simpa only [starCatalog_cut] using hself
    have hactive : ¬activeDirection (boundaryTag n) (catalogRelative (starCatalog ta) a) := by
      intro h
      exact ha (Finset.mem_filter.mpr ⟨he, h⟩)
    unfold activeDirection at hactive
    push Not at hactive
    obtain ⟨i, hi, hd⟩ := hactive
    have hm : (gridVertexOfTet ta.val.1 a i).val = (n i).val := by
      have hc := catalog_displacement ta a i
      rw [hd] at hc
      omega
    have hbound : (n i).val = 0 ∨ (n i).val = N := by
      by_cases hz : (n i).val = 0
      · exact Or.inl hz
      · right
        by_contra hu
        exact hi (by simp [boundaryTag, hz, hu])
    rcases hbound with hz | hu
    · apply boundary_edge_jet_zero hN v ta.val.1 ta.val.2 a j i 0 (Or.inl rfl)
      · rw [← gridVertexOfTet_point, ta.property]
        exact gridPoint_lower n i hz
      · rw [← gridVertexOfTet_point]
        exact gridPoint_lower _ i (hm.trans hz)
    · apply boundary_edge_jet_zero hN v ta.val.1 ta.val.2 a j i 1 (Or.inr rfl)
      · rw [← gridVertexOfTet_point, ta.property]
        exact gridPoint_upper hN n i hu
      · rw [← gridVertexOfTet_point]
        exact gridPoint_upper hN _ i (hm.trans hu)

def vertexTrace {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    BrokenPressure N →ₗ[ℝ] VertexData (boundaryTag n) where
  toFun q s := eval
    (vertex ((catalogIncidenceEquiv hN n).symm s).val.1 ((catalogIncidenceEquiv hN n).symm s).val.2)
    (q ((catalogIncidenceEquiv hN n).symm s).val.1)
  map_add' q r := by
    funext s
    simp only [Pi.add_apply, map_add]
  map_smul' c q := by
    funext s
    simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, RingHom.id_apply, smul_eq_mul]

theorem vertexTrace_incidence {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (q : BrokenPressure N) (ta : VertexStar n) :
    vertexTrace hN n q (catalogIncidenceEquiv hN n ta) =
      eval (vertex ta.val.1 ta.val.2) (q ta.val.1) := by
  simp only [vertexTrace, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]

theorem compatibility_extractJets_incidence {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (v : velocitySpace N k) (ta : VertexStar n) :
    compatibility (boundaryTag n) (extractJets hN n v) (catalogIncidenceEquiv hN n ta) =
      meshScale N * eval (vertex ta.val.1 ta.val.2) (divergence N v.val ta.val.1) := by
  classical
  rw [divergence_vertex_from_edge_jets hN, Finset.mul_sum]
  dsimp only [compatibility, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [catalogIncidenceEquiv_val, starCatalog_perm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  by_cases ha : catalogRelative (starCatalog ta) a ∈ catalogActiveEdges (boundaryTag n)
  · rw [dif_pos ha]
    apply Finset.sum_congr rfl
    intro j _
    rw [← extractJets_common hN n v ta a ha j]
    change _ = meshScale N * (directionalJet _ _ _ *
      eval _ (pderiv j (scaledBarycentric ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) a)))
    rw [pderiv_scaledBarycentric, eval_C]
    field_simp [(meshScale_pos N hN).ne']
  · rw [dif_neg ha]
    simp only [inactive_edge_jet_zero hN n v ta a ha, zero_mul, mul_zero, Finset.sum_const_zero]

theorem compatibility_extractJets {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (v : velocitySpace N k) :
    compatibility (boundaryTag n) (extractJets hN n v) =
      (meshScale N) • vertexTrace hN n (divergence N v.val) := by
  funext s
  obtain ⟨ta, rfl⟩ := (catalogIncidenceEquiv hN n).surjective s
  simp only [Pi.smul_apply, smul_eq_mul, vertexTrace_incidence]
  exact compatibility_extractJets_incidence hN n v ta

theorem pressure_vertexTrace_mem_compatibility {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (q : pressureSpace N k) : vertexTrace hN n q.val ∈ (compatibility (boundaryTag n)).range := by
  obtain ⟨v, hv, he⟩ := q.property
  refine ⟨(meshScale N)⁻¹ • extractJets hN n (⟨v, hv⟩ : velocitySpace N k), ?_⟩
  rw [map_smul, compatibility_extractJets, he, smul_smul,
    inv_mul_cancel₀ (meshScale_pos N hN).ne', one_smul]

theorem velocitySpace_degree_mono {N k l : ℕ} (hkl : k ≤ l)
    (v : velocitySpace N k) : v.val ∈ velocitySpace N l :=
  ⟨fun t j => (v.property.1 t j).trans hkl, v.property.2⟩

/-- Equality of the entire actual vertex-divergence image and the
compatibility image, for every positive mesh size and every vertex.
The reverse inclusion is realized by actual conforming cubic fields. -/
theorem actual_trace_iff {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k) (n : GridVertex N)
    (data : VertexData (boundaryTag n)) :
    data ∈ (compatibility (boundaryTag n)).range ↔
      ∃ v : velocitySpace N k, vertexTrace hN n (divergence N v.val) = data := by
  constructor
  · rintro ⟨x, hx⟩
    let v3 : velocitySpace N 3 := rawConforming hN n ((meshScale N) • x)
    let v : velocitySpace N k := ⟨v3.val, velocitySpace_degree_mono hk v3⟩
    refine ⟨v, ?_⟩
    funext s
    obtain ⟨ta, rfl⟩ := (catalogIncidenceEquiv hN n).surjective s
    rw [vertexTrace_incidence]
    change eval _ (divergence N (rawField n ((meshScale N) • x)) ta.val.1) = _
    rw [rawField_vertex_divergence, map_smul, hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (meshScale_pos N hN).ne', one_mul]
  · rintro ⟨v, rfl⟩
    refine ⟨(meshScale N)⁻¹ • extractJets hN n v, ?_⟩
    rw [map_smul, compatibility_extractJets, smul_smul,
      inv_mul_cancel₀ (meshScale_pos N hN).ne', one_smul]

def pressureCompatibilityData {N k : ℕ} (hN : 0 < N) (n : GridVertex N) :
    pressureSpace N k →ₗ[ℝ] (compatibility (boundaryTag n)).range :=
  ((vertexTrace hN n).comp (pressureSpace N k).subtype).codRestrict _
    (pressure_vertexTrace_mem_compatibility hN n)

end FreudenthalSVLean.ConformingVertexCompatibility
