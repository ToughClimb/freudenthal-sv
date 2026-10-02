import FreudenthalSVLean.RawVertexField

/-!
# Actual vertex traces of the global cubic correction

For manuscript equations `vertex-div-map` and `vertex-raw-properties`, the
global cubic nodal field has exactly `h⁻¹ A_b s` as its divergence data
at the marked vertex, under the proved arbitrary-mesh catalog equivalence.
All other mesh vertex incidences have zero derivative.  The calculation
uses polynomial differentiation and the exact local endpoint expansion;
it does not postulate a compatibility matrix for the physical field.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ConformingSkeletonBubble
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.RawVertexField

noncomputable section

namespace FreudenthalSVLean.RawVertexTrace

theorem scaledBubble_vertex_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (a b l : Vertex) (hab : a ≠ b) (c : ℝ) (i : Coordinate) :
    eval (vertex t l) (pderiv i (rescale (meshScale N) c
      (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b))) =
        c * (meshScale N)⁻¹ * if l = a then barycentricGradient t.2 b i else 0 := by
  rw [pderiv_rescale, rescale_eval]
  have he : (meshScale N)⁻¹ • vertex t l = chainVertex t.2 (cellOrigin t.1) l := by
    simp only [vertex, scaledVertex, smul_smul, inv_mul_cancel₀ (meshScale_pos N hN).ne',
      one_smul]
  rw [he, SkeletonBubble.pderiv_vertexBubble_vertex _ _ _ _ _ _ hab]

theorem cubicEdge_derivative_expansion {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta : VertexStar n) (d : ActiveEdge (boundaryTag n)) (s : Space)
    (l : Vertex) (i j : Coordinate) :
    eval (vertex ta.val.1 l)
      (pderiv i (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1 j)) =
        ∑ a : Vertex, if catalogRelative (starCatalog ta) a = d.val then
          s j * (meshScale N)⁻¹ *
            (if l = ta.val.2 then barycentricGradient ta.val.1.2 a i else 0)
        else 0 := by
  rw [local_cubic_expansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : catalogRelative (starCatalog ta) a = d.val
  · have hab : ta.val.2 ≠ a := by
      simpa only [starCatalog_cut] using
        (active_other (boundaryTag n) (starCatalog ta) a (he.symm ▸ d.property)).symm
    simp only [if_pos he]
    exact scaledBubble_vertex_derivative hN ta.val.1 ta.val.2 a l hab (s j) i
  · simp [he]

theorem rawField_vertex_derivative {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (ta : VertexStar n) (l : Vertex) (i j : Coordinate) :
    eval (vertex ta.val.1 l) (pderiv i (rawField n x ta.val.1 j)) =
      (meshScale N)⁻¹ * if l = ta.val.2 then
        ∑ a : Vertex, if ha : catalogRelative (starCatalog ta) a ∈ catalogActiveEdges (boundaryTag n) then
          x ⟨catalogRelative (starCatalog ta) a, ha⟩ j * barycentricGradient ta.val.1.2 a i
        else 0
      else 0 := by
  classical
  rw [rawField_apply, map_sum, map_sum]
  simp only [cubicEdge_derivative_expansion hN]
  by_cases hl : l = ta.val.2
  · simp only [if_pos hl]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [sum_active_eq]
    split_ifs <;> ring
  · simp [hl]

theorem rawField_vertex_divergence {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (ta : VertexStar n) :
    eval (vertex ta.val.1 ta.val.2) (divergence N (rawField n x) ta.val.1) =
      (meshScale N)⁻¹ * compatibility (boundaryTag n) x (catalogIncidenceEquiv hN n ta) := by
  classical
  change eval _ (∑ j : Coordinate, pderiv j (rawField n x ta.val.1 j)) = _
  rw [map_sum]
  simp only [rawField_vertex_derivative hN, ite_true, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  dsimp only [compatibility, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [catalogIncidenceEquiv_val, starCatalog_perm]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · simp only [mul_comm]
  · simp

/-- Every other incidence is protected, whether its tetrahedron belongs
to the star or lies outside its support. -/
theorem rawField_protects_other_vertices {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (t : Tet N) (l : Vertex)
    (hl : gridVertexOfTet t l ≠ n) (i j : Coordinate) :
    eval (vertex t l) (pderiv i (rawField n x t j)) = 0 := by
  classical
  by_cases ht : ∃ a : Vertex, gridVertexOfTet t a = n
  · obtain ⟨a, ha⟩ := ht
    let ta : VertexStar n := ⟨(t, a), ha⟩
    have hla : l ≠ a := by
      intro h
      exact hl (h ▸ ha)
    exact (rawField_vertex_derivative hN n x ta l i j).trans (by simp [ta, hla])
  · push Not at ht
    rw [rawField_zero_off_star n x t ht j, map_zero, map_zero]

end FreudenthalSVLean.RawVertexTrace
