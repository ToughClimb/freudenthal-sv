import FreudenthalSVLean.ActualOrderedEdgeGeometry
import FreudenthalSVLean.CanonicalPatternSpan
import FreudenthalSVLean.CanonicalSourceGeometry
import FreudenthalSVLean.BoundaryEdgeCompatibility
import FreudenthalSVLean.CheckerboardCompatibility
import FreudenthalSVLean.ConformingVertexCompatibility

/-!
# Actual canonical edge pressure compatibility from conformity

The source-relation part of manuscript Lemma `edge-star` is derived for
the actual arbitrary-`N` finite-element spaces in canonical coordinates.
The explicit geometric face witnesses discharge every hypothesis of the
analytic boundary-conormal and face-jump theorems.  Thus the zero,
equal-pair, and checkerboard relations hold pointwise on the entire closed
physical edge, with all other rows unrestricted.

Only the reduced containing-boundary tags are prescribed, so increasing
endpoints may themselves lie on additional box planes.  Transport under
general coordinate permutations and central inversion is separate.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ConformingVertexCompatibility
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.CanonicalSourceGeometry
open FreudenthalSVLean.BoundaryEdgeCompatibility
open FreudenthalSVLean.CheckerboardCompatibility

noncomputable section

namespace FreudenthalSVLean.ActualCanonicalSource

def orderedPressureTrace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : BrokenPressure N) (s : ℝ) : Fin (incidenceValence c) → ℝ :=
  fun i => eval (segmentPoint (gridPoint a) (gridPoint b) s)
    (q (orderedActualStar hN a b c hd hl i).val.1)

theorem one_sector_zero {N k : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex 0))
    (hl : CanonicalLocation a 0) (v : velocitySpace N k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    orderedPressureTrace hN a b 0 hd hl (divergence N v.val) s 0 = 0 := by
  have hp := one_location_planes (boundaryTag a) hl
  have hy : gridPoint a 1 = 0 := gridPoint_lower a 1 ((boundaryTag_zero_iff a 1).mp hp.1)
  have hz : gridPoint a 2 = 1 := gridPoint_upper hN a 2 ((boundaryTag_upper_iff hN a 2).mp hp.2)
  have hx₁ : segmentPoint (gridPoint a) (gridPoint b) s 1 = 0 := by
    rw [edge_constant_coordinate a b 1 (by rw [hd]; decide +kernel), hy]
  have hx₂ : segmentPoint (gridPoint a) (gridPoint b) s 2 = 1 := by
    rw [edge_constant_coordinate a b 2 (by rw [hd]; decide +kernel), hz]
  have hfy := ordered_face_coordinate hN a b 0 hd hl 0 3 1 one_face_planes.1
  have hfz := ordered_face_coordinate hN a b 0 hd hl 0 0 2 one_face_planes.2
  have hminor :
      barycentricGradient (R := ℝ) (orderedActualStar hN a b 0 hd hl 0).val.1.2 3 1 *
        barycentricGradient (orderedActualStar hN a b 0 hd hl 0).val.1.2 0 2 -
      barycentricGradient (orderedActualStar hN a b 0 hd hl 0).val.1.2 3 2 *
        barycentricGradient (orderedActualStar hN a b 0 hd hl 0).val.1.2 0 1 ≠ 0 := by
    simp only [orderedActualStar_gradient]
    have he := congrArg (fun z : ℤ => (z : ℝ)) one_face_minor
    push_cast at he
    rw [he]
    norm_num
  exact two_boundary_faces_divergence_zero hN v (orderedActualStar hN a b 0 hd hl 0).val.1
    3 0 1 2 0 1 (Or.inl rfl) (Or.inr rfl)
    (fun l h => (hfy l h).trans hy) (fun l h => (hfz l h).trans hz)
    1 2 hminor _ (ordered_edge_point_mem hN a b 0 hd hl 0 s hs) hx₁ hx₂

theorem boundary_diagonal_equal_pair {N k : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex 2))
    (hl : CanonicalLocation a 2) (v : velocitySpace N k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    orderedPressureTrace hN a b 2 hd hl (divergence N v.val) s 0 =
      orderedPressureTrace hN a b 2 hd hl (divergence N v.val) s 1 := by
  have hp := equal_pair_location_plane (boundaryTag a) hl
  have hz : gridPoint a 0 = 0 := gridPoint_lower a 0 ((boundaryTag_zero_iff a 0).mp hp)
  have hx : segmentPoint (gridPoint a) (gridPoint b) s 0 = 0 := by
    rw [edge_constant_coordinate a b 0 (by rw [hd]; decide +kernel), hz]
  have hf := ordered_shared_face hN a b 2 hd hl 0 1 1 1 equal_pair_faces.1
  have hft := ordered_face_coordinate hN a b 2 hd hl 0 3 0 equal_pair_faces.2.1
  have hfu := ordered_face_coordinate hN a b 2 hd hl 1 3 0 equal_pair_faces.2.2.1
  have hn : barycentricGradient (R := ℝ) (orderedActualStar hN a b 2 hd hl 0).val.1.2 1 1 ≠ 0 := by
    rw [orderedActualStar_gradient, equal_pair_faces.2.2.2]
    norm_num
  exact equal_pair_divergence hN v (orderedActualStar hN a b 2 hd hl 0).val.1
    (orderedActualStar hN a b 2 hd hl 1).val.1 1 1 3 3 hf 0 1 (by decide) hn
    0 (Or.inl rfl) (fun l h => (hft l h).trans hz) (fun l h => (hfu l h).trans hz)
    _ (ordered_edge_point_mem hN a b 2 hd hl 0 s hs) (ordered_edge_point_mem hN a b 2 hd hl 1 s hs) hx

theorem interior_diagonal_checkerboard {N k : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex 4))
    (hl : CanonicalLocation a 4) (v : velocitySpace N k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    orderedPressureTrace hN a b 4 hd hl (divergence N v.val) s 0 -
      orderedPressureTrace hN a b 4 hd hl (divergence N v.val) s 1 -
      orderedPressureTrace hN a b 4 hd hl (divergence N v.val) s 2 +
      orderedPressureTrace hN a b 4 hd hl (divergence N v.val) s 3 = 0 := by
  let n : Space := fun j => (checkerNormal₁ j : ℝ)
  let m : Space := fun j => (checkerNormal₂ j : ℝ)
  have hn₀ (j : Coordinate) :
      barycentricGradient (orderedActualStar hN a b 4 hd hl 0).val.1.2 2 j = (1 : ℝ) * n j := by
    rw [orderedActualStar_gradient, (checkerboard_normals j).1]
    simp [n]
  have hn₂ (j : Coordinate) :
      barycentricGradient (orderedActualStar hN a b 4 hd hl 2).val.1.2 1 j = (1 : ℝ) * n j := by
    rw [orderedActualStar_gradient, (checkerboard_normals j).2.1]
    simp [n]
  have hm₀ (j : Coordinate) :
      barycentricGradient (orderedActualStar hN a b 4 hd hl 0).val.1.2 0 j = (-1 : ℝ) * m j := by
    rw [orderedActualStar_gradient, (checkerboard_normals j).2.2.1]
    simp [m]
  have hm₁ (j : Coordinate) :
      barycentricGradient (orderedActualStar hN a b 4 hd hl 1).val.1.2 0 j = (-1 : ℝ) * m j := by
    rw [orderedActualStar_gradient, (checkerboard_normals j).2.2.2]
    simp [m]
  have hminor : n 0 * m 2 - n 2 * m 0 ≠ 0 := by
    change ((1 : ℤ) : ℝ) * ((1 : ℤ) : ℝ) - ((0 : ℤ) : ℝ) * ((0 : ℤ) : ℝ) ≠ 0
    norm_num
  exact checkerboard_divergence hN v
    (orderedActualStar hN a b 4 hd hl 0).val.1 (orderedActualStar hN a b 4 hd hl 1).val.1
    (orderedActualStar hN a b 4 hd hl 2).val.1 (orderedActualStar hN a b 4 hd hl 3).val.1
    2 2 1 1 0 3 0 3
    (ordered_shared_face hN a b 4 hd hl 0 1 2 2 checkerboard_faces.1)
    (ordered_shared_face hN a b 4 hd hl 2 3 1 1 checkerboard_faces.2.1)
    (ordered_shared_face hN a b 4 hd hl 0 2 0 3 checkerboard_faces.2.2.1)
    (ordered_shared_face hN a b 4 hd hl 1 3 0 3 checkerboard_faces.2.2.2)
    n m 1 1 (-1) (-1) hn₀ hn₂ hm₀ hm₁ 0 2 hminor _
    (ordered_edge_point_mem hN a b 4 hd hl 0 s hs) (ordered_edge_point_mem hN a b 4 hd hl 1 s hs)
    (ordered_edge_point_mem hN a b 4 hd hl 2 s hs) (ordered_edge_point_mem hN a b 4 hd hl 3 s hs)

/-- All seven source rows on the actual canonical mesh edge. -/
theorem actual_canonical_trace_mem_source {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (v : velocitySpace N k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    orderedPressureTrace hN a b c hd hl (divergence N v.val) s ∈ sourceSpace c := by
  fin_cases c
  · exact (zero_source_iff _).mpr (one_sector_zero hN a b hd hl v s hs)
  · exact (unrestricted_source 1 (by decide) (by decide) (by decide)).symm ▸
      (show orderedPressureTrace hN a b 1 hd hl (divergence N v.val) s ∈ ⊤ from trivial)
  · exact (equal_pair_source_iff _).mpr (boundary_diagonal_equal_pair hN a b hd hl v s hs)
  · exact (unrestricted_source 3 (by decide) (by decide) (by decide)).symm ▸
      (show orderedPressureTrace hN a b 3 hd hl (divergence N v.val) s ∈ ⊤ from trivial)
  · exact (checkerboard_source_iff _).mpr (interior_diagonal_checkerboard hN a b hd hl v s hs)
  · exact (unrestricted_source 5 (by decide) (by decide) (by decide)).symm ▸
      (show orderedPressureTrace hN a b 5 hd hl (divergence N v.val) s ∈ ⊤ from trivial)
  · exact (unrestricted_source 6 (by decide) (by decide) (by decide)).symm ▸
      (show orderedPressureTrace hN a b 6 hd hl (divergence N v.val) s ∈ ⊤ from trivial)

theorem pressure_canonical_trace_mem_source {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : pressureSpace N k) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    orderedPressureTrace hN a b c hd hl q.val s ∈ sourceSpace c := by
  obtain ⟨v, hv, hq⟩ := q.property
  rw [← hq]
  exact actual_canonical_trace_mem_source hN a b c hd hl ⟨v, hv⟩ s hs

end FreudenthalSVLean.ActualCanonicalSource
