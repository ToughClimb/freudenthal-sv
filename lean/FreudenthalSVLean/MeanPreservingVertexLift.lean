import FreudenthalSVLean.ActualRawVertexMean

/-!
# Fixed, conforming, mean-preserving vertex correction

For manuscript Lemma `vertex-local` and equation `vertex-explicit-operator`,
the actual cubic nodal correction is composed with the proved fixed mean
router.  The result has exactly the prescribed compatibility-image
divergence values at the marked vertex, protects every other vertex row,
has zero divergence integral on every mesh tetrahedron, and is supported
on the marked vertex star.  The geometry and all linear maps are fixed
before the input data arrive.

This module proves the algebraic and geometric properties of the actual
velocity.  Uniform gradient-energy bounds and identification of arbitrary
pressure traces with the compatibility image remain separate obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.RawVertexTrace
open FreudenthalSVLean.ActualRawVertexMean

noncomputable section

namespace FreudenthalSVLean.MeanPreservingVertexLift

def meanPreservingRaw {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    JetSpace (boundaryTag n) →ₗ[ℝ] velocitySpace N 3 :=
  rawConforming hN n - (supportedZeroVertexCubic n).subtype.comp
    ((starRouting hN n).comp (rawMeanZeroSum hN n))

theorem meanPreservingRaw_apply {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) :
    (meanPreservingRaw hN n x).val =
      rawField n x - (starRouting hN n (rawMeanZeroSum hN n x)).val.val := by
  rfl

theorem meanPreservingRaw_zero_off_star {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (t : Tet N)
    (ht : ∀ a : Vertex, gridVertexOfTet t a ≠ n) (j : Coordinate) :
    (meanPreservingRaw hN n x).val t j = 0 := by
  rw [meanPreservingRaw_apply]
  simp only [Pi.sub_apply, rawField_zero_off_star n x t ht,
    starRouting_zero_off_star hN n _ t ht, sub_zero]

theorem meanPreservingRaw_vertex_divergence {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (ta : VertexStar n) :
    eval (vertex ta.val.1 ta.val.2)
      (divergence N (meanPreservingRaw hN n x).val ta.val.1) =
        (meshScale N)⁻¹ * compatibility (boundaryTag n) x (catalogIncidenceEquiv hN n ta) := by
  rw [meanPreservingRaw_apply]
  simp only [map_sub, Pi.sub_apply, starRouting_protects_vertices, sub_zero]
  exact rawField_vertex_divergence hN n x ta

theorem meanPreservingRaw_protects_other_vertices {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (t : Tet N) (l : Vertex)
    (hl : gridVertexOfTet t l ≠ n) :
    eval (vertex t l) (divergence N (meanPreservingRaw hN n x).val t) = 0 := by
  rw [meanPreservingRaw_apply]
  simp only [map_sub, Pi.sub_apply, starRouting_protects_vertices, sub_zero]
  change eval _ (∑ j : Coordinate, pderiv j (rawField n x t j)) = 0
  simp only [map_sum, rawField_protects_other_vertices hN n x t l hl,
    Finset.sum_const_zero]

/-- Every true element mean is preserved, including every element outside
the local support. -/
theorem meanPreservingRaw_mean_zero {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (t : Tet N) :
    tetIntegral hN t (divergence N (meanPreservingRaw hN n x).val t) = 0 := by
  classical
  by_cases ht : ∃ a : Vertex, gridVertexOfTet t a = n
  · obtain ⟨a, ha⟩ := ht
    let ta : VertexStar n := ⟨(t, a), ha⟩
    have he := congrFun (starRouting_means hN n (rawMeanZeroSum hN n x)) ta
    change tetIntegral hN t
      (divergence N (starRouting hN n (rawMeanZeroSum hN n x)).val.val t) =
        rawMeans hN n x ta at he
    rw [meanPreservingRaw_apply]
    simp only [map_sub, Pi.sub_apply, he]
    simp only [rawMeans, LinearMap.coe_mk, AddHom.coe_mk, ta, sub_self]
  · push Not at ht
    have hz : (meanPreservingRaw hN n x).val t = 0 := by
      funext j
      exact meanPreservingRaw_zero_off_star hN n x t ht j
    change tetIntegral hN t (∑ j : Coordinate, pderiv j ((meanPreservingRaw hN n x).val t j)) = 0
    simp only [hz, Pi.zero_apply, map_zero, Finset.sum_const_zero]

def vertexLift {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (J : (compatibility (boundaryTag n)).range →ₗ[ℝ] JetSpace (boundaryTag n)) :
    (compatibility (boundaryTag n)).range →ₗ[ℝ] velocitySpace N 3 :=
  (meanPreservingRaw hN n).comp ((meshScale N) • J)

theorem vertexLift_right_inverse {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (J : (compatibility (boundaryTag n)).range →ₗ[ℝ] JetSpace (boundaryTag n))
    (hJ : ∀ x, compatibility (boundaryTag n) (J x) = x.val)
    (x : (compatibility (boundaryTag n)).range) (ta : VertexStar n) :
    eval (vertex ta.val.1 ta.val.2)
      (divergence N (vertexLift hN n J x).val ta.val.1) =
        x.val (catalogIncidenceEquiv hN n ta) := by
  change eval _ (divergence N
    (meanPreservingRaw hN n ((meshScale N) • J x)).val ta.val.1) = _
  rw [meanPreservingRaw_vertex_divergence]
  simp only [map_smul, hJ, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (meshScale_pos N hN).ne', one_mul]

theorem vertexLift_mean_zero {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (J : (compatibility (boundaryTag n)).range →ₗ[ℝ] JetSpace (boundaryTag n))
    (x : (compatibility (boundaryTag n)).range) (t : Tet N) :
    tetIntegral hN t (divergence N (vertexLift hN n J x).val t) = 0 :=
  meanPreservingRaw_mean_zero hN n ((meshScale N) • J x) t

theorem vertexLift_protects_other_vertices {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (J : (compatibility (boundaryTag n)).range →ₗ[ℝ] JetSpace (boundaryTag n))
    (x : (compatibility (boundaryTag n)).range) (t : Tet N) (l : Vertex)
    (hl : gridVertexOfTet t l ≠ n) :
    eval (vertex t l) (divergence N (vertexLift hN n J x).val t) = 0 :=
  meanPreservingRaw_protects_other_vertices hN n ((meshScale N) • J x) t l hl

theorem vertexLift_zero_off_star {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (J : (compatibility (boundaryTag n)).range →ₗ[ℝ] JetSpace (boundaryTag n))
    (x : (compatibility (boundaryTag n)).range) (t : Tet N)
    (ht : ∀ a : Vertex, gridVertexOfTet t a ≠ n) (j : Coordinate) :
    (vertexLift hN n J x).val t j = 0 :=
  meanPreservingRaw_zero_off_star hN n ((meshScale N) • J x) t ht j

end FreudenthalSVLean.MeanPreservingVertexLift
