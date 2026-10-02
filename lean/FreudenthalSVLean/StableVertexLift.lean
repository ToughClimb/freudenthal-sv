import FreudenthalSVLean.ConformingVertexCompatibility
import FreudenthalSVLean.StableRawVertexField
import Mathlib.Analysis.Real.Sqrt

/-!
# Uniform physical stability of the mean-preserving vertex lift

For manuscript Lemma `vertex-local`, the actual cubic correction and
actual face router are combined in the genuine gradient energy.  The raw
means have squared size `O(h⁴ ‖s‖²)` and the router has energy
`O(h⁻³ sum m_T²)`, so the mean-preserving field has energy `O(h ‖s‖²)`.
The fixed compatibility-image right inverse and amplitude `h` then give
`O(h³ sum d_T²)` for the prescribed divergence-vertex data.  One constant
and one family of linear right inverses are chosen before all mesh sizes
and vertices.  Global overlap and the Sobolev interface are separate
obligations.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.FiniteLinearLifting
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.StableStarMeanRouting
open FreudenthalSVLean.VertexMeanCancellation
open FreudenthalSVLean.ActualRawVertexMean
open FreudenthalSVLean.MeanPreservingVertexLift
open FreudenthalSVLean.StableRawVertexField
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableVertexLift

theorem pi_norm_square_le_sum {I : Type*} [Fintype I] (x : I → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i : I, (x i) ^ 2 := by
  classical
  let S := ∑ i : I, (x i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖x‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs, sq_abs] using
      Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => sq_nonneg (x j))
        (Finset.mem_univ i)
  have hs := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg S)).mpr hn
  simpa only [Real.sq_sqrt hS] using hs

theorem rawMeans_uniform_square : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N)
    (n : GridVertex N) (x : JetSpace (boundaryTag n)),
    (∑ ta : VertexStar n, (rawMeans hN n x ta) ^ 2) ≤
      C * (meshScale N) ^ 4 * ‖x‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := finite_family_map_bounds JetSpace VertexData localMeanMap
  refine ⟨24 * (C / 60) ^ 2, by positivity, ?_⟩
  intro N hN n x
  have hm (ta : VertexStar n) :
      (localMeanNumerator (boundaryTag n) x (RawVertexField.catalogIncidenceEquiv hN n ta)) ^ 2 ≤
        (C * ‖x‖) ^ 2 := by
    have hn := (norm_le_pi_norm (localMeanMap (boundaryTag n) x)
      (RawVertexField.catalogIncidenceEquiv hN n ta)).trans (hb (boundaryTag n) x)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg x))).mpr hn
    simpa only [localMeanMap, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, sq_abs] using hs
  calc
    _ ≤ ∑ _ta : VertexStar n, ((meshScale N) ^ 2 / 60) ^ 2 * (C * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro ta _
      rw [rawMeans_catalog, mul_pow]
      exact mul_le_mul_of_nonneg_left (hm ta) (sq_nonneg _)
    _ = (Fintype.card (VertexStar n) : ℝ) *
        (((meshScale N) ^ 2 / 60) ^ 2 * (C * ‖x‖) ^ 2) := by simp
    _ ≤ 24 * (((meshScale N) ^ 2 / 60) ^ 2 * (C * ‖x‖) ^ 2) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast star_size_bound n)
      positivity
    _ = _ := by ring

theorem routedRaw_uniform_energy : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N)
    (n : GridVertex N) (x : JetSpace (boundaryTag n)),
    velocityEnergy (starRouting hN n (rawMeanZeroSum hN n x)).val.val ≤
      C * meshScale N * ‖x‖ ^ 2 := by
  obtain ⟨CM, hCM, hm⟩ := rawMeans_uniform_square
  obtain ⟨CR, hCR, hr⟩ := starRouting_uniform_energy
  refine ⟨CR * CM, mul_pos hCR hCM, ?_⟩
  intro N hN n x
  calc
    _ ≤ CR * ((meshScale N) ^ 3)⁻¹ * ∑ ta : VertexStar n, (rawMeans hN n x ta) ^ 2 :=
      hr N hN n (rawMeanZeroSum hN n x)
    _ ≤ CR * ((meshScale N) ^ 3)⁻¹ * (CM * (meshScale N) ^ 4 * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left (hm N hN n x)
      positivity [meshScale_pos N hN]
    _ = _ := by field_simp [(meshScale_pos N hN).ne']

theorem velocityEnergy_neg {N : ℕ} (v : BrokenVelocity N) : velocityEnergy (-v) = velocityEnergy v := by
  have h := velocityEnergy_smul (-1 : ℝ) v
  simpa only [neg_one_smul, neg_one_sq, one_mul] using h

theorem velocityEnergy_sub {N : ℕ} (hN : 0 < N) (v w : BrokenVelocity N) :
    velocityEnergy (v - w) ≤ 2 * (velocityEnergy v + velocityEnergy w) := by
  have h := velocityEnergy_sum hN Finset.univ (fun b : Bool => if b then v else -w)
  simpa [velocityEnergy_neg, sub_eq_add_neg, add_comm] using h

theorem meanPreservingRaw_uniform_energy : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N)
    (n : GridVertex N) (x : JetSpace (boundaryTag n)),
    velocityEnergy (meanPreservingRaw hN n x).val ≤ C * meshScale N * ‖x‖ ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := rawField_uniform_energy
  obtain ⟨C1, hC1, h1⟩ := routedRaw_uniform_energy
  refine ⟨2 * (C0 + C1), by positivity, ?_⟩
  intro N hN n x
  rw [meanPreservingRaw_apply]
  calc
    _ ≤ 2 * (velocityEnergy (RawVertexField.rawField n x) +
        velocityEnergy (starRouting hN n (rawMeanZeroSum hN n x)).val.val) :=
      velocityEnergy_sub hN _ _
    _ ≤ 2 * (C0 * meshScale N * ‖x‖ ^ 2 + C1 * meshScale N * ‖x‖ ^ 2) := by
      linarith [h0 N hN n x, h1 N hN n x]
    _ = _ := by ring

/-- Uniformly stable actual supported cubic vertex correction on its
complete compatibility image.  The constant and fixed linear inverse
family are quantified before every physical mesh parameter. -/
theorem vertexLift_uniform_energy :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ∀ b : BoundaryWord,
      (compatibility b).range →ₗ[ℝ] JetSpace b,
      (∀ b (x : (compatibility b).range), compatibility b (J b x) = x.val) ∧
      (∀ (N : ℕ) (hN : 0 < N) (n : GridVertex N) (x : (compatibility (boundaryTag n)).range),
        velocityEnergy (vertexLift hN n (J (boundaryTag n)) x).val ≤
          C * (meshScale N) ^ 3 * ∑ t : Incidence (boundaryTag n), (x.val t) ^ 2) := by
  obtain ⟨CJ, hCJ, J, hright, hJ⟩ := fixed_bounded_compatibility_lifts
  obtain ⟨CE, hCE, hE⟩ := meanPreservingRaw_uniform_energy
  refine ⟨CE * CJ ^ 2, by positivity, J, hright, ?_⟩
  intro N hN n x
  have hh : 0 < meshScale N := meshScale_pos N hN
  have hJsq : ‖J (boundaryTag n) x‖ ^ 2 ≤ (CJ * ‖x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hCJ.le (norm_nonneg x))).mpr (hJ _ x)
  have hx : ‖x‖ ^ 2 ≤ ∑ t : Incidence (boundaryTag n), (x.val t) ^ 2 :=
    pi_norm_square_le_sum x.val
  change velocityEnergy (meanPreservingRaw hN n ((meshScale N) • J (boundaryTag n) x)).val ≤ _
  calc
    _ ≤ CE * meshScale N * ‖(meshScale N) • J (boundaryTag n) x‖ ^ 2 := hE N hN n _
    _ = CE * (meshScale N) ^ 3 * ‖J (boundaryTag n) x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      ring
    _ ≤ CE * (meshScale N) ^ 3 * (CJ * ‖x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hJsq (by positivity)
    _ = (CE * CJ ^ 2) * (meshScale N) ^ 3 * ‖x‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)

end FreudenthalSVLean.StableVertexLift
