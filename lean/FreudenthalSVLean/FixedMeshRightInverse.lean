import FreudenthalSVLean.GlobalSkeletonLift
import FreudenthalSVLean.PolynomialL2Space
import FreudenthalSVLean.FiniteLinearLifting

/-!
# Genuine stable right inverses on each fixed actual mesh

For the manuscript's separate finite small-mesh argument, the exact
pressure image embeds injectively into a finite product of reference
polynomial L2 spaces.  A fixed linear section of actual divergence has
a true gradient-integral bound by actual pressure energy.  The constant
in this module may depend on the mesh size; this is not the uniform
theorem.  Applying the result to `N=1` supplies the small-mesh case without
any rank certificate or assumed polynomial norm equivalence.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.PolynomialInverseEstimate
open FreudenthalSVLean.PolynomialL2Space
open FreudenthalSVLean.PressureVertexBound
open FreudenthalSVLean.GlobalSkeletonLift
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.FixedMeshRightInverse

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem pullback_injective (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) : Function.Injective (pullback σ o h) := by
  intro p q he
  apply MvPolynomial.funext
  intro x
  have hv := congrArg (fun r => eval (unitNormalize σ o (h⁻¹ • x)) r) he
  simpa only [pullback_eval, MeasurableEquiv.symm_apply_apply,
    smul_smul, mul_inv_cancel₀ hh, one_smul] using hv

def referencePressureEmbedding (N k : ℕ) :
    pressureSpace N k →ₗ[ℝ] (Tet N → degreeSpace (k - 1)) where
  toFun q t := ⟨pullback t.2 (cellOrigin t.1) (meshScale N) (q.val t),
    (mem_restrictTotalDegree _ _ _).mpr
      ((pullback_degree _ _ _ _).trans (pressure_degree_bound q t))⟩
  map_add' q r := by
    funext t
    apply Subtype.ext
    exact (pullbackLinear t.2 (cellOrigin t.1) (meshScale N)).map_add (q.val t) (r.val t)
  map_smul' c q := by
    funext t
    apply Subtype.ext
    exact (pullbackLinear t.2 (cellOrigin t.1) (meshScale N)).map_smul c (q.val t)

theorem referencePressureEmbedding_injective {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Function.Injective (referencePressureEmbedding N k) := by
  intro q r he
  apply Subtype.ext
  funext t
  apply pullback_injective t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN).ne'
  exact congrArg Subtype.val (congrFun he t)

theorem pressure_finiteDimensional {N : ℕ} (hN : 0 < N) (k : ℕ) :
    FiniteDimensional ℝ (pressureSpace N k) :=
  FiniteDimensional.of_injective (referencePressureEmbedding N k)
    (referencePressureEmbedding_injective hN k)

theorem referencePressureEmbedding_energy {N : ℕ} (hN : 0 < N) (k : ℕ)
    (q : pressureSpace N k) :
    (meshScale N) ^ 3 * ∑ t : Tet N, ‖referencePressureEmbedding N k q t‖ ^ 2 =
      pressureEnergy q.val := by
  rw [Finset.mul_sum, pressureEnergy]
  apply Finset.sum_congr rfl
  intro t _
  rw [show ‖referencePressureEmbedding N k q t‖ ^ 2 =
      PolynomialL2.referenceSquareIntegral (pullback t.2 (cellOrigin t.1)
        (meshScale N) (q.val t)) from norm_square_eq_integral _]
  exact (pullback_square_integral t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN) (q.val t)).symm

theorem pi_norm_square_le_sum {I : Type*} [Fintype I]
    {E : Type*} [NormedAddCommGroup E] (f : I → E) :
    ‖f‖ ^ 2 ≤ ∑ i : I, ‖f i‖ ^ 2 := by
  classical
  have hs : 0 ≤ ∑ i : I, ‖f i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖f‖ ≤ Real.sqrt (∑ i : I, ‖f i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hs).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖f j‖) (Finset.mem_univ i)
  exact (Real.le_sqrt (norm_nonneg _) hs).mp hn

def derivativeReferenceMap {N k : ℕ}
    (L : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (t : Tet N) (j i : Fin 3) :
    pressureSpace N k →ₗ[ℝ] SpatialPolynomialL2 where
  toFun q := pullback t.2 (cellOrigin t.1) (meshScale N) (pderiv i ((L q).val t j))
  map_add' q r := by
    change pullback _ _ _ (pderiv i ((L (q + r)).val t j)) =
      pullback _ _ _ (pderiv i ((L q).val t j)) +
        pullback _ _ _ (pderiv i ((L r).val t j))
    rw [L.map_add]
    simp only [Submodule.coe_add, Pi.add_apply, map_add, pullback]
  map_smul' c q := by
    change pullback _ _ _ (pderiv i ((L (c • q)).val t j)) =
      c • pullback _ _ _ (pderiv i ((L q).val t j))
    rw [L.map_smul]
    change pullback t.2 (cellOrigin t.1) (meshScale N)
      (pderiv i (c • ((L q).val t j))) =
        c • pullback t.2 (cellOrigin t.1) (meshScale N) (pderiv i ((L q).val t j))
    rw [(pderiv i).map_smul]
    exact (pullbackLinear t.2 (cellOrigin t.1) (meshScale N)).map_smul c
      (pderiv i ((L q).val t j))

/-- Any fixed linear lift on one fixed mesh is bounded in the genuine
integral quantities.  The source norm is induced by the proved injective
reference-volume representation, not by assumed coefficient estimates. -/
theorem fixed_lift_energy_bound {N : ℕ} (hN : 0 < N) (k : ℕ)
    (L : pressureSpace N k →ₗ[ℝ] velocitySpace N k) :
    ∃ C : ℝ, 0 < C ∧ ∀ q,
      velocityEnergy (L q).val ≤ C * pressureEnergy q.val := by
  classical
  let : NormedAddCommGroup (pressureSpace N k) := NormedAddCommGroup.induced
    (pressureSpace N k) (Tet N → degreeSpace (k - 1))
    (referencePressureEmbedding N k).toAddMonoidHom (referencePressureEmbedding_injective hN k)
  let : NormedSpace ℝ (pressureSpace N k) := NormedSpace.induced ℝ
    (pressureSpace N k) (Tet N → degreeSpace (k - 1)) (referencePressureEmbedding N k)
  let : FiniteDimensional ℝ (pressureSpace N k) := pressure_finiteDimensional hN k
  let T (t : Tet N) (j i : Fin 3) := (derivativeReferenceMap L t j i).toContinuousLinearMap
  let A : ℝ := ∑ t : Tet N, ∑ j : Fin 3, ∑ i : Fin 3, ‖T t j i‖ ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  refine ⟨1 + A, by linarith, ?_⟩
  intro q
  have hnorm : (meshScale N) ^ 3 * ‖q‖ ^ 2 ≤ pressureEnergy q.val := by
    change (meshScale N) ^ 3 * ‖referencePressureEmbedding N k q‖ ^ 2 ≤ _
    exact (mul_le_mul_of_nonneg_left (pi_norm_square_le_sum _)
      (pow_nonneg (meshScale_pos N hN).le 3)).trans_eq
      (referencePressureEmbedding_energy hN k q)
  have hb (t : Tet N) (j i : Fin 3) :
      (∫ x in tetrahedron t, (eval x (pderiv i ((L q).val t j))) ^ 2) ≤
        (meshScale N) ^ 3 * (‖T t j i‖ ^ 2 * ‖q‖ ^ 2) := by
    have hn := (T t j i).le_opNorm q
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    have hp := mul_le_mul_of_nonneg_left hs (pow_nonneg (meshScale_pos N hN).le 3)
    rw [mul_pow] at hp
    change (meshScale N) ^ 3 * ‖derivativeReferenceMap L t j i q‖ ^ 2 ≤ _ at hp
    rw [norm_square_eq_integral] at hp
    exact (pullback_square_integral t.2 (cellOrigin t.1) (meshScale N)
      (meshScale_pos N hN) (pderiv i ((L q).val t j))).le.trans hp
  calc
    _ = ∑ t : Tet N, ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x in tetrahedron t, (eval x (pderiv i ((L q).val t j))) ^ 2 := by
      rw [velocityEnergy_eq_sum]
      exact Finset.sum_congr rfl (fun t _ => localEnergy_eq_sum hN t _)
    _ ≤ ∑ t : Tet N, ∑ j : Fin 3, ∑ i : Fin 3,
        (meshScale N) ^ 3 * (‖T t j i‖ ^ 2 * ‖q‖ ^ 2) := by
      exact Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun j _ =>
        Finset.sum_le_sum (fun i _ => hb t j i)))
    _ = A * ((meshScale N) ^ 3 * ‖q‖ ^ 2) := by
      simp only [A, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ A * pressureEnergy q.val := mul_le_mul_of_nonneg_left hnorm hA
    _ ≤ (1 + A) * pressureEnergy q.val :=
      mul_le_mul_of_nonneg_right (by linarith) (DivergenceEnergy.pressureEnergy_nonneg q.val)

theorem conformingDivergence_surjective (N k : ℕ) :
    Function.Surjective (conformingDivergence N k) := by
  intro q
  obtain ⟨v, hv, he⟩ := q.property
  exact ⟨⟨v, hv⟩, Subtype.ext he⟩

/-- This constant is allowed to depend on the fixed mesh. -/
theorem fixed_mesh_right_inverse {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∃ (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ), 0 < C ∧
      (∀ q, divergence N (R q).val = q.val) ∧
      (∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val) := by
  let : FiniteDimensional ℝ (pressureSpace N k) := pressure_finiteDimensional hN k
  obtain ⟨R, hR⟩ := (conformingDivergence N k).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (conformingDivergence_surjective N k))
  obtain ⟨C, hC, hb⟩ := fixed_lift_energy_bound hN k R
  refine ⟨R, C, hC, ?_, hb⟩
  intro q
  exact congrArg Subtype.val (LinearMap.congr_fun hR q)

theorem unit_mesh_right_inverse (k : ℕ) :
    ∃ (R : pressureSpace 1 k →ₗ[ℝ] velocitySpace 1 k) (C : ℝ), 0 < C ∧
      (∀ q, divergence 1 (R q).val = q.val) ∧
      (∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val) :=
  fixed_mesh_right_inverse (by norm_num) k

end FreudenthalSVLean.FixedMeshRightInverse
