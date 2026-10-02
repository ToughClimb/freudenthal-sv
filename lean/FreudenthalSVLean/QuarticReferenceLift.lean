import FreudenthalSVLean.QuarticMacroConformity
import FreudenthalSVLean.RealTransport
import FreudenthalSVLean.StableVertexLift
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Fixed real quartic macro right inverse with genuine gradient stability

For manuscript Lemma `macro`, the actual eleven conforming spatial fields
define one linear right inverse on the zero-sum twelve-mean space.  Its
coefficients are `30 A⁻¹` applied to the first eleven means.  The means
are genuine Cartesian-volume integrals and the energy is the integral of
the nine squared actual polynomial partials.  Conformity, rectangular
zero trace and edge-zero divergence are preserved by the same fixed
linear combination.  Physical transport and global routing are separate
obligations, not hypotheses hidden in this reference theorem.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Matrix
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.QuarticMacroConformity
open FreudenthalSVLean.QuarticVolume
open FreudenthalSVLean.RealTransport
open FreudenthalSVLean.MeanRoutingAlgebra
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.FiniteLinearLifting

noncomputable section

namespace FreudenthalSVLean.QuarticReferenceLift

abbrev MacroVelocity := TetIndex → LocalVelocity
abbrev MeanData := TetIndex → ℝ
abbrev CompatibleMeans := zeroSum (V := TetIndex)

def basis (w : FieldIndex) : MacroVelocity := fun t => realSpatialVector t w

def combinationLinear : (FieldIndex → ℝ) →ₗ[ℝ] MacroVelocity where
  toFun c := ∑ w : FieldIndex, c w • basis w
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem combination_apply (c : FieldIndex → ℝ) (t : TetIndex) :
    combinationLinear c t = ∑ w : FieldIndex, c w • realSpatialVector t w := by
  simp only [combinationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, basis]

def localDiv : LocalVelocity →ₗ[ℝ] MvPolynomial SpatialIndex ℝ where
  toFun := PolynomialCalculus.polynomialDivergence
  map_add' v u := by
    simp [PolynomialCalculus.polynomialDivergence, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' z v := by
    simp only [PolynomialCalculus.polynomialDivergence, Pi.smul_apply,
      Derivation.map_smul, RingHom.id_apply, Finset.smul_sum]

def means : MacroVelocity →ₗ[ℝ] MeanData := LinearMap.pi fun t =>
  (FaceBubbleMean.unitSpatialIntegral (tetEquiv t) (realCellCorner t)).comp
    (localDiv.comp (LinearMap.proj t))

theorem means_basis (t : TetIndex) (w : FieldIndex) :
    means (basis w) t = (divergenceMean t w : ℝ) := by
  change (∫ x in unitChainSet (tetEquiv t) (realCellCorner t),
    eval x (PolynomialCalculus.polynomialDivergence (realSpatialVector t w))) = _
  unfold PolynomialCalculus.polynomialDivergence
  rw [← realSpatialDivergence_eq_derivatives]
  exact spatialDivergence_volume_mean t w

theorem means_combination (c : FieldIndex → ℝ) (t : TetIndex) :
    means (combinationLinear c) t = ∑ w : FieldIndex, c w * (divergenceMean t w : ℝ) := by
  simp only [combinationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, means_basis]

def firstElevenLinear : MeanData →ₗ[ℝ] (FieldIndex → ℝ) :=
  LinearMap.pi fun i => LinearMap.proj (firstElevenTet i)

def weights : MeanData →ₗ[ℝ] (FieldIndex → ℝ) :=
  (30 : ℝ) • (realQuarticMeanMatrixInverse.mulVecLin.comp firstElevenLinear)

def referenceLift : CompatibleMeans →ₗ[ℝ] MacroVelocity :=
  combinationLinear.comp (weights.comp (zeroSum (V := TetIndex)).subtype)

theorem matrix_weights (m : MeanData) :
    realQuarticMeanMatrix *ᵥ weights m = (30 : ℝ) • firstElevenLinear m := by
  change realQuarticMeanMatrix *ᵥ ((30 : ℝ) •
    (realQuarticMeanMatrixInverse *ᵥ firstElevenLinear m)) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    realQuarticMeanMatrix_mul_inverse, Matrix.one_mulVec]

theorem first_means (m : CompatibleMeans) (i : FieldIndex) :
    means (referenceLift m) (firstElevenTet i) = m.val (firstElevenTet i) := by
  change means (combinationLinear (weights m.val)) (firstElevenTet i) = _
  rw [means_combination]
  simp_rw [divergenceMean_eq_matrix_div_thirty, Rat.cast_div, Rat.cast_ofNat]
  have hm := congrFun (matrix_weights m.val) i
  change (∑ w : FieldIndex, realQuarticMeanMatrix i w * weights m.val w) =
    30 * m.val (firstElevenTet i) at hm
  have he : (∑ w : FieldIndex,
      weights m.val w * ((QuarticMacro.quarticMeanMatrix i w : ℚ) : ℝ) / 30) =
      (∑ w : FieldIndex, realQuarticMeanMatrix i w * weights m.val w) / 30 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    change weights m.val w * realQuarticMeanMatrix i w / 30 = _
    ring
  simp only [mul_div_assoc] at he
  rw [he, hm]
  ring

theorem means_sum_zero (c : FieldIndex → ℝ) :
    (∑ t : TetIndex, means (combinationLinear c) t) = 0 := by
  simp only [means_combination]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro w _
  rw [← Finset.mul_sum]
  have hz : (∑ t : TetIndex, (divergenceMean t w : ℝ)) = 0 := by
    have h := actualDivergence_means_sum_zero w
    simpa only [spatialDivergence_volume_mean] using h
  rw [hz, mul_zero]

/-- All twelve prescribed actual means are recovered, including the last
entry forced by the compatibility identity. -/
theorem referenceLift_means (m : CompatibleMeans) : means (referenceLift m) = m.val := by
  have hz := means_sum_zero (weights m.val)
  have hm : (∑ t : TetIndex, m.val t) = 0 := (mem_zeroSum m.val).mp m.property
  have hs : (∑ i : FieldIndex, means (referenceLift m) (firstElevenTet i)) =
      ∑ i : FieldIndex, m.val (firstElevenTet i) := Finset.sum_congr rfl (fun i _ => first_means m i)
  have hl : means (referenceLift m) (11 : TetIndex) = m.val (11 : TetIndex) := by
    change (∑ t : TetIndex, means (referenceLift m) t) = 0 at hz
    rw [Fin.sum_univ_castSucc] at hz hm
    change (∑ i : FieldIndex, means (referenceLift m) i.castSucc) =
      ∑ i : FieldIndex, m.val i.castSucc at hs
    change (∑ i : FieldIndex, means (referenceLift m) i.castSucc) +
      means (referenceLift m) (11 : TetIndex) = 0 at hz
    change (∑ i : FieldIndex, m.val i.castSucc) + m.val (11 : TetIndex) = 0 at hm
    linarith
  funext t
  refine Fin.lastCases hl (fun i => first_means m i) t

theorem combination_degree (c : FieldIndex → ℝ) (t : TetIndex) (j : SpatialIndex) :
    (combinationLinear c t j).totalDegree ≤ 4 := by
  rw [combination_apply]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply totalDegree_finsetSum_le
  intro w _
  exact (totalDegree_smul_le _ _).trans (realSpatialVector_degree t w j)

theorem combination_conforming (c : FieldIndex → ℝ) (t u : TetIndex) (x : Space)
    (ht : x ∈ unitChainSet (tetEquiv t) (realCellCorner t))
    (hu : x ∈ unitChainSet (tetEquiv u) (realCellCorner u)) (j : SpatialIndex) :
    eval x (combinationLinear c t j) = eval x (combinationLinear c u j) := by
  simp only [combination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul,
    map_sum, map_mul, eval_C, realSpatialVector_conforming t u _ x ht hu j]

theorem combination_boundary_zero (c : FieldIndex → ℝ) (t : TetIndex) (x : Space)
    (ht : x ∈ unitChainSet (tetEquiv t) (realCellCorner t))
    (hb : ∃ i : SpatialIndex, x i = 0 ∨ x i = (upperCorner i : ℝ)) (j : SpatialIndex) :
    eval x (combinationLinear c t j) = 0 := by
  simp only [combination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul,
    map_sum, map_mul, eval_C, realSpatialVector_boundary_zero t _ x ht hb j,
    mul_zero, Finset.sum_const_zero]

theorem combination_edge_zero (c : FieldIndex → ℝ) (t : TetIndex)
    (a b : LocalVertex) (s : ℝ) :
    eval (segmentPoint (chainVertex (tetEquiv t) (realCellCorner t) a)
      (chainVertex (tetEquiv t) (realCellCorner t) b) s)
      (localDiv (combinationLinear c t)) = 0 := by
  rw [combination_apply, map_sum]
  simp only [map_smul, smul_eq_C_mul, map_sum, map_mul, eval_C]
  have hd (w : FieldIndex) : localDiv (realSpatialVector t w) = realSpatialDivergence t w :=
    (realSpatialDivergence_eq_derivatives t w).symm
  simp only [hd, realSpatialDivergence_edge, mul_zero, Finset.sum_const_zero]

def elementEnergy (t : TetIndex) (v : LocalVelocity) : ℝ :=
  ∫ x in unitChainSet (tetEquiv t) (realCellCorner t), gradientDensity v x

def referenceEnergy (v : MacroVelocity) : ℝ := ∑ t : TetIndex, elementEnergy t (v t)

theorem referenceEnergy_nonneg (v : MacroVelocity) : 0 ≤ referenceEnergy v :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (gradientDensity_nonneg _))

theorem referenceEnergy_smul (z : ℝ) (v : MacroVelocity) :
    referenceEnergy (z • v) = z ^ 2 * referenceEnergy v := by
  simp only [referenceEnergy, elementEnergy, Pi.smul_apply,
    gradientDensity_smul, integral_const_mul, Finset.mul_sum]

theorem elementEnergy_sum {I : Type*} (t : TetIndex) (s : Finset I) (v : I → LocalVelocity) :
    elementEnergy t (∑ a ∈ s, v a) ≤ (s.card : ℝ) * ∑ a ∈ s, elementEnergy t (v a) := by
  have hv (a : I) : IntegrableOn (gradientDensity (v a))
      (unitChainSet (tetEquiv t) (realCellCorner t)) :=
    (gradientDensity_continuous _).continuousOn.integrableOn_compact
      (μ := volume) (unitChainSet_isCompact _ _)
  have hs : IntegrableOn (gradientDensity (∑ a ∈ s, v a))
      (unitChainSet (tetEquiv t) (realCellCorner t)) :=
    (gradientDensity_continuous _).continuousOn.integrableOn_compact
      (μ := volume) (unitChainSet_isCompact _ _)
  have ht : IntegrableOn (fun x => (s.card : ℝ) * ∑ a ∈ s, gradientDensity (v a) x)
      (unitChainSet (tetEquiv t) (realCellCorner t)) :=
    (integrable_finsetSum s (fun a _ => hv a)).const_mul _
  have hi := integral_mono hs ht (gradientDensity_sum s v)
  simpa only [elementEnergy, integral_const_mul, integral_finsetSum s (fun a _ => hv a)] using hi

theorem referenceEnergy_sum {I : Type*} (s : Finset I) (v : I → MacroVelocity) :
    referenceEnergy (∑ a ∈ s, v a) ≤ (s.card : ℝ) * ∑ a ∈ s, referenceEnergy (v a) := by
  simp only [referenceEnergy, Finset.sum_apply]
  calc
    _ ≤ ∑ t : TetIndex, (s.card : ℝ) * ∑ a ∈ s, elementEnergy t (v a t) :=
      Finset.sum_le_sum (fun t _ => elementEnergy_sum t s (fun a => v a t))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

def basisEnergyBound : ℝ := 1 + ∑ w : FieldIndex, referenceEnergy (basis w)

theorem basisEnergyBound_pos : 0 < basisEnergyBound := by
  have hs := Finset.sum_nonneg (fun w (_ : w ∈ (Finset.univ : Finset FieldIndex)) =>
    referenceEnergy_nonneg (basis w))
  unfold basisEnergyBound
  linarith

theorem basis_energy_le (w : FieldIndex) : referenceEnergy (basis w) ≤ basisEnergyBound := by
  have h := Finset.single_le_sum
    (fun u (_ : u ∈ (Finset.univ : Finset FieldIndex)) => referenceEnergy_nonneg (basis u))
    (Finset.mem_univ w)
  unfold basisEnergyBound
  linarith

theorem combination_energy (c : FieldIndex → ℝ) :
    referenceEnergy (combinationLinear c) ≤
      11 * basisEnergyBound * ∑ w : FieldIndex, (c w) ^ 2 := by
  change referenceEnergy (∑ w : FieldIndex, c w • basis w) ≤ _
  calc
    _ ≤ 11 * ∑ w : FieldIndex, referenceEnergy (c w • basis w) := by
      simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using
        referenceEnergy_sum (Finset.univ : Finset FieldIndex) (fun w => c w • basis w)
    _ = 11 * ∑ w : FieldIndex, (c w) ^ 2 * referenceEnergy (basis w) := by
      simp only [referenceEnergy_smul]
    _ ≤ 11 * ∑ w : FieldIndex, (c w) ^ 2 * basisEnergyBound := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (basis_energy_le w) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem weights_square_bound : ∃ C : ℝ, 0 < C ∧ ∀ m : MeanData,
    (∑ w : FieldIndex, (weights m w) ^ 2) ≤ C * ∑ t : TetIndex, (m t) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := finite_family_map_bounds
    (fun _ : Fin 1 => MeanData) (fun _ : Fin 1 => FieldIndex → ℝ) (fun _ => weights)
  refine ⟨11 * C ^ 2, by positivity, ?_⟩
  intro m
  have hnorm := hb 0 m
  have hm := StableVertexLift.pi_norm_square_le_sum m
  have hsq : ‖weights m‖ ^ 2 ≤ C ^ 2 * ‖m‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg m))).mpr hnorm
    simpa only [mul_pow] using h
  calc
    _ ≤ ∑ _w : FieldIndex, ‖weights m‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      have hw := norm_le_pi_norm (weights m) w
      have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hw
      simpa only [Real.norm_eq_abs, sq_abs] using h
    _ = 11 * ‖weights m‖ ^ 2 := by simp
    _ ≤ 11 * (C ^ 2 * ‖m‖ ^ 2) := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ 11 * (C ^ 2 * ∑ t : TetIndex, (m t) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (sq_nonneg C)) (by norm_num)
    _ = _ := by ring

/-- One fixed linear reference inverse, with a genuine gradient-energy
bound for every compatible mean vector. -/
theorem referenceLift_energy_bound : ∃ C : ℝ, 0 < C ∧ ∀ m : CompatibleMeans,
    referenceEnergy (referenceLift m) ≤ C * ∑ t : TetIndex, (m.val t) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := weights_square_bound
  refine ⟨11 * basisEnergyBound * C, by positivity [basisEnergyBound_pos], ?_⟩
  intro m
  have h := combination_energy (weights m.val)
  have hb' := mul_le_mul_of_nonneg_left (hb m.val)
    (show 0 ≤ 11 * basisEnergyBound by positivity [basisEnergyBound_pos])
  change referenceEnergy (combinationLinear (weights m.val)) ≤ _
  nlinarith

end FreudenthalSVLean.QuarticReferenceLift
