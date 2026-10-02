import FreudenthalSVLean.BogovskiiScalarIdentity

/-!
# Actual uniformly bounded gradients of Bogovskii truncations

For the continuous lift in manuscript Lemma `means`, each actual
physical partial derivative is the difference of two proved scalar
directional integrals. The equality follows by uniqueness of the true
Frechet derivative of the identified spatial fields. Actual Plancherel
estimates, pressure/moment energy transport and summation over all nine
physical components give a fixed, truncation-independent gradient bound.
Actual H1_0 membership has already been proved separately by smooth closure.
-/

open scoped ContDiff SchwartzMap BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.BogovskiiTruncation
open FreudenthalSVLean.BogovskiiC1Truncation
open FreudenthalSVLean.C1CubeH1Zero
open FreudenthalSVLean.BogovskiiSchwartzKernels
open FreudenthalSVLean.BogovskiiPressureSchwartz
open FreudenthalSVLean.ScalarMixtureEstimate
open FreudenthalSVLean.ScalarMixtureDifferentiation
open FreudenthalSVLean.BogovskiiScalarIdentity

noncomputable section

namespace FreudenthalSVLean.BogovskiiGradientEstimate

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def direction (i : Fin 3) : E := euclideanPoint (Pi.single i 1)

def partialConstant (j i : Fin 3) : ℝ :=
  2 * (scalarDerivativeConstant (momentSchwartz j) (direction i) +
    scalarDerivativeConstant rhoSchwartz (direction i))

def gradientConstant : ℝ := ∑ j : Fin 3, ∑ i : Fin 3, partialConstant j i

theorem partialConstant_nonneg (j i : Fin 3) : 0 ≤ partialConstant j i :=
  mul_nonneg (by norm_num) (add_nonneg (scalarDerivativeConstant_nonneg _ _)
    (scalarDerivativeConstant_nonneg _ _))

theorem gradientConstant_nonneg : 0 ≤ gradientConstant :=
  Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => partialConstant_nonneg j i))

theorem truncated_partial_scalar {ε : ℝ} (hε : 0 < ε) (q : Space → ℝ)
    (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : ∀ y : Space, y ∉ cube → q y = 0) (j i : Fin 3) (x : E) :
    (classicalPartial (truncated ε q j) i (coordinates x) : ℂ) =
      scalarDerivativeIntegral ε (momentSchwartz j) (pressureSchwartz q hd hc) (direction i) x -
        scalarDerivativeIntegral ε rhoSchwartz (momentInputSchwartz q hd hc j) (direction i) x := by
  let S₁ := scalarMixtureIntegral ε (momentSchwartz j) (pressureSchwartz q hd hc)
  let S₂ := scalarMixtureIntegral ε rhoSchwartz (momentInputSchwartz q hd hc j)
  have h1 : HasFDerivAt S₁ (fderiv ℝ S₁ x) x :=
    ((scalarMixtureIntegral_contDiff_one hε _ _).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt S₂ (fderiv ℝ S₂ x) x :=
    ((scalarMixtureIntegral_contDiff_one hε _ _).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hb : HasFDerivAt (truncated ε q j) (fderiv ℝ (truncated ε q j) (coordinates x))
      (coordinates x) :=
    ((truncated_contDiff_one hε hd.continuous hs j).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hp := Complex.ofRealCLM.hasFDerivAt.comp x (hb.comp x coordinates.hasFDerivAt)
  have he : (fun z : E => S₁ z - S₂ z) =
      (fun z : E => (truncated ε q j (coordinates z) : ℂ)) :=
    funext (scalarMixture_difference hε q hd hc hs j)
  have hdif := h1.fun_sub h2
  rw [he] at hdif
  have hdir := congrArg (fun L : E →L[ℝ] ℂ => L (direction i)) (hp.unique hdif)
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    sub_apply, direction, coordinates_euclideanPoint] at hdir
  change (classicalPartial (truncated ε q j) i (coordinates x) : ℂ) = _ at hdir
  simpa only [S₁, S₂, direction, scalarMixtureIntegral_partial hε] using! hdir

theorem truncated_partial_L2_bound {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : Function.support q ⊆ cube) (j i : Fin 3) :
    (∫ x : Space, classicalPartial (truncated ε q j) i x ^ 2) ≤
      partialConstant j i * ∫ x : Space, q x ^ 2 := by
  have hzero : ∀ y : Space, y ∉ cube → q y = 0 :=
    fun y hy => Function.notMem_support.mp (fun h => hy (hs h))
  let f := pressureSchwartz q hd hc
  let g := momentInputSchwartz q hd hc j
  let m := direction i
  let D₁ := scalarDerivativeIntegral ε (momentSchwartz j) f m
  let D₂ := scalarDerivativeIntegral ε rhoSchwartz g m
  have hf := pressureSchwartz_support q hd hc hs
  have hg := momentInputSchwartz_support q hd hc hs j
  have hD1 := scalarDerivativeIntegral_memLp hε (momentSchwartz j) f (momentSchwartz_support j) hf m
  have hD2 := scalarDerivativeIntegral_memLp hε rhoSchwartz g rhoSchwartz_support hg m
  have hI1 := (memLp_two_iff_integrable_sq_norm hD1.aestronglyMeasurable).mp hD1
  have hI2 := (memLp_two_iff_integrable_sq_norm hD2.aestronglyMeasurable).mp hD2
  have hreal : MemLp (classicalPartial (truncated ε q j) i) 2 volume :=
    ((truncated_inH1ZeroCube hε hd.continuous hzero j).1.2 i).1
  have hp : MemLp (fun x : E => classicalPartial (truncated ε q j) i (coordinates x)) 2 volume :=
    hreal.comp_measurePreserving coordinates_volume
  have hIp : Integrable (fun x : E => classicalPartial (truncated ε q j) i (coordinates x) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using!
      (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  calc
    _ = ∫ x : E, classicalPartial (truncated ε q j) i (coordinates x) ^ 2 :=
      (integral_pullback _).symm
    _ ≤ ∫ x : E, 2 * ‖D₁ x‖ ^ 2 + 2 * ‖D₂ x‖ ^ 2 := by
      apply integral_mono hIp ((hI1.const_mul 2).add (hI2.const_mul 2))
      intro x
      change classicalPartial (truncated ε q j) i (coordinates x) ^ 2 ≤
        2 * ‖D₁ x‖ ^ 2 + 2 * ‖D₂ x‖ ^ 2
      have he : ‖(classicalPartial (truncated ε q j) i (coordinates x) : ℂ)‖ ^ 2 =
          classicalPartial (truncated ε q j) i (coordinates x) ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [← he, truncated_partial_scalar hε q hd hc hzero j i x]
      have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (norm_sub_le (D₁ x) (D₂ x))
      nlinarith [sq_nonneg (‖D₁ x‖ - ‖D₂ x‖)]
    _ = 2 * (∫ x : E, ‖D₁ x‖ ^ 2) + 2 * (∫ x : E, ‖D₂ x‖ ^ 2) := by
      rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have h1 := scalarDerivativeIntegral_L2_bound hε hεh (momentSchwartz j) f (momentSchwartz_support j) hf m
      have h2 := scalarDerivativeIntegral_L2_bound hε hεh rhoSchwartz g rhoSchwartz_support hg m
      have h3 := momentInputSchwartz_L2_energy q hd hc hs j
      have h4 := pressureSchwartz_L2_energy q hd hc
      have h5 := mul_le_mul_of_nonneg_left h3 (scalarDerivativeConstant_nonneg rhoSchwartz m)
      change _ ≤ 2 * (scalarDerivativeConstant (momentSchwartz j) m +
        scalarDerivativeConstant rhoSchwartz m) * ∫ x : Space, q x ^ 2
      rw [h4] at h1
      nlinarith

theorem truncated_gradient_L2_bound {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : Function.support q ⊆ cube) :
    (∑ j : Fin 3, ∑ i : Fin 3, ∫ x : Space, classicalPartial (truncated ε q j) i x ^ 2) ≤
      gradientConstant * ∫ x : Space, q x ^ 2 := by
  calc
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3, partialConstant j i * ∫ x : Space, q x ^ 2 :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
        (fun i _ => truncated_partial_L2_bound hε hεh q hd hc hs j i))
    _ = _ := by simp only [gradientConstant, Finset.sum_mul]

end FreudenthalSVLean.BogovskiiGradientEstimate
