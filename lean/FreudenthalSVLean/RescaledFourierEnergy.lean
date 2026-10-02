import FreudenthalSVLean.SmallScaleFourierKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Genuine integrable rescaled Fourier energy

For the continuous Bogovskii estimate in manuscript Lemma `means`, the
lower-half Fourier energy is rescaled by eta=(1-t)xi. The exact volume
Jacobian and directional frequency factor together give (1-t)^(-4).
The true ray integral bounds each eta fiber uniformly, and Fubini then
gives a global integrable majorant in terms of the actual input L2 norm.
This is the small-scale estimate in Durán, arXiv:1103.3718, Section 2,
not an assumed singular-integral theorem.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set Filter
open FreudenthalSVLean.FourierDirectionalDecay
open FreudenthalSVLean.FourierRayBound
open FreudenthalSVLean.BogovskiiRayRescaling
open FreudenthalSVLean.SmallScaleFourierKernel

noncomputable section

namespace FreudenthalSVLean.RescaledFourierEnergy

set_option backward.isDefEq.respectTransparency false

def rescaledDensity (φ f : 𝓢(E, ℂ)) (m η : E) (t : ℝ) : ℝ :=
  ((1 - t) ^ 4)⁻¹ * weightedFourierRay φ η m (compression t) * ‖𝓕 f η‖ ^ 2

theorem rescaledDensity_nonneg (φ f : 𝓢(E, ℂ)) (m η : E) (t : ℝ) :
    0 ≤ rescaledDensity φ f m η t :=
  mul_nonneg (mul_nonneg (by positivity) (weightedFourierRay_nonneg φ η m _)) (sq_nonneg _)

theorem rescaledDensity_measurable (φ f : 𝓢(E, ℂ)) (m : E) :
    Measurable (fun p : E × ℝ => rescaledDensity φ f m p.1 p.2) := by
  unfold rescaledDensity weightedFourierRay compression frequency
  fun_prop

theorem rescaledDensity_integrableOn (φ f : 𝓢(E, ℂ)) (m η : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    IntegrableOn (rescaledDensity φ f m η) (Icc ε (1 / 2 : ℝ)) := by
  exact IntegrableOn.mono
    ((small_half_integrable _ (weightedFourierRay_continuous φ η m)).mul_const
      (‖𝓕 f η‖ ^ 2)) (fun t ht => ⟨hε.trans ht.1, ht.2⟩) le_rfl

theorem rescaledDensity_fiber_bound (φ f : 𝓢(E, ℂ)) (m η : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ t in Icc ε (1 / 2 : ℝ), rescaledDensity φ f m η t) ≤
      (4 * (Real.pi * decayConstant φ m)) * ‖𝓕 f η‖ ^ 2 := by
  change (∫ t in Icc ε (1 / 2 : ℝ),
    (((1 - t) ^ 4)⁻¹ * weightedFourierRay φ η m (compression t)) * ‖𝓕 f η‖ ^ 2) ≤ _
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (truncated_small_half_ray_bound φ η m hε) (sq_nonneg _)

theorem fourier_norm_square_integrable (f : 𝓢(E, ℂ)) :
    Integrable (fun η : E => ‖𝓕 f η‖ ^ 2) (volume : Measure E) :=
  (memLp_two_iff_integrable_sq_norm (𝓕 f).continuous.aestronglyMeasurable).mp
    ((𝓕 f).memLp 2)

theorem rescaledDensity_prod_integrable (φ f : 𝓢(E, ℂ)) (m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun p : E × ℝ => rescaledDensity φ f m p.1 p.2)
      ((volume : Measure E).prod (volume.restrict (Icc ε (1 / 2 : ℝ)))) := by
  have hm := (rescaledDensity_measurable φ f m).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun η => rescaledDensity_integrableOn φ f m η hε), ?_⟩
  apply ((fourier_norm_square_integrable f).const_mul (4 * (Real.pi * decayConstant φ m))).mono'
    (hm.norm.integral_prod_right'.aestronglyMeasurable)
  filter_upwards with η
  have he : (∫ t in Icc ε (1 / 2 : ℝ), ‖rescaledDensity φ f m η t‖) =
      ∫ t in Icc ε (1 / 2 : ℝ), rescaledDensity φ f m η t :=
    integral_congr_ae (Eventually.of_forall (fun t =>
      Real.norm_of_nonneg (rescaledDensity_nonneg φ f m η t)))
  rw [he, Real.norm_of_nonneg (integral_nonneg (rescaledDensity_nonneg φ f m η))]
  exact rescaledDensity_fiber_bound φ f m η hε

theorem rescaledDensity_double_integral_bound (φ f : 𝓢(E, ℂ)) (m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ η : E, ∫ t in Icc ε (1 / 2 : ℝ), rescaledDensity φ f m η t) ≤
      (4 * (Real.pi * decayConstant φ m)) * ∫ η : E, ‖𝓕 f η‖ ^ 2 := by
  calc
    _ ≤ ∫ η : E, (4 * (Real.pi * decayConstant φ m)) * ‖𝓕 f η‖ ^ 2 :=
      integral_mono (rescaledDensity_prod_integrable φ f m hε).integral_prod_left
        ((fourier_norm_square_integrable f).const_mul _) (fun η => rescaledDensity_fiber_bound φ f m η hε)
    _ = _ := integral_const_mul _ _

end FreudenthalSVLean.RescaledFourierEnergy
