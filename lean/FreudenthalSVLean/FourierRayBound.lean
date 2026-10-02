import FreudenthalSVLean.FourierDirectionalDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform genuine Fourier integrals along rays

For the continuous Bogovskii step in manuscript Lemma `means`, actual
directional Fourier decay is dominated by the integrable rational
weight c/(1+(ct)^2). Its genuine integral is at most pi, including the
zero-frequency case. Consequently every measurable truncation of the
weighted Fourier ray has one bound independent of the frequency and
the truncation. This is a proved analytic ingredient, not an assumed
Calderon--Zygmund theorem or a divergence-solvability claim.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set
open FreudenthalSVLean.FourierDirectionalDecay

noncomputable section

namespace FreudenthalSVLean.FourierRayBound

set_option backward.isDefEq.respectTransparency false

def rayWeight (c t : ℝ) : ℝ := c * (1 + (c * t) ^ 2)⁻¹

theorem rayWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 0 ≤ rayWeight c t := by
  unfold rayWeight
  positivity

theorem rayWeight_integrable {c : ℝ} (hc : 0 ≤ c) : Integrable (rayWeight c) := by
  rcases eq_or_lt_of_le hc with hzero | hpos
  · rw [← hzero]
    change Integrable (fun t : ℝ => (0 : ℝ) * (1 + (0 * t) ^ 2)⁻¹)
    simpa only [zero_mul] using
      (integrable_inv_one_add_sq.const_mul (0 : ℝ))
  · exact (integrable_inv_one_add_sq.comp_mul_left' (ne_of_gt hpos)).const_mul c

theorem rayWeight_integral {c : ℝ} (hc : 0 ≤ c) : (∫ t, rayWeight c t) ≤ Real.pi := by
  rcases eq_or_lt_of_le hc with hzero | hpos
  · simpa [← hzero, rayWeight] using Real.pi_pos.le
  · change (∫ t : ℝ, c * (1 + (c * t) ^ 2)⁻¹) ≤ Real.pi
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun t : ℝ => (1 + t ^ 2)⁻¹) c,
      integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr hpos)]
    simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul, le_refl]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def weightedFourierRay (φ : 𝓢(E, ℂ)) (ξ m : E) (t : ℝ) : ℝ :=
  frequency ξ m * ‖𝓕 φ (t • ξ)‖

theorem weightedFourierRay_nonneg (φ : 𝓢(E, ℂ)) (ξ m : E) (t : ℝ) :
    0 ≤ weightedFourierRay φ ξ m t := mul_nonneg (frequency_nonneg ξ m) (norm_nonneg _)

theorem weightedFourierRay_continuous (φ : 𝓢(E, ℂ)) (ξ m : E) :
    Continuous (weightedFourierRay φ ξ m) :=
  continuous_const.mul (((𝓕 φ).continuous.comp (continuous_id.smul continuous_const)).norm)

theorem weightedFourierRay_integrable (φ : 𝓢(E, ℂ)) (ξ m : E) :
    Integrable (weightedFourierRay φ ξ m) := by
  apply ((rayWeight_integrable (frequency_nonneg ξ m)).const_mul
    (decayConstant φ m)).mono' (weightedFourierRay_continuous φ ξ m).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (weightedFourierRay_nonneg φ ξ m t)]
  exact ray_pointwise_bound φ ξ m t

theorem weightedFourierRay_integral_bound (φ : 𝓢(E, ℂ)) (ξ m : E) :
    (∫ t, weightedFourierRay φ ξ m t) ≤ Real.pi * decayConstant φ m := by
  calc
    _ ≤ ∫ t, decayConstant φ m * rayWeight (frequency ξ m) t :=
      integral_mono (weightedFourierRay_integrable φ ξ m)
        ((rayWeight_integrable (frequency_nonneg ξ m)).const_mul (decayConstant φ m))
        (ray_pointwise_bound φ ξ m)
    _ = decayConstant φ m * ∫ t, rayWeight (frequency ξ m) t := integral_const_mul _ _
    _ ≤ decayConstant φ m * Real.pi := mul_le_mul_of_nonneg_left
      (rayWeight_integral (frequency_nonneg ξ m)) (decayConstant_nonneg φ m)
    _ = _ := mul_comm _ _

theorem weightedFourierRay_setIntegral_bound (φ : 𝓢(E, ℂ)) (ξ m : E) (s : Set ℝ) :
    (∫ t in s, weightedFourierRay φ ξ m t) ≤ Real.pi * decayConstant φ m :=
  (setIntegral_le_integral (weightedFourierRay_integrable φ ξ m)
    (Filter.Eventually.of_forall (weightedFourierRay_nonneg φ ξ m))).trans
      (weightedFourierRay_integral_bound φ ξ m)

end FreudenthalSVLean.FourierRayBound
