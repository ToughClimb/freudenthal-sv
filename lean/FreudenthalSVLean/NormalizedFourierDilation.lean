import FreudenthalSVLean.EuclideanCoordinateTransport
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Genuine normalized Fourier dilation

For the continuous Bogovskii estimate in manuscript Lemma `means`,
the actual normalized spatial dilation r^(-3) f(x/r) has Fourier
transform f-hat(r xi). Its exact three-dimensional volume factor is
proved by genuine Haar-measure change of variables. Actual integrability,
smoothness and compact support are transported, not assumed.
-/

open scoped ContDiff Real
open MeasureTheory FourierTransform
open FreudenthalSVLean.EuclideanCoordinateTransport

noncomputable section

namespace FreudenthalSVLean.NormalizedFourierDilation

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def normalizedDilation (r : ℝ) (f : E → ℂ) (x : E) : ℂ :=
  (r ^ 3)⁻¹ • f (r⁻¹ • x)

theorem normalizedDilation_integrable {r : ℝ} (hr : r ≠ 0) {f : E → ℂ}
    (hf : Integrable f) : Integrable (normalizedDilation r f) :=
  (hf.comp_smul (inv_ne_zero hr)).smul ((r ^ 3)⁻¹ : ℝ)

theorem normalizedDilation_contDiff {r : ℝ} {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (normalizedDilation r f) := by
  have hs : ContDiff ℝ ∞ (fun x : E => (r⁻¹ : ℝ) • x) := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using!
      (((r⁻¹ : ℝ) • ContinuousLinearMap.id ℝ E).contDiff (n := ∞))
  change ContDiff ℝ ∞ (fun x : E => (r ^ 3)⁻¹ • f (r⁻¹ • x))
  simpa only [Function.comp_def] using! (hf.comp hs).const_smul ((r ^ 3)⁻¹ : ℝ)

theorem normalizedDilation_compact {r : ℝ} (hr : r ≠ 0) {f : E → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (normalizedDilation r f) := by
  have hc : HasCompactSupport (fun x : E => f (r⁻¹ • x)) :=
    hf.comp_homeomorph (Homeomorph.smulOfNeZero (α := E) (r⁻¹ : ℝ) (inv_ne_zero hr))
  change HasCompactSupport (fun x : E => (r ^ 3)⁻¹ • f (r⁻¹ • x))
  simpa only [Pi.smul_apply] using!
    hc.smul_left (f := fun _ : E => (r ^ 3)⁻¹)

theorem normalizedDilation_fourier {r : ℝ} (hr : 0 < r) (f : E → ℂ) (ξ : E) :
    𝓕 (normalizedDilation r f) ξ = 𝓕 f (r • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  calc
    _ = (r ^ 3)⁻¹ • ∫ x : E, 𝐞 (-inner ℝ x ξ) • f (r⁻¹ • x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => smul_comm _ _ _)
    _ = (r ^ 3)⁻¹ • ∫ x : E,
        (fun y : E => 𝐞 (-inner ℝ y (r • ξ)) • f y) (r⁻¹ • x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      have he : inner ℝ (r⁻¹ • x) (r • ξ) = inner ℝ x ξ := by
        rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
      rw [he]
    _ = (r ^ 3)⁻¹ • (|r ^ 3| • ∫ y : E, 𝐞 (-inner ℝ y (r • ξ)) • f y) := by
      rw [Measure.integral_comp_inv_smul (volume : Measure E)
        (fun y : E => 𝐞 (-inner ℝ y (r • ξ)) • f y) r]
      simp only [finrank_euclideanSpace_fin]
    _ = _ := by rw [abs_of_pos (pow_pos hr 3), smul_smul, inv_mul_cancel₀ (pow_ne_zero 3 hr.ne'), one_smul]

end FreudenthalSVLean.NormalizedFourierDilation
