import Mathlib.Analysis.Fourier.LpSpace
import FreudenthalSVLean.EuclideanCoordinateTransport

/-!
# Agreement of actual L1 Fourier integrals with Hilbert L2 Fourier

For the continuous lifting in manuscript Lemma `means`, the actual
spatial derivatives need not be stipulated Schwartz functions. Whenever
an actual L1 and L2 function has an actual L2 Fourier integral, genuine
Fourier Fubini identifies it with Mathlib's Hilbert L2 transform.
Injectivity of the actual tempered-distribution embedding then gives
Plancherel for these functions. No unproved Sobolev identification or
assumed Fourier norm identity is used.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform
open FreudenthalSVLean.EuclideanCoordinateTransport

noncomputable section

namespace FreudenthalSVLean.GenuineL1L2Fourier

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

theorem L1_fourier_pairing {f : E → ℂ} (hf : Integrable f) (g : 𝓢(E, ℂ)) :
    (∫ ξ : E, g ξ * 𝓕 f ξ) = ∫ x : E, 𝓕 g x * f x := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    (L := innerₗ E) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf g.integrable
  calc
    _ = ∫ ξ : E, 𝓕 f ξ * g ξ := integral_congr_ae
      (Filter.Eventually.of_forall (fun ξ => mul_comm _ _))
    _ = ∫ x : E, f x * 𝓕 g x := by
      simpa only [flip_innerₗ, ContinuousLinearMap.mul_apply', SchwartzMap.fourier_coe] using! h
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))

theorem actual_fourier_toLp {f : E → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure E))
    (hhat : MemLp (𝓕 f) 2 (volume : Measure E)) :
    𝓕 (hf2.toLp f) = hhat.toLp (𝓕 f) := by
  have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  apply hinj
  change Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) =
    Lp.toTemperedDistribution (hhat.toLp (𝓕 f))
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hleft : (∫ x : E, 𝓕 g x * (hf2.toLp f) x) = ∫ x : E, 𝓕 g x * f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hright : (∫ ξ : E, g ξ * (hhat.toLp (𝓕 f)) ξ) = ∫ ξ : E, g ξ * 𝓕 f ξ := by
    apply integral_congr_ae
    filter_upwards [hhat.coeFn_toLp] with ξ hξ
    rw [hξ]
  rw [hleft, hright]
  exact (L1_fourier_pairing hf1 g).symm

theorem complex_toLp_norm_square {f : E → ℂ} (hf : MemLp f 2 (volume : Measure E)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : E, ‖f x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  change (‖hf.toLp f‖ ^ 2 : ℝ) = ((∫ x : E, ‖f x‖ ^ 2 : ℝ) : ℂ)
  calc
    _ = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simpa only [Complex.ofReal_pow] using!
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := hf.toLp f)).symm
    _ = ∫ x : E, inner ℂ ((hf.toLp f) x) ((hf.toLp f) x) := L2.inner_def _ _
    _ = ∫ x : E, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simpa only [Complex.ofReal_pow] using!
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := f x))
    _ = _ := by
      simpa only [Complex.ofRealCLM_apply, Function.comp_def] using!
        (Complex.ofRealCLM.integral_comp_comm
          ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf))

theorem actual_plancherel {f : E → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure E))
    (hhat : MemLp (𝓕 f) 2 (volume : Measure E)) :
    (∫ ξ : E, ‖𝓕 f ξ‖ ^ 2) = ∫ x : E, ‖f x‖ ^ 2 := by
  rw [← complex_toLp_norm_square hhat, ← actual_fourier_toLp hf1 hf2 hhat,
    Lp.norm_fourier_eq, complex_toLp_norm_square hf2]

end FreudenthalSVLean.GenuineL1L2Fourier
