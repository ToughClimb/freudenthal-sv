import FreudenthalSVLean.NormalizedFourierDilation
import FreudenthalSVLean.SmallScaleFourierKernel
import Mathlib.Analysis.Fourier.Convolution

/-!
# The actual Fourier transform of a spatial Bogovskii mixture

For the continuous lift in manuscript Lemma `means`, the normalized
affine mixture is a genuine convolution of two normalized dilations.
Its Fourier transform is therefore the product of the two actual
transforms at t xi and (1-t) xi. For a directional derivative of the
kernel, the factor t cancels exactly against the spatial derivative's
t^(-1). This proves the actual fixed-time identity used in the small-
scale estimate of Durán, arXiv:1103.3718, Section 2.
-/

open scoped SchwartzMap Real LineDeriv
open MeasureTheory FourierTransform Convolution
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.SmallScaleFourierKernel

noncomputable section

namespace FreudenthalSVLean.BogovskiiMixtureFourier

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def spatialMixture (t : ℝ) (φ f : E → ℂ) (x : E) : ℂ :=
  ∫ y : E, normalizedDilation t φ (x - (1 - t) • y) * f y

theorem spatialMixture_eq_convolution {t : ℝ} (ht : t < 1)
    (φ f : E → ℂ) (x : E) :
    spatialMixture t φ f x =
      (normalizedDilation t φ ⋆[ContinuousLinearMap.mul ℂ ℂ]
        normalizedDilation (1 - t) f) x := by
  have hs : 0 < 1 - t := sub_pos.mpr ht
  symm
  rw [convolution_mul_swap]
  calc
    _ = ( (1 - t) ^ 3)⁻¹ • ∫ v : E,
        normalizedDilation t φ (x - v) * f ((1 - t)⁻¹ • v) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with v
      simp only [normalizedDilation, Complex.real_smul]
      ring
    _ = ((1 - t) ^ 3)⁻¹ • ∫ v : E,
        (fun y : E => normalizedDilation t φ (x - (1 - t) • y) * f y)
          ((1 - t)⁻¹ • v) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with v
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    _ = ((1 - t) ^ 3)⁻¹ • (|(1 - t) ^ 3| •
        ∫ y : E, normalizedDilation t φ (x - (1 - t) • y) * f y) := by
      rw [Measure.integral_comp_inv_smul (volume : Measure E)
        (fun y : E => normalizedDilation t φ (x - (1 - t) • y) * f y) (1 - t)]
      simp only [finrank_euclideanSpace_fin]
    _ = _ := by
      rw [abs_of_pos (pow_pos hs 3), smul_smul,
        inv_mul_cancel₀ (pow_ne_zero 3 hs.ne'), one_smul]
      rfl

theorem spatialMixture_fourier {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {φ f : E → ℂ} (hφ : Integrable φ) (hf : Integrable f) (ξ : E) :
    𝓕 (spatialMixture t φ f) ξ = 𝓕 φ (t • ξ) * 𝓕 f ((1 - t) • ξ) := by
  have he : spatialMixture t φ f =
      normalizedDilation t φ ⋆[ContinuousLinearMap.mul ℂ ℂ]
        normalizedDilation (1 - t) f :=
    funext (spatialMixture_eq_convolution ht1 φ f)
  rw [he, Real.fourier_mul_convolution_eq
    (normalizedDilation_integrable ht.ne' hφ)
    (normalizedDilation_integrable (sub_pos.mpr ht1).ne' hf),
    normalizedDilation_fourier ht,
    normalizedDilation_fourier (sub_pos.mpr ht1)]

def derivativeMixture (t : ℝ) (φ f : 𝓢(E, ℂ)) (m : E) (x : E) : ℂ :=
  t⁻¹ • spatialMixture t (∂_{m} φ : 𝓢(E, ℂ)) f x

theorem actual_fourier_const_smul (c : ℂ) (f : E → ℂ) (ξ : E) :
    𝓕 (c • f) ξ = c • 𝓕 f ξ := by
  simpa only [Real.fourier_eq, Pi.smul_apply] using!
    congrArg (fun g : E → ℂ => g ξ)
      (VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ E) f c)

theorem derivativeMixture_fourier {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (φ f : 𝓢(E, ℂ)) (m ξ : E) :
    𝓕 (derivativeMixture t φ f m) ξ = FourierKernel φ f m ξ t := by
  have hg : (fun x : E => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hd := congrArg (fun g : 𝓢(E, ℂ) => g (t • ξ))
    (SchwartzMap.fourier_lineDerivOp_eq φ m)
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    real_inner_smul_left, smul_eq_mul, Complex.real_smul] at hd
  have he : derivativeMixture t φ f m =
      (t⁻¹ : ℂ) • spatialMixture t (∂_{m} φ : 𝓢(E, ℂ)) f := by
    ext x
    simp only [derivativeMixture, Pi.smul_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv]
  rw [he, actual_fourier_const_smul,
    spatialMixture_fourier ht ht1 (∂_{m} φ).integrable f.integrable]
  change (t⁻¹ : ℂ) * (𝓕 (∂_{m} φ) (t • ξ) * 𝓕 f ((1 - t) • ξ)) = _
  rw [hd]
  simp only [FourierKernel, Complex.ofReal_mul]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

end FreudenthalSVLean.BogovskiiMixtureFourier
