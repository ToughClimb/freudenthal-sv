import FreudenthalSVLean.BogovskiiDivergenceIdentity
import FreudenthalSVLean.BogovskiiPressureSchwartz

/-!
# Actual pressure-mixture change of variables

For the continuous lifting in manuscript Lemma `means`, the mass mixture
in the true divergence formula is the actual normalized scalar mixture.
Convolution symmetry exchanges the kernel and pressure integrations,
giving the genuine nonsingular formula
(1-t)^(-3) integral rho(z) q((x-t z)/(1-t)) dz for 0<t<1.
The identities use exact volume transport and actual Bochner integrals.
-/

open scoped ContDiff SchwartzMap Real
open MeasureTheory FourierTransform Convolution
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.EuclideanCubeTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiKernelDivergence
open FreudenthalSVLean.BogovskiiDivergenceIdentity
open FreudenthalSVLean.BogovskiiSchwartzKernels
open FreudenthalSVLean.BogovskiiPressureSchwartz
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.BogovskiiMixtureFourier

noncomputable section

namespace FreudenthalSVLean.BogovskiiPressureMixture

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

theorem spatialMixture_swap {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (φ f : E → ℂ) (x : E) : spatialMixture t φ f x = spatialMixture (1 - t) f φ x := by
  have hm : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
    ext
    exact mul_comm _ _
  calc
    _ = (normalizedDilation t φ ⋆[ContinuousLinearMap.mul ℂ ℂ]
        normalizedDilation (1 - t) f) x := spatialMixture_eq_convolution ht1 φ f x
    _ = (normalizedDilation (1 - t) f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        normalizedDilation t φ) x := by rw [← convolution_flip, hm]
    _ = _ := by
      rw [spatialMixture_eq_convolution (by linarith : 1 - t < 1) f φ x]
      simp only [sub_sub_cancel]

theorem mass_input_integrable (t : ℝ) (x : Space) {q : Space → ℝ}
    (hq : Continuous q) (hc : HasCompactSupport q) :
    Integrable (fun y : Space => massKernel t x y * q y) := by
  have hm : Continuous (fun y : Space => massKernel t x y * q y) := by
    unfold massKernel kernelArgument
    exact (continuous_const.mul (rho_contDiff.continuous.comp (by fun_prop))).mul hq
  exact hm.integrable_of_hasCompactSupport hc.mul_left

theorem smoothedPressure_complex {t : ℝ} (ht : 0 < t) (q : Space → ℝ)
    (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (x : E) :
    (smoothedPressure t q (coordinates x) : ℂ) =
      spatialMixture t rhoSchwartz (pressureSchwartz q hd hc) x := by
  symm
  calc
    _ = ∫ y : E, ((massKernel t (coordinates x) (coordinates y) * q (coordinates y) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      change ((t ^ 3)⁻¹ : ℝ) • rhoSchwartz (mixtureArgument t x y) * pressureSchwartz q hd hc y = _
      rw [rhoSchwartz_apply, pressureSchwartz_apply, coordinates_mixtureArgument ht.ne']
      simp only [Complex.real_smul, ← Complex.ofReal_mul, massKernel]
    _ = ∫ y : Space, ((massKernel t (coordinates x) y * q y : ℝ) : ℂ) :=
      integral_pullback (fun y => ((massKernel t (coordinates x) y * q y : ℝ) : ℂ))
    _ = _ := by
      simpa only [Complex.ofRealCLM_apply, Function.comp_def, smoothedPressure] using!
        (Complex.ofRealCLM.integral_comp_comm (mass_input_integrable t (coordinates x) hd.continuous hc))

def pressureArgument (t : ℝ) (x z : Space) : Space := (1 - t)⁻¹ • (x - t • z)

theorem smoothedPressure_formula {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (q : Space → ℝ)
    (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (x : Space) :
    smoothedPressure t q x = ((1 - t) ^ 3)⁻¹ *
      ∫ z : Space, rho z * q (pressureArgument t x z) := by
  have hi : Integrable (fun z : Space => rho z * q (pressureArgument t x z)) := by
    have hcont : Continuous (fun z : Space => rho z * q (pressureArgument t x z)) :=
      rho_contDiff.continuous.mul (hd.continuous.comp (by unfold pressureArgument; fun_prop))
    exact hcont.integrable_of_hasCompactSupport rho_compact.mul_right
  apply Complex.ofRealLI.injective
  change (smoothedPressure t q x : ℂ) = (((1 - t) ^ 3)⁻¹ *
    ∫ z : Space, rho z * q (pressureArgument t x z) : ℝ)
  rw [← coordinates_euclideanPoint x, smoothedPressure_complex ht q hd hc (euclideanPoint x),
    spatialMixture_swap ht ht1, spatialMixture]
  calc
    _ = ((1 - t) ^ 3)⁻¹ • ∫ z : E, ((rho (coordinates z) *
        q (pressureArgument t (coordinates (euclideanPoint x)) (coordinates z)) : ℝ) : ℂ) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      simp only [normalizedDilation, pressureSchwartz_apply, rhoSchwartz_apply, sub_sub_cancel,
        pressureArgument, map_smul, map_sub, Complex.real_smul, ← Complex.ofReal_mul]
      congr 1
      ring
    _ = ((1 - t) ^ 3)⁻¹ • ∫ z : Space,
        ((rho z * q (pressureArgument t (coordinates (euclideanPoint x)) z) : ℝ) : ℂ) := by
      rw [integral_pullback (fun z => ((rho z * q (pressureArgument t (coordinates (euclideanPoint x)) z) : ℝ) : ℂ))]
    _ = _ := by
      rw [coordinates_euclideanPoint]
      have he := Complex.ofRealCLM.integral_comp_comm hi
      simpa only [Complex.ofRealCLM_apply, Function.comp_def, Complex.real_smul, Complex.ofReal_mul] using!
        congrArg (fun c : ℂ => ((1 - t) ^ 3)⁻¹ • c) he

end FreudenthalSVLean.BogovskiiPressureMixture
