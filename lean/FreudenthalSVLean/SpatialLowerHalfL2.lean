import FreudenthalSVLean.CubeSupportedMixtures
import FreudenthalSVLean.CompactFourierIntegration
import FreudenthalSVLean.SmallScaleFourierL2
import FreudenthalSVLean.GenuineL1L2Fourier

/-!
# Genuine spatial lower-half L2 estimate

For the continuous lift in manuscript Lemma `means`, the actual
time-integrated spatial directional mixture has exactly the Fourier
transform estimated in `SmallScaleFourierL2`. Genuine cube support and
continuity prove its L1/L2 hypotheses. Compact Fourier Fubini and actual
Plancherel therefore give the uniform bound on the actual spatial
integral, not solely on a separately specified frequency expression.
The scalar mixture is the one in Durán, arXiv:1103.3718, Section 2.
-/

open scoped SchwartzMap Real LineDeriv
open MeasureTheory FourierTransform Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.BogovskiiMixtureFourier
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.CompactFourierIntegration
open FreudenthalSVLean.SmallScaleFourierKernel
open FreudenthalSVLean.SmallScaleFourierL2
open FreudenthalSVLean.GenuineL1L2Fourier
open FreudenthalSVLean.FourierDirectionalDecay

noncomputable section

namespace FreudenthalSVLean.SpatialLowerHalfL2

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def clippedDerivativeMixture (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m : E) (t : ℝ) (x : E) : ℂ :=
  (clippedTime ε t)⁻¹ • clippedMixture ε (∂_{m} φ : 𝓢(E, ℂ)) f (t, x)

def spatialLowerHalf (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m : E) : E → ℂ :=
  timeIntegral (Icc ε (1 / 2 : ℝ)) (clippedDerivativeMixture ε φ f m)

theorem clippedDerivativeMixture_continuous {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (m : E) : Continuous (clippedDerivativeMixture ε φ f m).uncurry :=
  ((continuous_const.max continuous_fst).inv₀
    (fun p : ℝ × E => (clippedTime_pos hε p.1).ne')).smul
      (clippedMixture_continuous hε (∂_{m} φ).continuous f.continuous)

theorem clippedDerivativeMixture_eq {ε t : ℝ} (ht : ε ≤ t)
    (φ f : 𝓢(E, ℂ)) (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m x : E) :
    clippedDerivativeMixture ε φ f m t x = derivativeMixture t φ f m x := by
  rw [clippedDerivativeMixture, clippedTime_eq ht,
    clippedMixture_eq ht (fun y hy => Function.notMem_support.mp (fun h => hy (hf h))) x]
  rfl

theorem clippedDerivativeMixture_zero {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E)
    {t : ℝ} (ht : t ∈ Icc ε (1 / 2 : ℝ)) {x : E} (hx : x ∉ cubeE) :
    clippedDerivativeMixture ε φ f m t x = 0 := by
  rw [clippedDerivativeMixture_eq ht.1 φ f hf m x, derivativeMixture,
    spatialMixture_zero (hε.trans_le ht.1) (by linarith [ht.2])
      (fun z hz => Function.notMem_support.mp (fun h => hz (schwartz_derivative_support hφ m h)))
      (fun y hy => Function.notMem_support.mp (fun h => hy (hf h))) hx, smul_zero]

theorem spatialLowerHalf_fourier {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m ξ : E) :
    𝓕 (spatialLowerHalf ε φ f m) ξ = lowerHalf ε φ f m ξ := by
  rw [spatialLowerHalf, timeIntegral_fourier isCompact_Icc cubeE_compact
    (clippedDerivativeMixture_continuous hε φ f m)
    (fun t ht x hx => clippedDerivativeMixture_zero hε φ f hφ hf m ht hx) ξ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 / 2 : ℝ)))] with t ht
  have he : clippedDerivativeMixture ε φ f m t = derivativeMixture t φ f m :=
    funext (clippedDerivativeMixture_eq ht.1 φ f hf m)
  rw [he, derivativeMixture_fourier (hε.trans_le ht.1) (by linarith [ht.2])]

theorem spatialLowerHalf_L2_bound {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E) :
    (∫ x : E, ‖spatialLowerHalf ε φ f m x‖ ^ 2) ≤
      4 * (Real.pi * decayConstant φ m) ^ 2 * ∫ x : E, ‖f x‖ ^ 2 := by
  have hc := clippedDerivativeMixture_continuous hε φ f m
  have hs : ∀ t ∈ Icc ε (1 / 2 : ℝ), ∀ x ∉ cubeE,
      clippedDerivativeMixture ε φ f m t x = 0 :=
    fun t ht x hx => clippedDerivativeMixture_zero hε φ f hφ hf m ht hx
  have h1 := timeIntegral_integrable isCompact_Icc cubeE_compact hc hs
  have h2 := timeIntegral_memLp_two isCompact_Icc cubeE_compact hc hs
  have he : 𝓕 (spatialLowerHalf ε φ f m) = lowerHalf ε φ f m :=
    funext (spatialLowerHalf_fourier hε φ f hφ hf m)
  have hhat : MemLp (𝓕 (spatialLowerHalf ε φ f m)) 2 volume := by
    rw [he]
    exact lowerHalf_memLp φ f m hε.le
  have hp := actual_plancherel (f := spatialLowerHalf ε φ f m) h1 h2 hhat
  rw [← hp, he]
  exact lowerHalf_L2_bound φ f m hε.le

end FreudenthalSVLean.SpatialLowerHalfL2
