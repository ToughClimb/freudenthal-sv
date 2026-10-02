import FreudenthalSVLean.BogovskiiRayRescaling
import FreudenthalSVLean.WeightedIntegralSquare
import FreudenthalSVLean.EuclideanCoordinateTransport

/-!
# The actual lower-half Fourier kernel

For the continuous lifting in manuscript Lemma `means`, this is the
genuine Fourier kernel in Durán, arXiv:1103.3718, Section 2. Its norm is
the proved nonnegative ray weight times the rescaled input transform.
Weighted Cauchy--Schwarz bounds each actual truncated integral by that
weight's true mass. This module proves a pointwise-frequency estimate;
the spatial Fourier identity and global L2 estimate are separate steps.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set
open FreudenthalSVLean.FourierDirectionalDecay
open FreudenthalSVLean.FourierRayBound
open FreudenthalSVLean.BogovskiiRayRescaling
open FreudenthalSVLean.WeightedIntegralSquare
open FreudenthalSVLean.EuclideanCoordinateTransport

noncomputable section

namespace FreudenthalSVLean.SmallScaleFourierKernel

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def FourierKernel (φ f : 𝓢(E, ℂ)) (m ξ : E) (t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ m : ℝ) *
    𝓕 φ (t • ξ) * 𝓕 f ((1 - t) • ξ)

def energyDensity (φ f : 𝓢(E, ℂ)) (m ξ : E) (t : ℝ) : ℝ :=
  weightedFourierRay φ ξ m t * ‖𝓕 f ((1 - t) • ξ)‖ ^ 2

def lowerHalf (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m ξ : E) : ℂ :=
  ∫ t in Icc ε (1 / 2 : ℝ), FourierKernel φ f m ξ t

theorem FourierKernel_continuous (φ f : 𝓢(E, ℂ)) (m ξ : E) :
    Continuous (FourierKernel φ f m ξ) := by
  unfold FourierKernel
  fun_prop

theorem FourierKernel_norm (φ f : 𝓢(E, ℂ)) (m ξ : E) (t : ℝ) :
    ‖FourierKernel φ f m ξ t‖ =
      weightedFourierRay φ ξ m t * ‖𝓕 f ((1 - t) • ξ)‖ := by
  have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
  rw [FourierKernel, norm_mul, norm_mul, norm_mul, hc]
  simp only [Complex.norm_real, Real.norm_eq_abs, weightedFourierRay, frequency]

theorem energyDensity_nonneg (φ f : 𝓢(E, ℂ)) (m ξ : E) (t : ℝ) :
    0 ≤ energyDensity φ f m ξ t :=
  mul_nonneg (weightedFourierRay_nonneg φ ξ m t) (sq_nonneg _)

theorem energyDensity_continuous (φ f : 𝓢(E, ℂ)) (m ξ : E) :
    Continuous (energyDensity φ f m ξ) := by
  unfold energyDensity
  exact (weightedFourierRay_continuous φ ξ m).mul
    ((((𝓕 f).continuous.comp ((continuous_const.sub continuous_id).smul
      continuous_const)).norm).pow 2)

theorem lowerHalf_pointwise_bound (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m ξ : E) :
    ‖lowerHalf ε φ f m ξ‖ ^ 2 ≤ (Real.pi * decayConstant φ m) *
      ∫ t in Icc ε (1 / 2 : ℝ), energyDensity φ f m ξ t := by
  have hg : Continuous (fun t : ℝ => ‖𝓕 f ((1 - t) • ξ)‖) := by fun_prop
  have hw := weightedFourierRay_continuous φ ξ m
  have h1 := (hw.mul hg).integrableOn_Icc (μ := (volume : Measure ℝ))
    (a := ε) (b := (1 / 2 : ℝ))
  have h2 := (hw.mul (hg.pow 2)).integrableOn_Icc (μ := (volume : Measure ℝ))
    (a := ε) (b := (1 / 2 : ℝ))
  have hn : 0 ≤ ∫ t in Icc ε (1 / 2 : ℝ),
      weightedFourierRay φ ξ m t * ‖𝓕 f ((1 - t) • ξ)‖ :=
    integral_nonneg (fun t => mul_nonneg (weightedFourierRay_nonneg φ ξ m t) (norm_nonneg _))
  have hnorm : ‖lowerHalf ε φ f m ξ‖ ≤ ∫ t in Icc ε (1 / 2 : ℝ),
      weightedFourierRay φ ξ m t * ‖𝓕 f ((1 - t) • ξ)‖ := by
    exact (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (Filter.Eventually.of_forall (FourierKernel_norm φ f m ξ)))
  calc
    _ ≤ (∫ t in Icc ε (1 / 2 : ℝ),
        weightedFourierRay φ ξ m t * ‖𝓕 f ((1 - t) • ξ)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hn).mpr hnorm
    _ ≤ (∫ t in Icc ε (1 / 2 : ℝ), weightedFourierRay φ ξ m t) *
        ∫ t in Icc ε (1 / 2 : ℝ), energyDensity φ f m ξ t :=
      weighted_integral_square hw.integrableOn_Icc h1 h2
        (Filter.Eventually.of_forall (weightedFourierRay_nonneg φ ξ m))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (weightedFourierRay_setIntegral_bound φ ξ m (Icc ε (1 / 2 : ℝ)))
      (integral_nonneg (energyDensity_nonneg φ f m ξ))

end FreudenthalSVLean.SmallScaleFourierKernel
