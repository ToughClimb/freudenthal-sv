import FreudenthalSVLean.SpatialUpperHalfL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform genuine scalar-mixture derivative estimate

For the continuous lift in manuscript Lemma `means`, the actual
directional time integral on epsilon<=t<=1 splits at 1/2 into the
proved small-scale Fourier estimate and the direct large-scale bound.
All integrals, support properties and square integrability are genuine.
The resulting scalar L2 constant is fixed by the kernel and direction
and precedes the positive truncation and the input pressure.
-/

open scoped SchwartzMap Real LineDeriv
open MeasureTheory Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.BogovskiiMixtureFourier
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.CompactFourierIntegration
open FreudenthalSVLean.SpatialLowerHalfL2
open FreudenthalSVLean.SpatialUpperHalfL2
open FreudenthalSVLean.FourierDirectionalDecay

noncomputable section

namespace FreudenthalSVLean.ScalarMixtureEstimate

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def scalarDerivativeConstant (φ : 𝓢(E, ℂ)) (m : E) : ℝ :=
  8 * (Real.pi * decayConstant φ m) ^ 2 + 512 * derivativeBound φ m ^ 2

theorem scalarDerivativeConstant_nonneg (φ : 𝓢(E, ℂ)) (m : E) :
    0 ≤ scalarDerivativeConstant φ m := by unfold scalarDerivativeConstant; positivity

def scalarDerivativeIntegral (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m : E) : E → ℂ :=
  timeIntegral (Icc ε (1 : ℝ)) (clippedDerivativeMixture ε φ f m)

theorem scalarDerivativeIntegral_split {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (φ f : 𝓢(E, ℂ)) (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m x : E) :
    scalarDerivativeIntegral ε φ f m x =
      spatialLowerHalf ε φ f m x + spatialUpperHalf φ f m x := by
  have hc : Continuous (fun t : ℝ => clippedDerivativeMixture ε φ f m t x) :=
    (clippedDerivativeMixture_continuous hε φ f m).comp
      (continuous_id.prodMk continuous_const)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := (volume : Measure ℝ)) ε (1 / 2))
    (hc.intervalIntegrable (μ := (volume : Measure ℝ)) (1 / 2) 1)
  rw [intervalIntegral.integral_of_le hεh,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by linarith : ε ≤ 1)] at hsplit
  simp_rw [← integral_Icc_eq_integral_Ioc] at hsplit
  have hu : (∫ t in Icc (1 / 2 : ℝ) 1, clippedDerivativeMixture ε φ f m t x) =
      spatialUpperHalf φ f m x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc (1 / 2 : ℝ) 1))] with t ht
    rw [clippedDerivativeMixture_eq (hεh.trans ht.1) φ f hf m x,
      clippedDerivativeMixture_eq ht.1 φ f hf m x]
  exact hsplit.symm.trans (congrArg (fun z : ℂ => spatialLowerHalf ε φ f m x + z) hu)

theorem scalarDerivativeIntegral_zero {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E)
    {x : E} (hx : x ∉ cubeE) : scalarDerivativeIntegral ε φ f m x = 0 := by
  apply timeIntegral_zero isCompact_Icc _ hx
  intro t ht x hx
  rw [clippedDerivativeMixture_eq ht.1 φ f hf m x, derivativeMixture,
    spatialMixture_zero (hε.trans_le ht.1) ht.2
      (fun z hz => Function.notMem_support.mp (fun h => hz (schwartz_derivative_support hφ m h)))
      (fun y hy => Function.notMem_support.mp (fun h => hy (hf h))) hx, smul_zero]

theorem scalarDerivativeIntegral_memLp {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E) :
    MemLp (scalarDerivativeIntegral ε φ f m) 2 volume := by
  apply timeIntegral_memLp_two isCompact_Icc cubeE_compact
    (clippedDerivativeMixture_continuous hε φ f m)
  intro t ht x hx
  rw [clippedDerivativeMixture_eq ht.1 φ f hf m x, derivativeMixture,
    spatialMixture_zero (hε.trans_le ht.1) ht.2
      (fun z hz => Function.notMem_support.mp (fun h => hz (schwartz_derivative_support hφ m h)))
      (fun y hy => Function.notMem_support.mp (fun h => hy (hf h))) hx, smul_zero]

theorem scalarDerivativeIntegral_L2_bound {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (φ f : 𝓢(E, ℂ)) (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E) :
    (∫ x : E, ‖scalarDerivativeIntegral ε φ f m x‖ ^ 2) ≤
      scalarDerivativeConstant φ m * ∫ y : E, ‖f y‖ ^ 2 := by
  have hl : MemLp (spatialLowerHalf ε φ f m) 2 volume :=
    timeIntegral_memLp_two isCompact_Icc cubeE_compact
      (clippedDerivativeMixture_continuous hε φ f m)
      (fun t ht x hx => clippedDerivativeMixture_zero hε φ f hφ hf m ht hx)
  have hu : MemLp (spatialUpperHalf φ f m) 2 volume :=
    (spatialUpperHalf_continuous φ f m).memLp_of_hasCompactSupport
      (spatialUpperHalf_compact φ f hφ hf m)
  have hil := (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl
  have hiu := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hi := scalarDerivativeIntegral_memLp hε φ f hφ hf m
  have hii := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  calc
    _ ≤ ∫ x : E, 2 * ‖spatialLowerHalf ε φ f m x‖ ^ 2 +
        2 * ‖spatialUpperHalf φ f m x‖ ^ 2 := by
      apply integral_mono hii ((hil.const_mul 2).add (hiu.const_mul 2))
      intro x
      change ‖scalarDerivativeIntegral ε φ f m x‖ ^ 2 ≤
        2 * ‖spatialLowerHalf ε φ f m x‖ ^ 2 + 2 * ‖spatialUpperHalf φ f m x‖ ^ 2
      rw [scalarDerivativeIntegral_split hε hεh φ f hf m x]
      have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (norm_add_le (spatialLowerHalf ε φ f m x) (spatialUpperHalf φ f m x))
      nlinarith [sq_nonneg (‖spatialLowerHalf ε φ f m x‖ - ‖spatialUpperHalf φ f m x‖)]
    _ = 2 * (∫ x : E, ‖spatialLowerHalf ε φ f m x‖ ^ 2) +
        2 * (∫ x : E, ‖spatialUpperHalf φ f m x‖ ^ 2) := by
      rw [integral_add (hil.const_mul 2) (hiu.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have hlow := spatialLowerHalf_L2_bound hε φ f hφ hf m
      have hupp := spatialUpperHalf_L2_bound φ f hφ hf m
      unfold scalarDerivativeConstant
      nlinarith

end FreudenthalSVLean.ScalarMixtureEstimate
