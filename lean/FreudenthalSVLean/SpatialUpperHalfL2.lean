import FreudenthalSVLean.SpatialLowerHalfL2
import FreudenthalSVLean.CubeSupportedL1L2

/-!
# Genuine spatial upper-half L2 estimate

For the continuous lift in manuscript Lemma `means`, the actual
time-integrated directional mixture on 1/2<=t<=1 is bounded directly
by the kernel derivative's supremum and the input's actual L1 norm.
The unit cube support and genuine L1/L2 inequality give an actual L2
bound independent of every lower truncation, mesh size and pressure.
This is the elementary large-scale part of Durán's Section 2 estimate.
-/

open scoped SchwartzMap Real LineDeriv
open MeasureTheory Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.BogovskiiMixtureFourier
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.CompactFourierIntegration
open FreudenthalSVLean.SpatialLowerHalfL2
open FreudenthalSVLean.CubeSupportedL1L2

noncomputable section

namespace FreudenthalSVLean.SpatialUpperHalfL2

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def derivativeBound (φ : 𝓢(E, ℂ)) (m : E) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (∂_{m} φ)

theorem derivativeBound_nonneg (φ : 𝓢(E, ℂ)) (m : E) : 0 ≤ derivativeBound φ m :=
  (norm_nonneg ((∂_{m} φ : 𝓢(E, ℂ)) 0)).trans (SchwartzMap.norm_le_seminorm ℝ _ _)

theorem derivativeMixture_norm_bound {t : ℝ} (ht : 1 / 2 ≤ t)
    (φ f : 𝓢(E, ℂ)) (m x : E) :
    ‖derivativeMixture t φ f m x‖ ≤
      16 * derivativeBound φ m * ∫ y : E, ‖f y‖ := by
  have ht0 : 0 < t := by linarith
  have hp : 1 / 16 ≤ t ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ht 4
    norm_num at h
    exact h
  have hi : (t ^ 4)⁻¹ ≤ 16 := by
    have h := (inv_le_inv₀ (pow_pos ht0 4) (by norm_num : (0 : ℝ) < 1 / 16)).mpr hp
    norm_num at h
    exact h
  rw [derivativeMixture, spatialMixture, ← integral_smul]
  calc
    _ ≤ ∫ y : E, 16 * derivativeBound φ m * ‖f y‖ := by
      apply norm_integral_le_of_norm_le (f.integrable.norm.const_mul _)
      filter_upwards with y
      calc
        _ = (t ^ 4)⁻¹ * ‖(∂_{m} φ : 𝓢(E, ℂ)) (mixtureArgument t x y)‖ * ‖f y‖ := by
          simp only [normalizedDilation, norm_smul, norm_mul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr ht0), abs_of_pos (inv_pos.mpr (pow_pos ht0 3))]
          unfold mixtureArgument
          field_simp
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hi (SchwartzMap.norm_le_seminorm ℝ _ _)
              (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

def spatialUpperHalf (φ f : 𝓢(E, ℂ)) (m : E) : E → ℂ :=
  timeIntegral (Icc (1 / 2 : ℝ) 1) (clippedDerivativeMixture (1 / 2) φ f m)

theorem spatialUpperHalf_zero (φ f : 𝓢(E, ℂ))
    (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E)
    {x : E} (hx : x ∉ cubeE) : spatialUpperHalf φ f m x = 0 := by
  apply timeIntegral_zero isCompact_Icc _ hx
  intro t ht x hx
  rw [clippedDerivativeMixture_eq ht.1 φ f hf m x, derivativeMixture,
    spatialMixture_zero (by linarith [ht.1]) ht.2
      (fun z hz => Function.notMem_support.mp (fun h => hz (schwartz_derivative_support hφ m h)))
      (fun y hy => Function.notMem_support.mp (fun h => hy (hf h))) hx, smul_zero]

theorem spatialUpperHalf_continuous (φ f : 𝓢(E, ℂ)) (m : E) :
    Continuous (spatialUpperHalf φ f m) :=
  timeIntegral_continuous isCompact_Icc
    (clippedDerivativeMixture_continuous (by norm_num) φ f m)

theorem spatialUpperHalf_compact (φ f : 𝓢(E, ℂ))
    (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E) :
    HasCompactSupport (spatialUpperHalf φ f m) := by
  apply cubeE_compact.of_isClosed_subset (isClosed_tsupport (spatialUpperHalf φ f m))
  apply closure_minimal _ cubeE_closed
  intro x hx
  by_contra hn
  exact hx (spatialUpperHalf_zero φ f hφ hf m hn)

theorem spatialUpperHalf_norm_bound (φ f : 𝓢(E, ℂ))
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m x : E) :
    ‖spatialUpperHalf φ f m x‖ ≤ 16 * derivativeBound φ m * ∫ y : E, ‖f y‖ := by
  have hC : 0 ≤ 16 * derivativeBound φ m * ∫ y : E, ‖f y‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (derivativeBound_nonneg φ m))
      (integral_nonneg (fun _ => norm_nonneg _))
  calc
    _ ≤ ∫ t in Icc (1 / 2 : ℝ) 1, 16 * derivativeBound φ m * ∫ y : E, ‖f y‖ := by
      apply norm_integral_le_of_norm_le (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc (1 / 2 : ℝ) 1))] with t ht
      rw [clippedDerivativeMixture_eq ht.1 φ f hf m x]
      exact derivativeMixture_norm_bound ht.1 φ f m x
    _ ≤ _ := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
      nlinarith

theorem spatialUpperHalf_L2_bound (φ f : 𝓢(E, ℂ))
    (hφ : Function.support (φ : E → ℂ) ⊆ cubeE)
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) (m : E) :
    (∫ x : E, ‖spatialUpperHalf φ f m x‖ ^ 2) ≤
      256 * derivativeBound φ m ^ 2 * ∫ y : E, ‖f y‖ ^ 2 := by
  have hn : 0 ≤ ∫ y : E, ‖f y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hC := derivativeBound_nonneg φ m
  calc
    _ ≤ (16 * derivativeBound φ m * ∫ y : E, ‖f y‖) ^ 2 :=
      cube_norm_square_le_constant (spatialUpperHalf_continuous φ f m)
        (fun x hx => spatialUpperHalf_zero φ f hφ hf m hx) (by positivity)
        (spatialUpperHalf_norm_bound φ f hf m)
    _ = 256 * derivativeBound φ m ^ 2 * (∫ y : E, ‖f y‖) ^ 2 := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (cube_l1_square_le_l2 f hf) (by positivity)

end FreudenthalSVLean.SpatialUpperHalfL2
