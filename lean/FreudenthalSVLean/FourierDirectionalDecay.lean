import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Actual directional Fourier decay for the cube divergence inverse

For the continuous Bogovskii step in manuscript Lemma `means`, two
genuine directional derivatives give a quadratic Fourier decay bound.
It follows from Mathlib's proved Schwartz differentiation identities
and actual L1 norms; no singular-integral boundedness is assumed.
This is the elementary Fourier ingredient of the L2 argument in Durán,
arXiv:1103.3718, Section 2, expressed for any Euclidean direction.
-/

open scoped SchwartzMap Real LineDeriv
open MeasureTheory FourierTransform

noncomputable section

namespace FreudenthalSVLean.FourierDirectionalDecay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency false

def frequency (ξ m : E) : ℝ := 2 * Real.pi * |inner ℝ ξ m|

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem frequency_nonneg (ξ m : E) : 0 ≤ frequency ξ m := by
  unfold frequency
  positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem frequency_smul (t : ℝ) (ξ m : E) :
    frequency (t • ξ) m = |t| * frequency ξ m := by
  simp only [frequency, real_inner_smul_left, abs_mul]
  ring

theorem first_fourier_norm (φ : 𝓢(E, ℂ)) (ξ m : E) :
    ‖𝓕 (∂_{m} φ) ξ‖ = frequency ξ m * ‖𝓕 φ ξ‖ := by
  have hg : (fun x : E => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have he := congrArg (fun f : 𝓢(E, ℂ) => f ξ) (SchwartzMap.fourier_lineDerivOp_eq φ m)
  have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg] at he
  rw [he, norm_smul, norm_smul, hc, Real.norm_eq_abs]
  unfold frequency
  ring

theorem second_fourier_norm (φ : 𝓢(E, ℂ)) (ξ m : E) :
    ‖𝓕 (∂_{m} (∂_{m} φ)) ξ‖ = frequency ξ m ^ 2 * ‖𝓕 φ ξ‖ := by
  rw [first_fourier_norm, first_fourier_norm]
  ring

def decayConstant (φ : 𝓢(E, ℂ)) (m : E) : ℝ :=
  ‖φ.toLp 1‖ + ‖(∂_{m} (∂_{m} φ)).toLp 1‖

theorem decayConstant_nonneg (φ : 𝓢(E, ℂ)) (m : E) : 0 ≤ decayConstant φ m :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem quadratic_fourier_decay (φ : 𝓢(E, ℂ)) (ξ m : E) :
    (1 + frequency ξ m ^ 2) * ‖𝓕 φ ξ‖ ≤ decayConstant φ m := by
  have h0 := SchwartzMap.norm_fourier_apply_le_toLp_one φ ξ
  have h2 := SchwartzMap.norm_fourier_apply_le_toLp_one (∂_{m} (∂_{m} φ)) ξ
  rw [second_fourier_norm] at h2
  unfold decayConstant
  nlinarith

theorem ray_pointwise_bound (φ : 𝓢(E, ℂ)) (ξ m : E) (t : ℝ) :
    frequency ξ m * ‖𝓕 φ (t • ξ)‖ ≤
      decayConstant φ m * (frequency ξ m * (1 + (frequency ξ m * t) ^ 2)⁻¹) := by
  have hd := quadratic_fourier_decay φ (t • ξ) m
  rw [frequency_smul] at hd
  have he : (|t| * frequency ξ m) ^ 2 = (frequency ξ m * t) ^ 2 := by
    rw [mul_pow, sq_abs]
    ring
  rw [he] at hd
  have hr : ‖𝓕 φ (t • ξ)‖ ≤ decayConstant φ m / (1 + (frequency ξ m * t) ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hr (frequency_nonneg ξ m)
  simpa only [div_eq_mul_inv, mul_left_comm, mul_assoc] using hm

end FreudenthalSVLean.FourierDirectionalDecay
