import FreudenthalSVLean.BogovskiiHilbertConvergence
import FreudenthalSVLean.SmoothCubePressureDensity
import FreudenthalSVLean.UniformApproximationSurjectivity

/-!
# Actual cube-divergence surjectivity

For the continuous lifting in manuscript Lemma `means`, every genuine
mean-zero cube L2 pressure has an approximate preimage with relative error
at most one half and a single uniform norm bound. The proof first uses
the proved density of actual smooth pressures, then their uniformly
bounded genuine Bogovskii truncations and actual divergence convergence.
The checked geometric-series argument converts these uniformly bounded
approximate preimages to exact preimages in the complete H1_0 Hilbert
space. Density alone is not used to infer surjectivity.
-/

open scoped Topology
open Filter
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.SmoothCubePressureSpace
open FreudenthalSVLean.SmoothCubePressureDensity
open FreudenthalSVLean.HilbertCubeDivergence
open FreudenthalSVLean.BogovskiiHilbertTruncation
open FreudenthalSVLean.BogovskiiHilbertConvergence
open FreudenthalSVLean.UniformApproximationSurjectivity

noncomputable section

namespace FreudenthalSVLean.BogovskiiHilbertSurjectivity

set_option backward.isDefEq.respectTransparency false

theorem divergence_uniform_half_approximation (y : pressureHilbert) :
    ∃ W : VectorHilbert,
      ‖divergenceHilbert W - y‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧
      ‖W‖ ≤ (2 * liftingConstant) * ‖y‖ := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨q, hq⟩ := smoothPressureClass_denseRange.exists_dist_lt y
    (by positivity : 0 < ‖y‖ / 4)
  have hqd : ‖smoothPressureClass q - y‖ < ‖y‖ / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hq
  have he := (tendsto_iff_norm_sub_tendsto_zero.mp (approximatingLift_divergence_tendsto q)).eventually
    (eventually_lt_nhds (by positivity : 0 < ‖y‖ / 4))
  obtain ⟨n, hn⟩ := he.exists
  have hqbound : ‖smoothPressureClass q‖ ≤ 2 * ‖y‖ := by
    have ht := norm_add_le (smoothPressureClass q - y) y
    rw [sub_add_cancel] at ht
    linarith
  refine ⟨approximatingLift q n, ?_, ?_⟩
  · have ht := norm_add_le (divergenceHilbert (approximatingLift q n) - smoothPressureClass q)
      (smoothPressureClass q - y)
    rw [sub_add_sub_cancel] at ht
    linarith
  · calc
      _ ≤ liftingConstant * ‖smoothPressureClass q‖ := approximatingLift_norm_bound q n
      _ ≤ liftingConstant * (2 * ‖y‖) := mul_le_mul_of_nonneg_left hqbound liftingConstant_nonneg
      _ = _ := by ring

theorem divergenceHilbert_surjective : Function.Surjective divergenceHilbert :=
  surjective_of_uniform_half_approximation divergenceHilbert
    (mul_nonneg (by norm_num) liftingConstant_nonneg) divergence_uniform_half_approximation

end FreudenthalSVLean.BogovskiiHilbertSurjectivity
