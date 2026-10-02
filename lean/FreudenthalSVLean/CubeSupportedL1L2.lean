import FreudenthalSVLean.CubeSupportedMixtures
import FreudenthalSVLean.WeightedIntegralSquare

/-!
# Actual L1/L2 estimate on the unit cube

For the continuous lift in manuscript Lemma `means`, an actual
cube-supported Schwartz input satisfies (integral norm f)^2 <= integral
norm f^2. The unit cube's Euclidean Lebesgue volume is genuinely one,
and the bound follows from the proved weighted variance inequality.
-/

open scoped SchwartzMap
open MeasureTheory Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.WeightedIntegralSquare

noncomputable section

namespace FreudenthalSVLean.CubeSupportedL1L2

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

theorem cube_norm_square_le_constant {v : E → ℂ} (hv : Continuous v)
    (hs : ∀ x ∉ cubeE, v x = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖v x‖ ≤ C) :
    (∫ x : E, ‖v x‖ ^ 2) ≤ C ^ 2 := by
  have hc : HasCompactSupport v := by
    apply cubeE_compact.of_isClosed_subset (isClosed_tsupport v)
    apply closure_minimal _ cubeE_closed
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  have hm : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hc
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  calc
    _ = ∫ x in cubeE, ‖v x‖ ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hs x hx, norm_zero, zero_pow (by decide)])).symm
    _ ≤ ∫ _x in cubeE, C ^ 2 := by
      apply integral_mono hi.integrableOn (integrableOn_const cubeE_compact.measure_ne_top)
      intro x
      exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb x)
    _ = _ := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ,
        cubeE_volume, ENNReal.toReal_one, smul_eq_mul, one_mul]

theorem cube_l1_square_le_l2 (f : 𝓢(E, ℂ))
    (hf : Function.support (f : E → ℂ) ⊆ cubeE) :
    (∫ x : E, ‖f x‖) ^ 2 ≤ ∫ x : E, ‖f x‖ ^ 2 := by
  have h2 : Integrable (fun x : E => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (f.memLp 2)
  have he := weighted_integral_square (μ := (volume : Measure E).restrict cubeE)
    (w := fun _ => (1 : ℝ)) (g := fun x => ‖f x‖)
    (integrableOn_const cubeE_compact.measure_ne_top)
    (by simpa only [one_mul, IntegrableOn] using! f.integrable.norm.integrableOn)
    (by simpa only [one_mul, IntegrableOn] using! h2.integrableOn)
    (Eventually.of_forall (fun _ => zero_le_one))
  have hn : (∫ x in cubeE, ‖f x‖) = ∫ x : E, ‖f x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [Function.notMem_support.mp (fun h => hx (hf h)), norm_zero])
  have hn2 : (∫ x in cubeE, ‖f x‖ ^ 2) = ∫ x : E, ‖f x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [Function.notMem_support.mp (fun h => hx (hf h)), norm_zero, zero_pow (by decide)])
  simpa only [one_mul, integral_const, measureReal_def, Measure.restrict_apply_univ,
    cubeE_volume, ENNReal.toReal_one, smul_eq_mul, one_mul, hn, hn2] using he

end FreudenthalSVLean.CubeSupportedL1L2
