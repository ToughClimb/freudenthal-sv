import FreudenthalSVLean.InteriorMollification

/-!
# L2 convergence of smooth interior-supported approximations

For the manuscript's H1_0 interface, the smooth convolution/compression
sequence converges in genuine squared L2 error for every bounded cube-
supported locally integrable function continuous almost everywhere.  A
scalar factor tending to one and bounded by five is allowed, as required
by the genuine gradient chain rule.  Support lies in the fixed closed
cube and the error is bounded by 36 M^2 there, giving a proved dominated-
convergence argument for both values and weak-gradient components.
-/

open scoped ContDiff Topology
open Set Filter MeasureTheory Metric
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.WeakGradientMollification
open FreudenthalSVLean.MollificationL2
open FreudenthalSVLean.InteriorMollification

noncomputable section

namespace FreudenthalSVLean.InteriorMollificationL2

set_option backward.isDefEq.respectTransparency false

theorem interiorMollify_norm_le {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M) (n : ℕ) (x : Space) :
    ‖interiorMollify n f x‖ ≤ M := mollify_norm_le _ hf hM hb _

theorem interiorMollify_zero_off_cube {f : Space → ℝ}
    (hs : Function.support f ⊆ cube) (n : ℕ) (x : Space) (hx : x ∉ cube) :
    interiorMollify n f x = 0 := by
  apply Function.notMem_support.mp
  exact fun hh => hx (openCube_subset_cube
    (innerBox_subset_openCube n (interiorMollify_support_box n hs hh)))

theorem interior_scaled_square_error_tendsto {f : Space → ℝ}
    (hf : LocallyIntegrable f volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (hs : Function.support f ⊆ cube)
    (hc : ∀ᵐ x : Space ∂volume, ContinuousAt f x) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 1)) (ha' : ∀ n, 0 ≤ a n ∧ a n ≤ 5) :
    Tendsto (fun n => ∫ x, (a n * interiorMollify n f x - f x) ^ 2) atTop (𝓝 0) := by
  classical
  let bound : Space → ℝ := cube.indicator (fun _ => 36 * M ^ 2)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => (a n * interiorMollify n f x - f x) ^ 2) volume :=
    (((interiorMollify_contDiff n hf).continuous.aestronglyMeasurable.const_mul (a n)).sub
      hf.aestronglyMeasurable).pow 2
  have hi : Integrable bound volume := by
    apply (integrable_indicator_iff (isClosed_Icc : IsClosed cube).measurableSet).mpr
    exact integrableOn_const (isCompact_Icc : IsCompact cube).measure_ne_top
  have hbound (n : ℕ) : ∀ᵐ x : Space ∂volume,
      ‖(a n * interiorMollify n f x - f x) ^ 2‖ ≤ bound x := by
    filter_upwards with x
    by_cases hx : x ∈ cube
    · rw [show bound x = 36 * M ^ 2 from indicator_of_mem hx _]
      have hn : ‖a n * interiorMollify n f x‖ ≤ 5 * M := by
        rw [norm_mul, Real.norm_of_nonneg (ha' n).1]
        exact mul_le_mul (ha' n).2 (interiorMollify_norm_le hf.aestronglyMeasurable hM hb n x)
          (norm_nonneg _) (by norm_num)
      have hs' := (norm_sub_le (a n * interiorMollify n f x) (f x)).trans (add_le_add hn (hb x))
      rw [norm_pow]
      nlinarith [norm_nonneg (a n * interiorMollify n f x - f x)]
    · have hf0 : f x = 0 := Function.notMem_support.mp (fun hh => hx (hs hh))
      simp only [interiorMollify_zero_off_cube hs n x hx, hf0, mul_zero, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
  have hconv : ∀ᵐ x : Space ∂volume,
      Tendsto (fun n => (a n * interiorMollify n f x - f x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hc] with x hx
    simpa only [one_mul, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      ((ha.mul (interiorMollify_tendsto hf.aestronglyMeasurable x hx)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))).pow 2
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence bound hm hi hbound hconv

theorem interiorMollify_square_error_tendsto {f : Space → ℝ}
    (hf : LocallyIntegrable f volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (hs : Function.support f ⊆ cube)
    (hc : ∀ᵐ x : Space ∂volume, ContinuousAt f x) :
    Tendsto (fun n => ∫ x, (interiorMollify n f x - f x) ^ 2) atTop (𝓝 0) := by
  simpa only [one_mul] using interior_scaled_square_error_tendsto hf hM hb hs hc
    (fun _ => 1) tendsto_const_nhds (fun _ => by constructor <;> norm_num)

theorem interior_scaled_square_integral_tendsto {f : Space → ℝ}
    (hf : LocallyIntegrable f volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (hs : Function.support f ⊆ cube)
    (hc : ∀ᵐ x : Space ∂volume, ContinuousAt f x) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 1)) (ha' : ∀ n, 0 ≤ a n ∧ a n ≤ 5) :
    Tendsto (fun n => ∫ x, (a n * interiorMollify n f x) ^ 2) atTop (𝓝 (∫ x, (f x) ^ 2)) := by
  classical
  let bound : Space → ℝ := cube.indicator (fun _ => 25 * M ^ 2)
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    exact ((interiorMollify_contDiff n hf).continuous.aestronglyMeasurable.const_mul (a n)).pow 2
  · apply (integrable_indicator_iff (isClosed_Icc : IsClosed cube).measurableSet).mpr
    exact integrableOn_const (isCompact_Icc : IsCompact cube).measure_ne_top
  · intro n
    filter_upwards with x
    by_cases hx : x ∈ cube
    · rw [show bound x = 25 * M ^ 2 from indicator_of_mem hx _]
      have hn : ‖a n * interiorMollify n f x‖ ≤ 5 * M := by
        rw [norm_mul, Real.norm_of_nonneg (ha' n).1]
        exact mul_le_mul (ha' n).2 (interiorMollify_norm_le hf.aestronglyMeasurable hM hb n x)
          (norm_nonneg _) (by norm_num)
      rw [norm_pow]
      nlinarith [norm_nonneg (a n * interiorMollify n f x)]
    · simp only [interiorMollify_zero_off_cube hs n x hx, mul_zero,
        zero_pow (by norm_num : 2 ≠ 0), norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
  · filter_upwards [hc] with x hx
    simpa only [one_mul] using (ha.mul (interiorMollify_tendsto hf.aestronglyMeasurable x hx)).pow 2

end FreudenthalSVLean.InteriorMollificationL2
