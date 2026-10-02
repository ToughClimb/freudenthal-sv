import FreudenthalSVLean.WeakGradientMollification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine L2 approximation by smooth normalized convolution

For the manuscript's Sobolev interface, bounded compactly supported
locally integrable functions are approximated in genuine squared L2
error by normalized smooth convolutions.  The proof gives a common
compact support bound and a pointwise norm bound, then combines Mathlib's
proved almost-everywhere mollifier convergence with dominated convergence.
The later H1 statement applies the same result to the actual weak
derivatives using the proved convolution derivative formula.
-/

open scoped Convolution ContDiff Pointwise Topology
open Set Filter MeasureTheory ContinuousLinearMap Metric
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakGradientMollification

noncomputable section

namespace FreudenthalSVLean.MollificationL2

set_option backward.isDefEq.respectTransparency false

theorem mollify_norm_le (b : ContDiffBump (0 : Space)) {f : Space → ℝ}
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (x : Space) : ‖mollify b f x‖ ≤ M := by
  rw [mollify_comm]
  simpa only [dist_zero_right] using
    dist_convolution_le (x₀ := x) (z₀ := (0 : ℝ)) hM
      b.support_normed_eq.subset b.nonneg_normed b.integral_normed
      hf (fun y _ => by simpa only [dist_zero_right] using hb y)

theorem mollify_support_ball (b : ContDiffBump (0 : Space)) {f : Space → ℝ} {R : ℝ}
    (hs : Function.support f ⊆ closedBall 0 R) (hb : b.rOut ≤ 1) :
    Function.support (mollify b f) ⊆ closedBall 0 (R + 1) := by
  intro x hx
  have hp := support_convolution_subset (lsmul ℝ ℝ) hx
  rw [b.support_normed_eq] at hp
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_add.mp hp
  rw [mem_closedBall, dist_zero_right]
  have hA : ‖a‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs ha
  have hB : ‖c‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hc : ‖c‖ < b.rOut).le.trans hb
  exact (norm_add_le a c).trans (add_le_add hA hB)

def mollifier (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

theorem mollifier_rOut_le_one (n : ℕ) : (mollifier n).rOut ≤ 1 := by
  change 1 / ((n : ℝ) + 1) ≤ 1
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem mollifier_ratio (n : ℕ) : (mollifier n).rOut ≤ 2 * (mollifier n).rIn := by
  dsimp [mollifier]
  linarith

theorem mollifier_rOut_tendsto : Tendsto (fun n => (mollifier n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem mollify_square_error_tendsto {f : Space → ℝ}
    (hf : LocallyIntegrable f volume) {M R : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) (hs : Function.support f ⊆ closedBall 0 R) :
    Tendsto (fun n => ∫ x, (mollify (mollifier n) f x - f x) ^ 2) atTop (𝓝 0) := by
  classical
  let K : Set Space := closedBall 0 (R + 1)
  let bound : Space → ℝ := K.indicator (fun _ => 4 * M ^ 2)
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    mollifier_rOut_tendsto (Eventually.of_forall mollifier_ratio) hf
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => (mollify (mollifier n) f x - f x) ^ 2) volume :=
    (((mollify_contDiff (mollifier n) hf).continuous.aestronglyMeasurable).sub
      hf.aestronglyMeasurable).pow 2
  have hi : Integrable bound volume := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact integrableOn_const (isCompact_closedBall (0 : Space) (R + 1)).measure_ne_top
  have hbound (n : ℕ) : ∀ᵐ x : Space ∂volume,
      ‖(mollify (mollifier n) f x - f x) ^ 2‖ ≤ bound x := by
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [show bound x = 4 * M ^ 2 from indicator_of_mem hx _]
      have hn := (norm_sub_le (mollify (mollifier n) f x) (f x)).trans
        (add_le_add (mollify_norm_le (mollifier n) hf.aestronglyMeasurable hM hb x) (hb x))
      rw [norm_pow]
      nlinarith [norm_nonneg (mollify (mollifier n) f x - f x)]
    · have hg : mollify (mollifier n) f x = 0 := by
        apply Function.notMem_support.mp
        exact fun hh => hx (mollify_support_ball (mollifier n) hs (mollifier_rOut_le_one n) hh)
      have hxR : x ∉ closedBall 0 R := fun hh => hx (closedBall_subset_closedBall (by linarith) hh)
      have hg' : f x = 0 := Function.notMem_support.mp (fun hh => hxR (hs hh))
      simp only [hg, hg', sub_self, zero_pow (by norm_num : 2 ≠ 0), norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
  have hconv : ∀ᵐ x : Space ∂volume,
      Tendsto (fun n => (mollify (mollifier n) f x - f x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [mollify_comm, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      (hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))).pow 2
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence bound hm hi hbound hconv

end FreudenthalSVLean.MollificationL2
