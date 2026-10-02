import FreudenthalSVLean.BoxH1Estimate
import FreudenthalSVLean.H1ApproximationL2

/-!
# Local mean estimates for actual weak H1 functions

For the local interpolation estimate in manuscript Lemma `means` and
equation `SZ`, the smooth Cartesian-box Poincare inequality passes to
genuine weak H1 data by strong L2 convergence.  The actual volume average
is a proved continuous L2 functional, and subtraction of its constant
representative is continuous on every finite-measure local region.  The
weak derivatives in the conclusion are the genuine test-function weak
derivatives supplied by `SmoothH1Approximation`, not formal coefficients.
No stable finite-element interpolant or continuous divergence inverse is
assumed by this module.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakFaceGauss
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.BoxH1Estimate

noncomputable section

namespace FreudenthalSVLean.WeakBoxH1Estimate

set_option backward.isDefEq.respectTransparency false

theorem centered_square_integral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (hμ : μ univ ≠ ⊤) {u : ℕ → α → ℝ} {f : α → ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hf : MemLp f 2 μ)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f))) (c : ℝ) :
    Tendsto (fun n => ∫ x, (u n x - c * ∫ y, u n y ∂μ) ^ 2 ∂μ) atTop
      (𝓝 (∫ x, (f x - c * ∫ y, f y ∂μ) ^ 2 ∂μ)) := by
  let : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμ⟩
  let one : Lp ℝ 2 μ := (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ => 1)
  have hc (d : ℝ) : (memLp_const (μ := μ) (p := 2) d).toLp (fun _ => d) = d • one := by
    have he : d • (fun _ : α => (1 : ℝ)) = fun _ : α => d := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    simpa only [one, he] using!
      MemLp.toLp_const_smul d (memLp_const (μ := μ) (p := 2) (1 : ℝ))
  have hn {v : α → ℝ} (hv : MemLp v 2 μ) (d : ℝ) :
      ‖hv.toLp v - d • one‖ ^ 2 = ∫ x, (v x - d) ^ 2 ∂μ := by
    rw [← hc d, ← hv.toLp_sub (memLp_const d)]
    simpa only [Pi.sub_apply] using! toLp_norm_square (hv.sub (memLp_const d))
  have hi : Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    simpa only [Function.comp_def, l2Integral_toLp] using
      ((l2Integral μ hμ).continuous.tendsto (hf.toLp f)).comp ht
  have hs := ht.sub ((hi.const_mul c).smul (tendsto_const_nhds (x := one)))
  simpa only [hn] using hs.norm.pow 2

theorem box_mean_error_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (a b : ℝ) :
    Tendsto (fun n => ∫ x in boxSet a b, (u n x - boxMean a b (u n)) ^ 2) atTop
      (𝓝 (∫ x in boxSet a b, (f x - boxMean a b f) ^ 2)) := by
  have hμ : (volume.restrict (boxSet a b)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_Icc : IsCompact (boxSet a b)).measure_ne_top
  exact centered_square_integral_tendsto hμ
    (fun n => (hu.memLp n).restrict (boxSet a b)) (hu.weak_gradient.1.restrict (boxSet a b))
    (smooth_value_local_L2_tendsto hu (boxSet a b)) (((b - a)⁻¹) ^ 3)

theorem weak_box_mean_poincare {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u) {a b : ℝ} (hab : a < b) :
    (∫ x in boxSet a b, (f x - boxMean a b f) ^ 2) ≤
      3 * (b - a) ^ 2 * ∑ j : Fin 3, ∫ x in boxSet a b, (g j x) ^ 2 := by
  obtain ⟨u, hu⟩ := hf
  have hl := box_mean_error_tendsto hu a b
  have hr := (tendsto_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j _ => smooth_gradient_local_square_integral_tendsto hu (boxSet a b) j)).const_mul
      (3 * (b - a) ^ 2)
  exact le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n => box_mean_poincare hab (hu.smooth n)))

end FreudenthalSVLean.WeakBoxH1Estimate
