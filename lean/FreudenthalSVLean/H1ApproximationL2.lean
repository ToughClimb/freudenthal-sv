import FreudenthalSVLean.WeakFaceTrace

/-!
# Actual L2 convergence from the H1 approximation criterion

For the weak-H1 trace and flux step in manuscript Lemma `means`, the
actual squared H1 error implies genuine L2 convergence of both the
function and each weak derivative, on the full space and on every
measurable element region.  Their true squared volume integrals converge
as well.  These statements connect the smooth-closure criterion to L2
limits and do not assume a trace or divergence-inverse theorem.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakFaceTrace

noncomputable section

namespace FreudenthalSVLean.H1ApproximationL2

set_option backward.isDefEq.respectTransparency false

theorem toLp_tendsto_of_square_error {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → α → ℝ} {f : α → ℝ} (hu : ∀ n, MemLp (u n) 2 μ) (hf : MemLp f 2 μ)
    (he : Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)) := by
  have hnorm (n : ℕ) : ‖(hu n).toLp (u n) - hf.toLp f‖ ^ 2 =
      ∫ x, (u n x - f x) ^ 2 ∂μ := by
    rw [← (hu n).toLp_sub hf]
    simpa only [Pi.sub_apply] using toLp_norm_square ((hu n).sub hf)
  have hs : Tendsto (fun n => ‖(hu n).toLp (u n) - hf.toLp f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

theorem square_error_restrict_tendsto {u : ℕ → Space → ℝ} {f : Space → ℝ}
    (hu : ∀ n, MemLp (u n) 2 volume) (hf : MemLp f 2 volume)
    (he : Tendsto (fun n => ∫ x, (u n x - f x) ^ 2) atTop (𝓝 0)) (S : Set Space) :
    Tendsto (fun n => ∫ x in S, (u n x - f x) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) _ he
  intro n
  simpa only [Pi.sub_apply] using!
    setIntegral_le_integral ((hu n).sub hf).integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _))

theorem smooth_value_error_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) :
    Tendsto (fun n => ∫ x, (u n x - f x) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) _ hu.convergence
  intro n
  unfold h1Error
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem smooth_gradient_error_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (j : Fin 3) :
    Tendsto (fun n => ∫ x, (fderiv ℝ (u n) x (Pi.single j 1) - g j x) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) _ hu.convergence
  intro n
  have hj := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin 3 => ∫ x, (fderiv ℝ (u n) x (Pi.single i 1) - g i x) ^ 2)
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ j)
  exact hj.trans (le_add_of_nonneg_left (integral_nonneg (fun _ => sq_nonneg _)))

theorem smooth_value_L2_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) :
    Tendsto (fun n => (hu.memLp n).toLp (u n)) atTop (𝓝 (hu.weak_gradient.1.toLp f)) :=
  toLp_tendsto_of_square_error hu.memLp hu.weak_gradient.1 (smooth_value_error_tendsto hu)

theorem smooth_gradient_L2_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (j : Fin 3) :
    Tendsto (fun n => (hu.partial_memLp n j).toLp
      (fun x => fderiv ℝ (u n) x (Pi.single j 1))) atTop
        (𝓝 ((hu.weak_gradient.2 j).1.toLp (g j))) :=
  toLp_tendsto_of_square_error (fun n => hu.partial_memLp n j) (hu.weak_gradient.2 j).1
    (smooth_gradient_error_tendsto hu j)

theorem smooth_value_local_L2_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (S : Set Space) :
    Tendsto (fun n => ((hu.memLp n).restrict S).toLp (u n)) atTop
      (𝓝 ((hu.weak_gradient.1.restrict S).toLp f)) :=
  toLp_tendsto_of_square_error (fun n => (hu.memLp n).restrict S) (hu.weak_gradient.1.restrict S)
    (square_error_restrict_tendsto hu.memLp hu.weak_gradient.1 (smooth_value_error_tendsto hu) S)

theorem smooth_gradient_local_L2_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (S : Set Space) (j : Fin 3) :
    Tendsto (fun n => ((hu.partial_memLp n j).restrict S).toLp
      (fun x => fderiv ℝ (u n) x (Pi.single j 1))) atTop
        (𝓝 (((hu.weak_gradient.2 j).1.restrict S).toLp (g j))) :=
  toLp_tendsto_of_square_error (fun n => (hu.partial_memLp n j).restrict S)
    ((hu.weak_gradient.2 j).1.restrict S)
    (square_error_restrict_tendsto (fun n => hu.partial_memLp n j) (hu.weak_gradient.2 j).1
      (smooth_gradient_error_tendsto hu j) S)

theorem smooth_value_local_square_integral_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (S : Set Space) :
    Tendsto (fun n => ∫ x in S, (u n x) ^ 2) atTop (𝓝 (∫ x in S, (f x) ^ 2)) := by
  simpa only [toLp_norm_square] using (smooth_value_local_L2_tendsto hu S).norm.pow 2

theorem smooth_gradient_local_square_integral_tendsto {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} {u : ℕ → Space → ℝ}
    (hu : SmoothH1Approximation f g u) (S : Set Space) (j : Fin 3) :
    Tendsto (fun n => ∫ x in S, (fderiv ℝ (u n) x (Pi.single j 1)) ^ 2) atTop
      (𝓝 (∫ x in S, (g j x) ^ 2)) := by
  simpa only [toLp_norm_square] using (smooth_gradient_local_L2_tendsto hu S j).norm.pow 2

end FreudenthalSVLean.H1ApproximationL2
