import FreudenthalSVLean.WeakGradientLinearity
import FreudenthalSVLean.WeakFaceTrace

/-!
# Linearity of actual smooth H1 approximation

For the fixed linear weak face-trace interface needed by manuscript
Lemma `means`, functions with genuine weak L2 gradients and genuine
smooth H1 approximation are closed under linear combinations.  Actual
Frechet differentiation supplies the derivative rules, and squared
Lebesgue integral estimates prove convergence; neither a completion
identity nor a stipulated Sobolev vector-space structure is used.
-/

open scoped BigOperators Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakGradientLinearity

noncomputable section

namespace FreudenthalSVLean.H1ApproximationLinearity

set_option backward.isDefEq.respectTransparency false

theorem smooth_partial_add {u v : Space → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (x : Space) (j : Fin 3) :
    fderiv ℝ (fun y => u y + v y) x (Pi.single j 1) =
      fderiv ℝ u x (Pi.single j 1) + fderiv ℝ v x (Pi.single j 1) := by
  have hd : HasFDerivAt (fun y => u y + v y) (fderiv ℝ u x + fderiv ℝ v x) x := by
    simpa only [Pi.add_apply] using!
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.add
        (hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  rfl

theorem smooth_partial_const_mul {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ)
    (x : Space) (j : Fin 3) :
    fderiv ℝ (fun y => c * u y) x (Pi.single j 1) =
      c * fderiv ℝ u x (Pi.single j 1) := by
  have hd : HasFDerivAt (fun y => c * u y) (c • fderiv ℝ u x) x := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.const_smul c
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem integral_square_add_bound {a b : Space → ℝ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) :
    (∫ x, (a x + b x) ^ 2) ≤ 2 * ((∫ x, (a x) ^ 2) + ∫ x, (b x) ^ 2) := by
  have ht := integral_mono (ha.add hb).integrable_sq
    ((ha.integrable_sq.add hb.integrable_sq).const_mul 2)
    (fun x => by
      change (a x + b x) ^ 2 ≤ 2 * ((a x) ^ 2 + (b x) ^ 2)
      nlinarith [sq_nonneg (a x - b x)])
  change (∫ x, (a x + b x) ^ 2) ≤ ∫ x, 2 * ((a x) ^ 2 + (b x) ^ 2) at ht
  rw [integral_const_mul] at ht
  have he : (∫ x, (a x) ^ 2 + (b x) ^ 2) = (∫ x, (a x) ^ 2) + ∫ x, (b x) ^ 2 :=
    integral_add ha.integrable_sq hb.integrable_sq
  rw [he] at ht
  exact ht

theorem h1Error_add_bound {f F : Space → ℝ} {g G : Fin 3 → Space → ℝ}
    {u v : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (hv : SmoothH1Approximation F G v)
    (n : ℕ) :
    h1Error (fun x => f x + F x) (fun j x => g j x + G j x) (fun x => u n x + v n x) ≤
      2 * (h1Error f g (u n) + h1Error F G (v n)) := by
  have hvbound := integral_square_add_bound ((hu.memLp n).sub hu.weak_gradient.1)
    ((hv.memLp n).sub hv.weak_gradient.1)
  have hgbound := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    integral_square_add_bound ((hu.partial_memLp n j).sub (hu.weak_gradient.2 j).1)
      ((hv.partial_memLp n j).sub (hv.weak_gradient.2 j).1))
  simp only [Pi.sub_apply, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hvbound hgbound
  unfold h1Error
  simp only [smooth_partial_add (hu.smooth n) (hv.smooth n), add_sub_add_comm]
  linarith

theorem smoothH1Approximation_add {f F : Space → ℝ} {g G : Fin 3 → Space → ℝ}
    {u v : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (hv : SmoothH1Approximation F G v) :
    SmoothH1Approximation (fun x => f x + F x) (fun j x => g j x + G j x)
      (fun n x => u n x + v n x) := by
  refine ⟨hasL2WeakGradient_add hu.weak_gradient hv.weak_gradient, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa only [Pi.add_apply] using! (hu.smooth n).add (hv.smooth n)
  · intro n
    simpa only [Pi.add_apply] using! (hu.memLp n).add (hv.memLp n)
  · intro n j
    simpa only [smooth_partial_add (hu.smooth n) (hv.smooth n), Pi.add_apply] using!
      (hu.partial_memLp n j).add (hv.partial_memLp n j)
  · exact squeeze_zero (fun _ => h1Error_nonneg _ _ _) (h1Error_add_bound hu hv)
      (by simpa only [zero_add, mul_zero] using ((hu.convergence.add hv.convergence).const_mul 2))

theorem h1Error_const_mul {f : Space → ℝ} {g : Fin 3 → Space → ℝ} {u : Space → ℝ}
    (hu : ContDiff ℝ 1 u) (c : ℝ) :
    h1Error (fun x => c * f x) (fun j x => c * g j x) (fun x => c * u x) = c ^ 2 * h1Error f g u := by
  simp only [h1Error, smooth_partial_const_mul hu c, ← mul_sub, mul_pow, integral_const_mul,
    ← Finset.mul_sum, ← mul_add]

theorem smoothH1Approximation_const_mul {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (c : ℝ) :
    SmoothH1Approximation (fun x => c * f x) (fun j x => c * g j x) (fun n x => c * u n x) := by
  refine ⟨hasL2WeakGradient_const_mul hu.weak_gradient c, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hu.smooth n).const_smul c
  · intro n
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hu.memLp n).const_smul c
  · intro n j
    simpa only [smooth_partial_const_mul (hu.smooth n) c, Pi.smul_apply, smul_eq_mul] using!
      (hu.partial_memLp n j).const_smul c
  · have he (n : ℕ) : h1Error (fun x => c * f x) (fun j x => c * g j x)
        (fun x => c * u n x) = c ^ 2 * h1Error f g (u n) := h1Error_const_mul (hu.smooth n) c
    simpa only [he, mul_zero] using hu.convergence.const_mul (c ^ 2)

theorem smoothH1Approximation_zero :
    SmoothH1Approximation (fun _ : Space => 0) (fun (_ : Fin 3) (_ : Space) => 0)
      (fun (_ : ℕ) (_ : Space) => 0) := by
  refine ⟨hasL2WeakGradient_zero, fun _ => contDiff_const, fun _ => MemLp.zero', ?_, ?_⟩
  · intro n j
    simp
  · simp [h1Error]

end FreudenthalSVLean.H1ApproximationLinearity
