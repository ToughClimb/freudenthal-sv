import FreudenthalSVLean.ConformingH1Zero

/-!
# An explicit Poincare bound on the physical cube

For the manuscript's H1 stability interpretation, a smooth cube-supported
function satisfies integral u^2 <= 4 integral (partial_i u)^2 for each
coordinate i.  The proof tests genuine weak integration by parts against
x_i u and applies a pointwise completed-square inequality using |x_i|<=1
on the cube.  Thus it uses neither a stipulated Poincare constant nor a
formal integral of a nonintegrable function.  The following transport
to finite-element functions uses the proved actual smooth approximation.
-/

open scoped ContDiff Topology
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.WeakVelocityGradient

noncomputable section

namespace FreudenthalSVLean.SmoothCubePoincare

set_option backward.isDefEq.respectTransparency false

theorem coordinate_contDiff (i : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x i) :=
  (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).contDiff

theorem coordinate_fderiv (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => y i) x (Pi.single i 1) = 1 := by
  have hd : HasFDerivAt (fun y : Space => y i) (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ) x := by
    simpa only using! (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt
  rw [hd.fderiv]
  simp

theorem smooth_cube_poincare {u : Space → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : Function.support u ⊆ cube) (i : Fin 3) :
    (∫ x, (u x) ^ 2) ≤ 4 * ∫ x, (fderiv ℝ u x (Pi.single i 1)) ^ 2 := by
  let d : Space → ℝ := fun x => fderiv ℝ u x (Pi.single i 1)
  let φ : Space → ℝ := fun x => x i * u x
  have hd : Continuous d := (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport d := by
    simpa only [d, Function.comp_def] using (hc.fderiv ℝ).comp_left
      (g := fun L : Space →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)
  have hφ : ContDiff ℝ ∞ φ := (coordinate_contDiff i).mul hu
  have hφc : HasCompactSupport φ := hc.mul_left
  have hφd (x : Space) : fderiv ℝ φ x (Pi.single i 1) = u x + x i * d x := by
    change fderiv ℝ (fun y : Space => y i * u y) x (Pi.single i 1) = _
    rw [fderiv_fun_mul ((coordinate_contDiff i).differentiable (by simp)).differentiableAt
      (hu.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, coordinate_fderiv, mul_one]
    ring
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hu (by simp)
  have hw := lipschitz_hasWeakPartial hC i (Filter.EventuallyEq.rfl :
    (fun x => fderiv ℝ u x (Pi.single i 1)) =ᵐ[volume] d)
    φ hφ hφc
  have iu : Integrable (fun x => (u x) ^ 2) := (hu.continuous.memLp_of_hasCompactSupport
    (p := 2) hc).integrable_sq
  have id : Integrable (fun x => (d x) ^ 2) := (hd.memLp_of_hasCompactSupport
    (p := 2) hdc).integrable_sq
  have iI : Integrable (fun x => u x * (x i * d x)) :=
    (hu.continuous.mul ((continuous_apply i).mul hd)).integrable_of_hasCompactSupport hc.mul_right
  have he : (∫ x, u x * (x i * d x)) = -((∫ x, (u x) ^ 2) + ∫ x, u x * (x i * d x)) := by
    calc
      _ = ∫ x, d x * φ x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [φ]
        ring
      _ = -(∫ x, u x * fderiv ℝ φ x (Pi.single i 1)) := hw
      _ = _ := by
        simp only [hφd, mul_add, ← pow_two]
        rw [integral_add iu iI]
  have hpoint (x : Space) : -(2 * (u x * (x i * d x))) ≤ (u x) ^ 2 / 2 + 2 * (d x) ^ 2 := by
    by_cases hx : x ∈ cube
    · have h0 : 0 ≤ x i := hx.1 i
      have h1 : x i ≤ 1 := hx.2 i
      have hsquare : (x i * d x) ^ 2 ≤ (d x) ^ 2 := by
        nlinarith [sq_nonneg (d x), mul_nonneg (sq_nonneg (d x)) (show 0 ≤ 1 - (x i) ^ 2 by nlinarith)]
      nlinarith [sq_nonneg (u x / 2 + x i * d x)]
    · have hz : u x = 0 := Function.notMem_support.mp (fun hh => hx (hs hh))
      simp only [hz, zero_mul, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_add, neg_zero]
      positivity
  have hi := integral_mono (iI.const_mul 2).neg ((iu.div_const 2).add (id.const_mul 2)) hpoint
  change (∫ x, -(2 * (u x * (x i * d x)))) ≤ ∫ x, (u x) ^ 2 / 2 + 2 * (d x) ^ 2 at hi
  rw [integral_neg, integral_const_mul, integral_add (iu.div_const 2) (id.const_mul 2),
    integral_div, integral_const_mul] at hi
  rw [he] at hi
  change (∫ x, (u x) ^ 2) ≤ 4 * ∫ x, (d x) ^ 2
  linarith

end FreudenthalSVLean.SmoothCubePoincare
