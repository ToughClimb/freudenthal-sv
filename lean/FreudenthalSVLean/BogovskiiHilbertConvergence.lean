import FreudenthalSVLean.BogovskiiHilbertTruncation

/-!
# Genuine convergence of Hilbert divergences of uniformly bounded lifts

For manuscript Lemma `means`, the error norm of the actual Hilbert
divergence is exactly the genuine squared L2 error of its proved mass
mixture. Almost-everywhere representative identities justify this equality;
the genuine pressure convergence then gives norm convergence. Thus the
bounded truncations approximate every actual smooth mean-zero pressure in
the complete pressure Hilbert space, with no surjectivity assumption.
-/

open scoped Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.SmoothCubePressureSpace
open FreudenthalSVLean.HilbertCubeDivergence
open FreudenthalSVLean.BogovskiiDivergenceIdentity
open FreudenthalSVLean.BogovskiiPressureConvergence
open FreudenthalSVLean.BogovskiiHilbertTruncation

noncomputable section

namespace FreudenthalSVLean.BogovskiiHilbertConvergence

set_option backward.isDefEq.respectTransparency false

def approximatingLift (q : smoothPressureSpace) (n : ℕ) : VectorHilbert :=
  truncatedHilbert (epsilon n) (epsilon_pos n) q

theorem approximatingLift_norm_bound (q : smoothPressureSpace) (n : ℕ) :
    ‖approximatingLift q n‖ ≤ liftingConstant * ‖smoothPressureClass q‖ :=
  truncatedHilbert_norm_bound (epsilon_pos n) (epsilon_le_half n) q

theorem approximatingLift_error_norm_square (q : smoothPressureSpace) (n : ℕ) :
    ‖divergenceHilbert (approximatingLift q n) - smoothPressureClass q‖ ^ 2 =
      ∫ x : Space, (smoothedPressure (epsilon n) q.val.val x - q.val.val x) ^ 2 := by
  let a := divergenceHilbert (approximatingLift q n)
  let b := smoothPressureClass q
  change ‖a.val - b.val‖ ^ 2 = _
  have he := toLp_norm_square (Lp.memLp (a.val - b.val))
  rw [Lp.toLp_coeFn] at he
  rw [he]
  apply integral_congr_ae
  have ha : (a.val : Space → ℝ) =ᵐ[volume] smoothedPressure (epsilon n) q.val.val :=
    truncatedHilbert_divergence_ae (epsilon_pos n) (epsilon_lt_one n).le q
  have hb : (b.val : Space → ℝ) =ᵐ[volume] q.val.val := q.val.property.1.coeFn_toLp
  filter_upwards [Lp.coeFn_sub a.val b.val, ha, hb] with x hx hy hz
  simp only [hx, Pi.sub_apply, hy, hz]

theorem approximatingLift_divergence_tendsto (q : smoothPressureSpace) :
    Tendsto (fun n => divergenceHilbert (approximatingLift q n)) atTop
      (𝓝 (smoothPressureClass q)) := by
  have he : Tendsto (fun n => ‖divergenceHilbert (approximatingLift q n) -
      smoothPressureClass q‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp only [approximatingLift_error_norm_square]
    exact smoothedPressure_L2_tendsto q.val.val q.property.1 q.property.2 (smoothPressure_support q)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp he
  change Tendsto (fun n => Real.sqrt (‖divergenceHilbert (approximatingLift q n) -
    smoothPressureClass q‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hs
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using! hs

end FreudenthalSVLean.BogovskiiHilbertConvergence
