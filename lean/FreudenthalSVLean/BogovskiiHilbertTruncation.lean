import FreudenthalSVLean.BogovskiiGradientEstimate
import FreudenthalSVLean.BogovskiiPressureConvergence
import FreudenthalSVLean.SmoothCubePressureSpace
import FreudenthalSVLean.HilbertCubeDivergence

/-!
# Actual uniformly bounded Hilbert Bogovskii truncations

For the continuous lifting in manuscript Lemma `means`, the genuine C1
truncated fields define actual H1_0 Hilbert jets. Their full Hilbert norm
is bounded uniformly in the truncation by the true pressure L2 norm,
using the proved gradient estimate and cube Poincare inequality. The
actual weak divergence agrees with the proved mass mixture, including
the zero-mean compatibility. The genuine L2 pressure convergence therefore
gives convergent divergences of uniformly bounded actual preimages.
-/

open scoped ContDiff BigOperators Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.H1JetRepresentative
open FreudenthalSVLean.HilbertCubeDivergence
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.SmoothCubePressureSpace
open FreudenthalSVLean.BogovskiiTruncation
open FreudenthalSVLean.BogovskiiC1Truncation
open FreudenthalSVLean.C1CubeH1Zero
open FreudenthalSVLean.BogovskiiGradientEstimate
open FreudenthalSVLean.BogovskiiDivergenceIdentity
open FreudenthalSVLean.BogovskiiPressureConvergence

noncomputable section

namespace FreudenthalSVLean.BogovskiiHilbertTruncation

set_option backward.isDefEq.respectTransparency false

def truncatedData (ε : ℝ) (hε : 0 < ε) (q : smoothPressureSpace) (j : Fin 3) : h1ZeroSpace :=
  ⟨(truncated ε q.val.val j, classicalPartial (truncated ε q.val.val j)),
    truncated_inH1ZeroCube hε q.property.1.continuous q.val.property.2.1 j⟩

def truncatedHilbert (ε : ℝ) (hε : 0 < ε) (q : smoothPressureSpace) : VectorHilbert :=
  WithLp.toLp 2 (fun j => jetClass (truncatedData ε hε q j))

theorem smoothPressure_support (q : smoothPressureSpace) :
    Function.support q.val.val ⊆ cube := by
  intro x hx
  by_contra hn
  exact hx (q.val.property.2.1 x hn)

theorem truncatedHilbert_norm_square {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (q : smoothPressureSpace) :
    ‖truncatedHilbert ε hε q‖ ^ 2 ≤ 5 * gradientConstant * ‖smoothPressureClass q‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ j : Fin 3, 5 * ∑ i : Fin 3,
        ∫ x : Space, classicalPartial (truncated ε q.val.val j) i x ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact jetLinear_gradient_bound (truncatedData ε hε q j)
    _ = 5 * (∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x : Space, classicalPartial (truncated ε q.val.val j) i x ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 5 * (gradientConstant * ∫ x : Space, q.val.val x ^ 2) :=
      mul_le_mul_of_nonneg_left
        (truncated_gradient_L2_bound hε hεh q.val.val q.property.1 q.property.2
          (smoothPressure_support q)) (by norm_num)
    _ = _ := by
      change 5 * (gradientConstant * ∫ x : Space, q.val.val x ^ 2) =
        5 * gradientConstant * ‖pressureClass q.val‖ ^ 2
      rw [pressureClass_norm_square, mul_assoc]

def liftingConstant : ℝ := Real.sqrt (5 * gradientConstant)

theorem liftingConstant_nonneg : 0 ≤ liftingConstant := Real.sqrt_nonneg _

theorem truncatedHilbert_norm_bound {ε : ℝ} (hε : 0 < ε) (hεh : ε ≤ 1 / 2)
    (q : smoothPressureSpace) :
    ‖truncatedHilbert ε hε q‖ ≤ liftingConstant * ‖smoothPressureClass q‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg liftingConstant_nonneg (norm_nonneg _))).mp
  rw [mul_pow, liftingConstant, Real.sq_sqrt
    (mul_nonneg (by norm_num) gradientConstant_nonneg)]
  exact truncatedHilbert_norm_square hε hεh q

theorem representative_partial_ae (v : h1ZeroSpace) (i : Fin 3) :
    (representative (jetClass v)).val.2 i =ᵐ[volume] v.val.2 i := by
  have he := congrArg (fun z : H1JetHilbert => z i.succ) (representative_class (jetClass v))
  change jetLinear (representative (jetClass v)) i.succ = jetLinear v i.succ at he
  rw [jetLinear_apply, jetLinear_apply] at he
  exact (MemLp.toLp_eq_toLp_iff _ _).mp he

theorem truncatedHilbert_divergence_ae {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : smoothPressureSpace) :
    ((divergenceHilbert (truncatedHilbert ε hε q)).val : Space → ℝ) =ᵐ[volume]
      smoothedPressure ε q.val.val := by
  apply (divergenceHilbert_ae _).trans
  have hj (j : Fin 3) :
      (vectorRepresentative (truncatedHilbert ε hε q) j).val.2 j =ᵐ[volume]
        classicalPartial (truncated ε q.val.val j) j :=
    representative_partial_ae (truncatedData ε hε q j) j
  filter_upwards [ae_all_iff.mpr hj] with x hx
  calc
    _ = ∑ j : Fin 3, classicalPartial (truncated ε q.val.val j) j x :=
      Finset.sum_congr rfl (fun j _ => hx j)
    _ = _ := truncated_divergence_mean_zero hε hε1 q.property.1.continuous
      q.val.property.2.1 q.val.property.2.2 x

end FreudenthalSVLean.BogovskiiHilbertTruncation
