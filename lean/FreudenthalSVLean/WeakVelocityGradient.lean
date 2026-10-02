import FreudenthalSVLean.ConformingVelocityLipschitz
import Mathlib.Analysis.Calculus.Rademacher

/-!+# Distributional gradients of actual finite-element velocities

For the manuscript's identification of the discrete gradient norm with
the H1 seminorm, every coordinate derivative satisfies the defining weak
integration-by-parts identity against every smooth compactly supported
test function on the full physical space.  The proof uses the established
global Lipschitz representative and Mathlib's proved integration-by-parts
theorem for line derivatives, then its actual almost-everywhere polynomial
gradient.  The weak derivative is unique among L2 functions.  These are
genuine distributional identities, not an inference from almost-everywhere
classical differentiability alone.  Density in H1 of test functions
supported inside the open cube remains a separate H1_0 obligation.
-/

open scoped BigOperators NNReal ContDiff
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ClassicalVelocityGradient
open FreudenthalSVLean.ConformingVelocityLipschitz

noncomputable section

namespace FreudenthalSVLean.WeakVelocityGradient

set_option backward.isDefEq.respectTransparency false

/-- The actual distributional partial-derivative identity on physical R3. -/
def HasWeakPartial (f g : Space → ℝ) (i : Fin 3) : Prop :=
  ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, g x * φ x) = -(∫ x, f x * fderiv ℝ φ x (Pi.single i 1))

/-- The standard L2 weak-gradient characterization, without a trace assertion. -/
def HasL2WeakGradient (f : Space → ℝ) (g : Fin 3 → Space → ℝ) : Prop :=
  MemLp f 2 volume ∧ ∀ i, MemLp (g i) 2 volume ∧ HasWeakPartial f (g i) i

theorem lipschitz_hasWeakPartial {f g : Space → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (i : Fin 3)
    (he : (fun x => fderiv ℝ f x (Pi.single i 1)) =ᵐ[volume] g) :
    HasWeakPartial f g i := by
  intro φ hφ hc
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  have hl : (fun x => lineDeriv ℝ f x (Pi.single i 1)) =ᵐ[volume] g := by
    filter_upwards [hf.ae_differentiableAt (μ := volume), he] with x hx hg
    exact hx.lineDeriv_eq_fderiv.trans hg
  calc
    (∫ x, g x * φ x) = ∫ x, lineDeriv ℝ f x (Pi.single i 1) * φ x := by
      apply integral_congr_ae
      filter_upwards [hl] with x hx
      exact congrArg (fun y : ℝ => y * φ x) hx.symm
    _ = ∫ x, lineDeriv ℝ φ x (-Pi.single i 1) * f x :=
      hf.integral_lineDeriv_mul_eq hD hc (Pi.single i 1)
    _ = -(∫ x, f x * fderiv ℝ φ x (Pi.single i 1)) := by
      simp only [(hφ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
        map_neg, mul_comm, mul_neg, integral_neg]

theorem hasWeakPartial_unique {f g h : Space → ℝ} {i : Fin 3}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hfg : HasWeakPartial f g i) (hfh : HasWeakPartial f h i) : g =ᵐ[volume] h := by
  apply ae_eq_of_integral_contDiff_smul_eq (hg.locallyIntegrable (by norm_num))
    (hh.locallyIntegrable (by norm_num))
  intro φ hφ hc
  simpa only [smul_eq_mul, mul_comm] using (hfg φ hφ hc).trans (hfh φ hφ hc).symm

theorem velocityFunction_hasWeakPartial {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    HasWeakPartial (velocityFunction hN v j)
      (piecewisePressure (fun t => pderiv i (v.val t j))) i := by
  obtain ⟨C, hC⟩ := velocityFunction_lipschitz hN v j
  exact lipschitz_hasWeakPartial hC i (velocityFunction_fderiv_ae hN v j i)

theorem velocityFunction_hasL2WeakGradient {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    HasL2WeakGradient (velocityFunction hN v j)
      (fun i => piecewisePressure (fun t => pderiv i (v.val t j))) := by
  refine ⟨velocityFunction_memLp hN v j, fun i => ⟨?_, ?_⟩⟩
  · exact piecewisePressure_memLp hN _
  · exact velocityFunction_hasWeakPartial hN v j i

/-- The manuscript's gradient energy is the true L2 weak-gradient energy. -/
theorem velocityFunction_weak_gradient_energy {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) :
    (∑ j : Fin 3, ∑ i : Fin 3,
      ∫ x, (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2) =
        velocityEnergy v.val := by
  simp only [piecewisePressure_square_integral hN, ← toMeshL2_norm_square hN]
  exact (velocityEnergy_eq_sum_L2 hN v.val).symm

end FreudenthalSVLean.WeakVelocityGradient
