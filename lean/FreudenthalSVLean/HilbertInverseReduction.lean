import FreudenthalSVLean.HilbertCubeDivergence
import FreudenthalSVLean.HilbertLinearSection
import FreudenthalSVLean.ContinuousInverseReduction

/-!
# Transport of genuine Hilbert divergence solvability to both mesh targets

For manuscript Lemma `means`, surjectivity of actual cube divergence
between the proved complete Hilbert spaces gives one bounded linear
section. Fixed linear actual H1_0 representatives turn it into the exact
actual-function continuous inverse specification. All stability constants
precede the input and the mesh. The full k=4,5 targets follow from this
surjectivity statement. `BogovskiiHilbertSurjectivity` proves the statement
and `MainTheorem` instantiates the unconditional continuous and discrete
inverse theorems.
-/

open scoped BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.HilbertCubeDivergence
open FreudenthalSVLean.HilbertLinearSection
open FreudenthalSVLean.ContinuousInverseReduction
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.WeakLinearFaceTrace

noncomputable section

namespace FreudenthalSVLean.HilbertInverseReduction

set_option backward.isDefEq.respectTransparency false

def smoothVector : (Fin 3 → h1ZeroSpace) →ₗ[ℝ] (Fin 3 → smoothH1Space) :=
  LinearMap.pi (fun j => smoothInclusion.comp (LinearMap.proj j))

def sectionActualMap (S : pressureHilbert →L[ℝ] VectorHilbert) :
    cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space) :=
  smoothVector.comp (vectorRepresentative.comp (S.toLinearMap.comp pressureClass))

theorem sectionActualMap_spec (S : pressureHilbert →L[ℝ] VectorHilbert)
    (hS : ∀ q, divergenceHilbert (S q) = q) :
    ContinuousCubeInverseSpec (sectionActualMap S) (‖S‖ ^ 2 + 1) := by
  constructor
  · intro q j
    exact (vectorRepresentative (S (pressureClass q)) j).property
  · intro q
    change (fun x => ∑ j : Fin 3,
      (vectorRepresentative (S (pressureClass q)) j).val.2 j x) =ᵐ[volume] q.val
    have he : ((divergenceHilbert (S (pressureClass q))).val : Space → ℝ) =ᵐ[volume]
        q.val := by
      rw [hS]
      exact q.property.1.coeFn_toLp
    exact (divergenceHilbert_ae _).symm.trans he
  · intro q
    change BoundedWeakDivergence.vectorGradientEnergy
      (vectorRepresentative (S (pressureClass q))) ≤ (‖S‖ ^ 2 + 1) * ∫ x, (q.val x) ^ 2
    have hs : ‖S (pressureClass q)‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖pressureClass q‖ ^ 2 := by
      simpa only [sq, mul_mul_mul_comm] using
        mul_self_le_mul_self (norm_nonneg (S (pressureClass q))) (S.le_opNorm (pressureClass q))
    calc
      _ ≤ ‖S (pressureClass q)‖ ^ 2 := vectorRepresentative_gradient_bound _
      _ ≤ ‖S‖ ^ 2 * ‖pressureClass q‖ ^ 2 := hs
      _ ≤ (‖S‖ ^ 2 + 1) * ‖pressureClass q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by rw [pressureClass_norm_square]

theorem continuous_inverse_of_surjective
    (h : Function.Surjective divergenceHilbert) : HasContinuousCubeRightInverse := by
  obtain ⟨S, hS⟩ := section_of_surjective divergenceHilbert h
  exact ⟨‖S‖ ^ 2 + 1, by positivity, sectionActualMap S, sectionActualMap_spec S hS⟩

theorem quartic_uniform_right_inverse_of_surjective
    (h : Function.Surjective divergenceHilbert) : HasUniformRightInverse 4 :=
  quartic_uniform_right_inverse_of_continuous (continuous_inverse_of_surjective h)

theorem quintic_uniform_right_inverse_of_surjective
    (h : Function.Surjective divergenceHilbert) : HasUniformRightInverse 5 :=
  quintic_uniform_right_inverse_of_continuous (continuous_inverse_of_surjective h)

end FreudenthalSVLean.HilbertInverseReduction
