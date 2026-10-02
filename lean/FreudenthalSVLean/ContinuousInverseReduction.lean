import FreudenthalSVLean.CubeZeroMeanL2
import FreudenthalSVLean.UniformMeanFortin
import FreudenthalSVLean.UniformMeanLiftReduction

/-!
# Transport of a genuine continuous cube inverse to the full k=4,5 target

For the continuous step in manuscript Lemma `means`, this module states
the precise interface on actual zero-extended mean-zero L2 functions:
one fixed linear divergence inverse with genuine H1_0 outputs and a true
weak-gradient bound. The transport to mesh pressures, uniform mean lifting,
quartic/quintic discrete right inverses and separate N=1 case is proved
from this explicit interface. `MainTheorem.continuous_cube_right_inverse`
establishes its existence and instantiates both discrete targets. No
assumed theorem, new axiom or placeholder proof supplies that existence.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.UniformMeanFortin
open FreudenthalSVLean.GlobalVertexLift
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.UniformMeanLiftReduction

noncomputable section

namespace FreudenthalSVLean.ContinuousInverseReduction

set_option backward.isDefEq.respectTransparency false

structure ContinuousCubeInverseSpec
    (B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space)) (C : ℝ) : Prop where
  boundary : ∀ q j, InH1ZeroCube (B q j).val.1 (B q j).val.2
  divergence : ∀ q, (fun x => ∑ j : Fin 3, (B q j).val.2 j x) =ᵐ[volume] q.val
  energy : ∀ q, inputGradientEnergy (B q) ≤ C * ∫ x, (q.val x) ^ 2

/-- The continuous interface proved in `MainTheorem.continuous_cube_right_inverse`. -/
def HasContinuousCubeRightInverse : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space),
    ContinuousCubeInverseSpec B C

theorem continuous_mean_identity {N : ℕ} (hN : 0 < N)
    (B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space)) (C : ℝ)
    (hB : ContinuousCubeInverseSpec B C) (q : cubePressureFunctions) (t : Tet N) :
    (∑ j : Fin 3, ∫ x in tetrahedron t, (B q j).val.2 j x) =
      ∫ x in tetrahedron t, q.val x := by
  let : IsFiniteMeasure ((volume : Measure Space).restrict (tetrahedron t)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (tetrahedron_isCompact hN t).measure_lt_top⟩
  have hi (j : Fin 3) : IntegrableOn (fun x => (B q j).val.2 j x) (tetrahedron t) :=
    (((hB.boundary q j).1.2 j).1.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  exact integral_congr_ae (ae_restrict_of_ae (hB.divergence q))

def discreteMeanMap {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k)
    (B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space)) :
    pressureSpace N k →ₗ[ℝ] velocitySpace N k :=
  (degreeInclusion hk).comp ((meanFortinLinear hN).comp (B.comp (pressureEmbedding hN)))

theorem discreteMeanMap_means {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k)
    (B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space)) (C : ℝ)
    (hB : ContinuousCubeInverseSpec B C) (q : pressureSpace N k) (t : Tet N) :
    tetIntegral hN t (divergence N (discreteMeanMap hN hk B q).val t) =
      tetIntegral hN t (q.val t) := by
  change tetIntegral hN t (divergence N (meanFortinLinear hN (B (pressureEmbedding hN q))).val t) = _
  rw [meanFortin_means hN _ (hB.boundary _), continuous_mean_identity hN B C hB]
  exact piecewisePressure_integral_on_element hN q.val t

theorem discreteMeanMap_energy {N k : ℕ} (hN : 0 < N) (hk : 3 ≤ k)
    (B : cubePressureFunctions →ₗ[ℝ] (Fin 3 → smoothH1Space)) (C : ℝ)
    (hB : ContinuousCubeInverseSpec B C) (q : pressureSpace N k) :
    velocityEnergy (discreteMeanMap hN hk B q).val ≤
      (meanFortinConstant * C) * pressureEnergy q.val := by
  change velocityEnergy (meanFortinLinear hN (B (pressureEmbedding hN q))).val ≤ _
  calc
    _ ≤ meanFortinConstant * inputGradientEnergy (B (pressureEmbedding hN q)) :=
      meanFortin_energy hN _ (hB.boundary _)
    _ ≤ meanFortinConstant * (C * ∫ x, ((pressureEmbedding hN q).val x) ^ 2) :=
      mul_le_mul_of_nonneg_left (hB.energy _) meanFortinConstant_pos.le
    _ = _ := by rw [pressureEmbedding_energy]; ring

theorem uniform_initial_mean_lift_of_continuous (k : ℕ) (hk : 3 ≤ k)
    (h : HasContinuousCubeRightInverse) : HasUniformInitialMeanLift k := by
  obtain ⟨C, hC, B, hB⟩ := h
  refine ⟨meanFortinConstant * C, mul_pos meanFortinConstant_pos hC, ?_⟩
  intro N hN
  exact ⟨discreteMeanMap (by omega) hk B,
    ⟨discreteMeanMap_means (by omega) hk B C hB, discreteMeanMap_energy (by omega) hk B C hB⟩⟩

/-- Transport from the genuine continuous cube inverse; instantiated in `MainTheorem`. -/
theorem quartic_uniform_right_inverse_of_continuous
    (h : HasContinuousCubeRightInverse) : HasUniformRightInverse 4 :=
  quartic_uniform_right_inverse_iff_initial_mean_lift.mpr
    (uniform_initial_mean_lift_of_continuous 4 (by decide) h)

/-- Transport from the genuine continuous cube inverse; instantiated in `MainTheorem`. -/
theorem quintic_uniform_right_inverse_of_continuous
    (h : HasContinuousCubeRightInverse) : HasUniformRightInverse 5 :=
  quintic_uniform_right_inverse_iff_initial_mean_lift.mpr
    (uniform_initial_mean_lift_of_continuous 5 (by decide) h)

end FreudenthalSVLean.ContinuousInverseReduction
