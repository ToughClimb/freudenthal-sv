import FreudenthalSVLean.StableGlobalFaceCorrection
import FreudenthalSVLean.InterpolationResidual
import FreudenthalSVLean.GlobalVertexLift

/-!
# A uniformly stable fixed linear element-mean Fortin map

For manuscript Lemma `means` and equation `SZ`, actual volume-averaging
P1 interpolation followed by the fixed cubic interior-face correction
gives one linear operator on genuine smooth-approximable weak H1 data.
For H1_0 input it matches the actual divergence integral on every mesh
element, including boundary elements, and has an N-independent physical
gradient-energy bound. Constants precede all N>0 and the map precedes
its input. The theorem does not assert existence of a continuous
divergence inverse; supplying that inverse remains a separate obligation.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.VelocityH1Representation
open FreudenthalSVLean.InterpolationResidual
open FreudenthalSVLean.GlobalFaceCorrection
open FreudenthalSVLean.StableGlobalFaceCorrection
open FreudenthalSVLean.WeakFaceFluxCorrection
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.GlobalVertexLift

noncomputable section

namespace FreudenthalSVLean.UniformMeanFortin

open Classical
set_option backward.isDefEq.respectTransparency false

def meanFortinLinear {N : ℕ} (hN : 0 < N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] velocitySpace N 3 :=
  (degreeInclusion (by decide : 1 ≤ 3)).comp (volumeNodalInterpolation hN) +
    (globalCorrectionLinear hN).comp (interpolationResidual hN)

theorem meanFortin_val {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    (meanFortinLinear hN v).val = (volumeNodalInterpolation hN v).val +
      (globalCorrectionLinear hN (interpolationResidual hN v)).val := rfl

theorem meanFortin_means {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) (t : Tet N) :
    tetIntegral hN t (divergence N (meanFortinLinear hN v).val t) =
      ∑ j : Fin 3, ∫ x in tetrahedron t, (v j).val.2 j x := by
  rw [meanFortin_val, map_add]
  simp only [Pi.add_apply, map_add]
  rw [globalCorrection_means]
  have hs : (∑ r : Fin 4, if activeGridFace t r then
      meshFluxLinear hN t r (interpolationResidual hN v) else 0) =
        ∑ r : Fin 4, meshFluxLinear hN t r (interpolationResidual hN v) := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases ha : activeGridFace t r
    · rw [if_pos ha]
    · rw [if_neg ha, residual_boundary_flux_zero hN t r ha v hv]
  have hp : tetIntegral hN t (divergence N (volumeNodalInterpolation hN v).val t) =
      ∑ r : Fin 4, meshFluxLinear hN t r (velocityH1Linear hN (volumeNodalInterpolation hN v)) :=
    meshFluxLinear_divergence_mean hN (volumeNodalInterpolation hN v) t
  rw [hs, hp]
  have hr (r : Fin 4) : meshFluxLinear hN t r (interpolationResidual hN v) =
      meshFluxLinear hN t r v -
        meshFluxLinear hN t r (velocityH1Linear hN (volumeNodalInterpolation hN v)) :=
    (meshFluxLinear hN t r).map_sub _ _
  simp only [hr, Finset.sum_sub_distrib]
  rw [meshFluxLinear_gauss hN t v]
  abel

theorem residualCorrection_energy {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    velocityEnergy (globalCorrectionLinear hN (interpolationResidual hN v)).val ≤
      (214990912 * correctionConstant) * inputGradientEnergy v := by
  have he := globalCorrection_energy_bound hN (interpolationResidual hN v)
  have hvsum : (∑ t : Tet N, elementValueEnergy (interpolationResidual hN v) t) =
      interpolationError hN v := residual_mesh_value_error hN v
  rw [hvsum] at he
  have herror := volumeNodalInterpolation_error_bound hN v hv
  have hgradient := residual_gradient_bound hN v hv
  calc
    _ ≤ 32 * correctionConstant *
        (6 * ((meshScale N) ^ 2)⁻¹ * interpolationError hN v +
          inputGradientEnergy (interpolationResidual hN v)) := he
    _ ≤ 32 * correctionConstant *
        (6 * ((meshScale N) ^ 2)⁻¹ * (995328 * (meshScale N) ^ 2 * inputGradientEnergy v) +
          746498 * inputGradientEnergy v) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left herror (by positivity)) hgradient)
        (by positivity [correctionConstant_pos])
    _ = _ := by
      field_simp [(meshScale_pos N hN).ne']
      ring

def meanFortinConstant : ℝ := 2 * (373248 + 214990912 * correctionConstant)

theorem meanFortinConstant_pos : 0 < meanFortinConstant := by
  unfold meanFortinConstant
  positivity [correctionConstant_pos]

theorem meanFortin_energy {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    velocityEnergy (meanFortinLinear hN v).val ≤ meanFortinConstant * inputGradientEnergy v := by
  rw [meanFortin_val]
  calc
    _ ≤ 2 * (velocityEnergy (volumeNodalInterpolation hN v).val +
        velocityEnergy (globalCorrectionLinear hN (interpolationResidual hN v)).val) :=
      StableCanonicalEdgeLift.add_energy_bound hN _ _
    _ ≤ 2 * (373248 * inputGradientEnergy v +
        (214990912 * correctionConstant) * inputGradientEnergy v) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (volumeNodalInterpolation_gradient_bound hN v hv)
          (residualCorrection_energy hN v hv)) (by norm_num)
    _ = _ := by unfold meanFortinConstant; ring

/-- Genuine element means and a constant before N, with a fixed linear map before input. -/
theorem uniform_mean_fortin : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N),
    ∃ F : (Fin 3 → smoothH1Space) →ₗ[ℝ] velocitySpace N 3,
      ∀ v : Fin 3 → smoothH1Space,
        (∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) →
        (∀ t : Tet N, tetIntegral hN t (divergence N (F v).val t) =
          ∑ j : Fin 3, ∫ x in tetrahedron t, (v j).val.2 j x) ∧
        velocityEnergy (F v).val ≤ C * inputGradientEnergy v := by
  exact ⟨meanFortinConstant, meanFortinConstant_pos, fun _ hN =>
    ⟨meanFortinLinear hN, fun v hv => ⟨meanFortin_means hN v hv, meanFortin_energy hN v hv⟩⟩⟩

end FreudenthalSVLean.UniformMeanFortin
