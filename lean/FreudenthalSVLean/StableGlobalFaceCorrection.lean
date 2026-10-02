import FreudenthalSVLean.GlobalFaceCorrection
import FreudenthalSVLean.VolumeInterpolationL2

/-!
# Uniform global physical energy estimate for the cubic weak-flux correction

For manuscript Lemma `means`, the local face estimate and the proved
eight-incidence polynomial support bound yield a single mesh-independent
constant. Summation uses the true almost-everywhere element partition
and genuine weak-gradient L2 integrals, not coefficient norms. The
explicit h^{-2} value term is retained; its cancellation requires the
proved h-order interpolation error when this map is applied to a residual.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.VolumeInterpolationL2
open FreudenthalSVLean.VelocityH1Representation
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.InteriorFaceCoverage
open FreudenthalSVLean.FacePartner
open FreudenthalSVLean.WeakFaceFluxCorrection
open FreudenthalSVLean.GlobalFaceCorrection
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableGlobalFaceCorrection

open Classical
set_option backward.isDefEq.respectTransparency false

def elementValueEnergy {N : ℕ} (v : Fin 3 → smoothH1Space) (t : Tet N) : ℝ :=
  ∑ j : Fin 3, ∫ x in tetrahedron t, ((v j).val.1 x) ^ 2

def elementGradientEnergy {N : ℕ} (v : Fin 3 → smoothH1Space) (t : Tet N) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in tetrahedron t, ((v j).val.2 i x) ^ 2

theorem elementValueEnergy_nonneg {N : ℕ} (v : Fin 3 → smoothH1Space) (t : Tet N) :
    0 ≤ elementValueEnergy v t :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem elementGradientEnergy_nonneg {N : ℕ} (v : Fin 3 → smoothH1Space) (t : Tet N) :
    0 ≤ elementGradientEnergy v t :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem mesh_gradient_sum_bound {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    (∑ t : Tet N, elementGradientEnergy v t) ≤ inputGradientEnergy v := by
  unfold elementGradientEnergy inputGradientEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨u, hu⟩ := (v j).property
  have hi := (hu.weak_gradient.2 i).1.integrable_sq
  rw [← cube_integral_eq_element_sum hN hi]
  exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

theorem localCorrection_energy_bound {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (v : Fin 3 → smoothH1Space) :
    velocityEnergy (localCorrectionLinear hN f v) ≤ correctionConstant *
      (6 * ((meshScale N) ^ 2)⁻¹ * elementValueEnergy v f.1 + elementGradientEnergy v f.1) := by
  by_cases ha : activeGridFace f.1 f.2
  · let b := faceNeighbor hN f.1 f.2 ha
    have he := weak_faceCorrection_energy hN (anchoredOwner f.1 f.2) b.star f.2 b.index
      (anchoredOwner_omitted_ne f.1 f.2) b.omitted_ne b.owner_ne b.shared
      (fun j => (v j).val.1) (fun j => (v j).val.2) (fun j => (v j).property)
      (fun j => traceMap f.1.2 (cellOrigin f.1.1) (meshScale N) (meshScale_pos N hN) f.2 (v j))
      (fun j => WeakLinearFaceTrace.trace_spec f.1.2 (cellOrigin f.1.1)
        (meshScale N) (meshScale_pos N hN) f.2 (v j))
    have hfield : localCorrectionLinear hN f v =
        (1 / 2 : ℝ) • faceCorrection f.1 f.2 (meshFluxLinear hN f.1 f.2 v) := by
      change faceCorrection f.1 f.2 (orientedFluxLinear hN f v) = _
      simp only [orientedFluxLinear, if_pos ha, LinearMap.smul_apply, smul_eq_mul,
        faceCorrection, smul_smul]
    rw [hfield, velocityEnergy_smul]
    calc
      _ ≤ velocityEnergy (faceCorrection f.1 f.2 (meshFluxLinear hN f.1 f.2 v)) := by
        nlinarith [velocityEnergy_nonneg (faceCorrection f.1 f.2 (meshFluxLinear hN f.1 f.2 v))]
      _ ≤ _ := by
        simpa only [anchoredOwner, meshFluxLinear_apply, elementValueEnergy, elementGradientEnergy]
          using he
  · rw [localCorrection_inactive hN f ha v]
    have hn : 0 ≤ 6 * ((meshScale N) ^ 2)⁻¹ * elementValueEnergy v f.1 +
        elementGradientEnergy v f.1 :=
      add_nonneg (mul_nonneg (by positivity) (elementValueEnergy_nonneg v f.1))
        (elementGradientEnergy_nonneg v f.1)
    have hz : velocityEnergy (0 : BrokenVelocity N) = 0 := by simp [velocityEnergy]
    rw [hz]
    exact mul_nonneg correctionConstant_pos.le hn

theorem globalCorrection_energy_bound {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    velocityEnergy (globalCorrectionLinear hN v).val ≤ 32 * correctionConstant *
      (6 * ((meshScale N) ^ 2)⁻¹ * (∑ t : Tet N, elementValueEnergy v t) +
        inputGradientEnergy v) := by
  calc
    _ ≤ 8 * ∑ f : FaceIndex N, velocityEnergy (localCorrectionLinear hN f v) :=
      globalCorrection_overlap_energy hN v
    _ ≤ 8 * ∑ f : FaceIndex N, correctionConstant *
        (6 * ((meshScale N) ^ 2)⁻¹ * elementValueEnergy v f.1 + elementGradientEnergy v f.1) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => localCorrection_energy_bound hN f v))
        (by norm_num)
    _ = 32 * correctionConstant *
        (6 * ((meshScale N) ^ 2)⁻¹ * (∑ t : Tet N, elementValueEnergy v t) +
          ∑ t : Tet N, elementGradientEnergy v t) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum, Finset.sum_add_distrib]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mesh_gradient_sum_bound hN v)) (by positivity [correctionConstant_pos])

end FreudenthalSVLean.StableGlobalFaceCorrection
