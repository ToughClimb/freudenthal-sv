import FreudenthalSVLean.VelocityH1Representation
import FreudenthalSVLean.VolumeInterpolationL2
import FreudenthalSVLean.BoundaryWeakFaceTrace

/-!
# Actual weak-H1 residual of the uniform volume interpolant

For manuscript Lemma `means`, the residual is a single fixed linear
map on actual smooth-approximable weak H1 data. Its values are the true
input minus the actual conforming P1 velocity, and its weak gradients
are their actual difference. The proved interpolation estimates give
an h-order meshwise L2 error and a uniform whole-space gradient bound.
All boundary-face fluxes vanish for genuine H1_0 input by linearity of
the weak trace and the proved zero traces of both terms.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.WeakFaceGauss
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.FaceL2MeanEstimate
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.BoundaryWeakFaceTrace
open FreudenthalSVLean.H1ApproximationLinearity
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.VelocityH1Representation

noncomputable section

namespace FreudenthalSVLean.InterpolationResidual

set_option backward.isDefEq.respectTransparency false

def interpolationResidual {N : ℕ} (hN : 0 < N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] (Fin 3 → smoothH1Space) :=
  LinearMap.id - (velocityH1Linear hN).comp (volumeNodalInterpolation hN)

theorem residual_value {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) (j : Fin 3) :
    (interpolationResidual hN v j).val.1 =
      fun x => (v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x := rfl

theorem residual_gradient {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) (j i : Fin 3) :
    (interpolationResidual hN v j).val.2 i = fun x =>
      (v j).val.2 i x - piecewisePressure (fun t =>
        pderiv i ((volumeNodalInterpolation hN v).val t j)) x := rfl

theorem inputGradientEnergy_nonneg (v : Fin 3 → smoothH1Space) : 0 ≤ inputGradientEnergy v :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem inputGradientEnergy_sub_bound (v w : Fin 3 → smoothH1Space) :
    inputGradientEnergy (v - w) ≤ 2 * (inputGradientEnergy v + inputGradientEnergy w) := by
  have ht (j i : Fin 3) :
      (∫ x, ((v j).val.2 i x - (w j).val.2 i x) ^ 2) ≤
        2 * ((∫ x, ((v j).val.2 i x) ^ 2) + ∫ x, ((w j).val.2 i x) ^ 2) := by
    obtain ⟨u, hu⟩ := (v j).property
    obtain ⟨z, hz⟩ := (w j).property
    simpa only [Pi.neg_apply, neg_sq, sub_eq_add_neg] using!
      integral_square_add_bound (hu.weak_gradient.2 i).1 (hz.weak_gradient.2 i).1.neg
  calc
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3, 2 *
        ((∫ x, ((v j).val.2 i x) ^ 2) + ∫ x, ((w j).val.2 i x) ^ 2) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => ht j i))
    _ = _ := by simp only [inputGradientEnergy, ← Finset.mul_sum, Finset.sum_add_distrib]

theorem residual_gradient_bound {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    inputGradientEnergy (interpolationResidual hN v) ≤ 746498 * inputGradientEnergy v := by
  have he := inputGradientEnergy_sub_bound v (velocityH1Linear hN (volumeNodalInterpolation hN v))
  rw [velocityH1Linear_energy] at he
  calc
    _ ≤ 2 * (inputGradientEnergy v + velocityEnergy (volumeNodalInterpolation hN v).val) := he
    _ ≤ 2 * (inputGradientEnergy v + 373248 * inputGradientEnergy v) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (volumeNodalInterpolation_gradient_bound hN v hv)) (by norm_num)
    _ = _ := by ring

theorem residual_mesh_value_error {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    (∑ t : Tet N, ∑ j : Fin 3, ∫ x in tetrahedron t,
      ((interpolationResidual hN v j).val.1 x) ^ 2) = interpolationError hN v := by
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  apply setIntegral_congr_fun (tetrahedron_isCompact hN t).measurableSet
  intro x hx
  change ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2 = _
  rw [velocityFunction_on_element hN _ t x hx j]

theorem residual_boundary_flux_zero {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : ¬ activeGridFace t r) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    meshFluxLinear hN t r (interpolationResidual hN v) = 0 := by
  rw [meshFluxLinear_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hi : traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r (v j) = 0 :=
    inactive_gridFace_weak_trace_zero hN t r ha (hv j)
      (trace_spec t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r (v j))
  have ho : traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r
      (velocityH1Linear hN (volumeNodalInterpolation hN v) j) = 0 :=
    inactive_gridFace_weak_trace_zero hN t r ha
      (velocityH1Linear_inH1ZeroCube hN (volumeNodalInterpolation hN v) j)
      (trace_spec t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r
        (velocityH1Linear hN (volumeNodalInterpolation hN v) j))
  change outwardWeight t.2 (meshScale N) r j *
    faceMean (traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r
      (v j - velocityH1Linear hN (volumeNodalInterpolation hN v) j)) = 0
  rw [map_sub, hi, ho, sub_self, map_zero, mul_zero]

end FreudenthalSVLean.InterpolationResidual
