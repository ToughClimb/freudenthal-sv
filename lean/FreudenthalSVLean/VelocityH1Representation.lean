import FreudenthalSVLean.ConformingWeakFaceTrace
import FreudenthalSVLean.StableVolumeInterpolation
import FreudenthalSVLean.FaceL2MeanEstimate

/-!
# A fixed linear genuine weak-H1 representation of velocities

For the residual used in manuscript Lemma `means`, every actual
conforming velocity is embedded by one linear map into actual functions
and their actual L2 weak gradients, with a proved smooth H1
approximation. Its gradient energy is exactly the physical element
gradient energy. The actual weak face flux is identified with the true
polynomial face integral by codimension-one convergence, and hence the
sum of its four fluxes is its genuine divergence mean.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.ConformingWeakFaceTrace
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.WeakFaceGauss
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.FaceL2MeanEstimate

noncomputable section

namespace FreudenthalSVLean.VelocityH1Representation

set_option backward.isDefEq.respectTransparency false

def componentH1Linear {N k : ℕ} (hN : 0 < N) (j : Fin 3) :
    velocitySpace N k →ₗ[ℝ] smoothH1Space where
  toFun v := ⟨(velocityFunction hN v j,
      fun i => piecewisePressure (fun t => pderiv i (v.val t j))),
    ⟨fun n => InteriorMollification.interiorMollify n (velocityFunction hN v j),
      velocityFunction_interiorApproximation hN v j⟩⟩
  map_add' v w := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun ((velocityFunctionLinear hN).map_add v w) j
    · funext i
      have he : (fun t => pderiv i ((v + w).val t j)) =
          (fun t => pderiv i (v.val t j)) + (fun t => pderiv i (w.val t j)) := by
        funext t
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
      change piecewisePressure (fun t => pderiv i ((v + w).val t j)) = _
      rw [he]
      exact (piecewisePressureLinear N).map_add _ _
  map_smul' c v := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun ((velocityFunctionLinear hN).map_smul c v) j
    · funext i
      have he : (fun t => pderiv i ((c • v).val t j)) =
          c • (fun t => pderiv i (v.val t j)) := by
        funext t
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_C_mul, pderiv_C_mul]
      change piecewisePressure (fun t => pderiv i ((c • v).val t j)) = _
      rw [he]
      exact (piecewisePressureLinear N).map_smul c _

def velocityH1Linear {N k : ℕ} (hN : 0 < N) :
    velocitySpace N k →ₗ[ℝ] (Fin 3 → smoothH1Space) :=
  LinearMap.pi (fun j => componentH1Linear hN j)

theorem velocityH1Linear_value {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) (j : Fin 3) :
    (velocityH1Linear hN v j).val.1 = velocityFunction hN v j := rfl

theorem velocityH1Linear_gradient {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) (j i : Fin 3) :
    (velocityH1Linear hN v j).val.2 i = piecewisePressure (fun t => pderiv i (v.val t j)) := rfl

theorem velocityH1Linear_inH1ZeroCube {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) (j : Fin 3) :
    InH1ZeroCube (velocityH1Linear hN v j).val.1 (velocityH1Linear hN v j).val.2 :=
  velocityFunction_inH1ZeroCube hN v j

theorem velocityH1Linear_energy {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) :
    inputGradientEnergy (velocityH1Linear hN v) = velocityEnergy v.val :=
  velocityFunction_weak_gradient_energy hN v

def meshFluxLinear {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] ℝ :=
  ∑ j : Fin 3, outwardWeight t.2 (meshScale N) r j •
    ((faceMean.toLinearMap.comp
      (traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r)).comp
        (LinearMap.proj j))

theorem meshFluxLinear_apply {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (v : Fin 3 → smoothH1Space) :
    meshFluxLinear hN t r v = traceFlux t.2 (meshScale N) r (fun j =>
      traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r (v j)) := by
  simp only [meshFluxLinear, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.proj_apply, smul_eq_mul, traceFlux]

theorem meshFluxLinear_gauss {N : ℕ} (hN : 0 < N) (t : Tet N)
    (v : Fin 3 → smoothH1Space) :
    (∑ j : Fin 3, ∫ x in tetrahedron t, (v j).val.2 j x) =
      ∑ r : Fin 4, meshFluxLinear hN t r v := by
  simp only [meshFluxLinear_apply, traceFlux]
  calc
    _ = ∑ j : Fin 3, ∑ r : Fin 4, outwardWeight t.2 (meshScale N) r j *
        faceMean (traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r (v j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact traceMap_gauss t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) (v j) j
    _ = _ := Finset.sum_comm

theorem meshFluxLinear_polynomial {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (r : Fin 4) :
    meshFluxLinear hN t r (velocityH1Linear hN v) =
      ∑ j : Fin 3, outwardWeight t.2 (meshScale N) r j *
        scaledFaceIntegral t.2 (cellOrigin t.1) (meshScale N) r (v.val t j) := by
  rw [meshFluxLinear_apply]
  unfold traceFlux
  apply Finset.sum_congr rfl
  intro j _
  have ht : traceMap t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r
      (velocityH1Linear hN v j) = continuousFaceL2 (continuous_eval (v.val t j))
        t.2 (cellOrigin t.1) (meshScale N) r :=
    velocityFunction_weak_trace_polynomial hN v t r j
      (trace_spec t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r
        (velocityH1Linear hN v j))
  dsimp only
  rw [ht]
  rw [faceMean]
  exact congrArg (fun z => outwardWeight t.2 (meshScale N) r j * z)
    (l2Integral_toLp _ faceMeasure_finite
      (continuous_face_memLp (continuous_eval (v.val t j)) t.2 (cellOrigin t.1) (meshScale N) r))

theorem meshFluxLinear_divergence_mean {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) :
    (∫ x in tetrahedron t, eval x (divergence N v.val t)) =
      ∑ r : Fin 4, meshFluxLinear hN t r (velocityH1Linear hN v) := by
  simp only [meshFluxLinear_polynomial]
  exact scaled_polynomial_divergence_gauss t.2 (cellOrigin t.1)
    (meshScale N) (meshScale_pos N hN) (v.val t)

end FreudenthalSVLean.VelocityH1Representation
