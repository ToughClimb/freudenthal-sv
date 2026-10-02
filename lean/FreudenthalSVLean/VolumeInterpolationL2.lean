import FreudenthalSVLean.StableVolumeInterpolation
import FreudenthalSVLean.ConformingVelocityFunction

/-!
# Actual whole-space L2 error of the uniform volume interpolant

For manuscript Lemma `means` and equation `SZ`, the meshwise squared
error of the fixed P1 interpolant is identified with the true L2 error
of the actual conforming zero-extended velocity.  Closed elements share
only volume-zero faces, so actual Lebesgue integration partitions over
all tetrahedra for every N>0.  Genuine H1_0 closure implies zero input
outside the cube almost everywhere, and the output vanishes there
pointwise.  Consequently the proved h-order error is the actual
whole-space L2 error, not only a polynomial coefficient norm.
-/

open scoped BigOperators Topology
open MvPolynomial MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshMeasurePartition
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.BoundaryBoxH1Estimate
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.StableVolumeInterpolation

noncomputable section

namespace FreudenthalSVLean.VolumeInterpolationL2

set_option backward.isDefEq.respectTransparency false

theorem cube_integral_eq_element_sum {N : ℕ} (hN : 0 < N) {F : Space → ℝ}
    (hi : Integrable F) :
    (∫ x in cube, F x) = ∑ t : Tet N, ∫ x in tetrahedron t, F x := by
  have ht := integral_iUnion_ae
    (fun t : Tet N => (tetrahedron_isCompact hN t).measurableSet.nullMeasurableSet)
    (tetrahedra_pairwise_aeDisjoint hN) (hi.integrableOn (s := ⋃ t : Tet N, tetrahedron t))
  simpa only [tetrahedra_union_cube N hN, tsum_fintype] using ht

def residualValueDensity {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) (x : Space) : ℝ :=
  ∑ j : Fin 3,
    ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2

theorem residualValueDensity_integrable {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    Integrable (residualValueDensity hN v) := by
  apply integrable_finsetSum
  intro j _
  simpa only [Pi.sub_apply] using!
    ((smoothH1Space_value_memLp (v j)).sub
      (velocityFunction_memLp hN (volumeNodalInterpolation hN v) j)).integrable_sq

theorem interpolationError_eq_cube_integral {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space) :
    interpolationError hN v = ∫ x in cube, residualValueDensity hN v x := by
  rw [cube_integral_eq_element_sum hN (residualValueDensity_integrable hN v)]
  unfold interpolationError
  apply Finset.sum_congr rfl
  intro t _
  have hi (j : Fin 3) : IntegrableOn
      (fun x => ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2)
      (tetrahedron t) := by
    simpa only [Pi.sub_apply] using!
      (((smoothH1Space_value_memLp (v j)).sub
        (velocityFunction_memLp hN (volumeNodalInterpolation hN v) j)).integrable_sq).integrableOn
  change (∑ j : Fin 3, ∫ x in tetrahedron t,
    ((v j).val.1 x - eval x ((volumeNodalInterpolation hN v).val t j)) ^ 2) =
      ∫ x in tetrahedron t, ∑ j : Fin 3,
        ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  apply setIntegral_congr_fun (tetrahedron_isCompact hN t).measurableSet
  intro x hx
  change ((v j).val.1 x - eval x ((volumeNodalInterpolation hN v).val t j)) ^ 2 =
    ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2
  rw [velocityFunction_on_element hN _ t x hx j]

theorem residualValueDensity_zero_off_cube {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    residualValueDensity hN v =ᵐ[volume.restrict cubeᶜ] (0 : Space → ℝ) := by
  have hinput (j : Fin 3) : (v j).val.1 =ᵐ[volume.restrict cubeᶜ] (0 : Space → ℝ) :=
    inH1ZeroCube_zero_on_set (hv j) (compl_subset_compl.mpr openCube_subset_cube)
  have hall : ∀ᵐ x : Space ∂volume.restrict cubeᶜ, ∀ j : Fin 3, (v j).val.1 x = 0 := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [hinput j] with x hx
    exact hx
  filter_upwards [hall, ae_restrict_mem (measurableSet_Icc.compl : MeasurableSet cubeᶜ)] with x hi hx
  apply Finset.sum_eq_zero
  intro j _
  rw [hi j, velocityFunction_zero_off_cube hN _ j x hx]
  norm_num

theorem interpolationError_eq_global_integral {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    interpolationError hN v = ∫ x, residualValueDensity hN v x := by
  have hz : (∫ x in cubeᶜ, residualValueDensity hN v x) = 0 := by
    calc
      _ = ∫ _x in cubeᶜ, (0 : ℝ) :=
        integral_congr_ae (residualValueDensity_zero_off_cube hN v hv)
      _ = 0 := integral_zero _ _
  have he := integral_add_compl (s := cube) (measurableSet_Icc : MeasurableSet cube)
    (residualValueDensity_integrable hN v)
  rw [hz, add_zero] at he
  exact (interpolationError_eq_cube_integral hN v).trans he

theorem actual_L2_interpolation_error_bound {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    (∫ x, ∑ j : Fin 3,
      ((v j).val.1 x - velocityFunction hN (volumeNodalInterpolation hN v) j x) ^ 2) ≤
              995328 * (meshScale N) ^ 2 * inputGradientEnergy v := by
  change (∫ x, residualValueDensity hN v x) ≤ _
  rw [← interpolationError_eq_global_integral hN v hv]
  exact volumeNodalInterpolation_error_bound hN v hv

end FreudenthalSVLean.VolumeInterpolationL2
