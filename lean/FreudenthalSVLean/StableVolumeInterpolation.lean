import FreudenthalSVLean.InterpolationBoxOverlap
import FreudenthalSVLean.VelocityEnergy

/-!
# Uniformly stable actual volume-averaging interpolation

For manuscript Lemma `means` and equation `SZ`, the fixed linear volume
nodal interpolant takes actual weak H1_0 vector data to the actual
homogeneous conforming P1 velocity space.  The proved local estimates
and the all-N pointwise overlap bound give genuine gradient energy
stability and a meshwise actual L2 error of order h.  The constants
373248 and 995328 are chosen before N, and the single linear map before
its input.  No finite rank certificate or imported interpolation theorem
is used.  Divergence means still require the face-flux correction, and
the continuous divergence inverse remains a separate obligation.
-/

open scoped BigOperators Topology
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.LocalVolumeInterpolation
open FreudenthalSVLean.InterpolationBoxOverlap
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableVolumeInterpolation

set_option backward.isDefEq.respectTransparency false

def inputGradientEnergy (v : Fin 3 → smoothH1Space) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2

def interpolationError {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) : ℝ :=
  ∑ t : Tet N, ∑ j : Fin 3, ∫ x in tetrahedron t,
    ((v j).val.1 x - eval x ((volumeNodalInterpolation hN v).val t j)) ^ 2

theorem volumeNodalInterpolation_gradient_bound {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    velocityEnergy (volumeNodalInterpolation hN v).val ≤ 373248 * inputGradientEnergy v := by
  have hΓ (j : Fin 3) : (∑ t : Tet N, localGradientIntegral (v j).val.2 t) ≤
      1296 * ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2 :=
    local_gradient_sum_bound hN (fun i => ((hv j).1.2 i).1)
  calc
    _ = ∑ t : Tet N, ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x in tetrahedron t, (eval x (pderiv i (scalarInterpolation (v j).val.1 t))) ^ 2 := by
      rw [velocityEnergy_eq_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [localEnergy_eq_sum hN]
      simp only [volumeInterpolation_scalar hN]
    _ ≤ ∑ t : Tet N, ∑ j : Fin 3, 288 * localGradientIntegral (v j).val.2 t :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum
        (fun j _ => local_interpolation_gradient_bound hN (hv j) t))
    _ = 288 * ∑ j : Fin 3, ∑ t : Tet N, localGradientIntegral (v j).val.2 t := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ 288 * ∑ j : Fin 3, 1296 * ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hΓ j)) (by norm_num)
    _ = _ := by
      simp only [← Finset.mul_sum, inputGradientEnergy]
      ring

theorem volumeNodalInterpolation_error_bound {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    interpolationError hN v ≤ 995328 * (meshScale N) ^ 2 * inputGradientEnergy v := by
  have hΓ (j : Fin 3) : (∑ t : Tet N, localGradientIntegral (v j).val.2 t) ≤
      1296 * ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2 :=
    local_gradient_sum_bound hN (fun i => ((hv j).1.2 i).1)
  calc
    _ = ∑ t : Tet N, ∑ j : Fin 3, ∫ x in tetrahedron t,
        ((v j).val.1 x - eval x (scalarInterpolation (v j).val.1 t)) ^ 2 := by
      simp only [interpolationError, volumeInterpolation_scalar hN]
    _ ≤ ∑ t : Tet N, ∑ j : Fin 3,
        768 * (meshScale N) ^ 2 * localGradientIntegral (v j).val.2 t :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum
        (fun j _ => local_interpolation_error_bound hN (hv j) t))
    _ = (768 * (meshScale N) ^ 2) *
        ∑ j : Fin 3, ∑ t : Tet N, localGradientIntegral (v j).val.2 t := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ (768 * (meshScale N) ^ 2) *
        ∑ j : Fin 3, 1296 * ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hΓ j)) (by positivity)
    _ = _ := by
      simp only [← Finset.mul_sum, inputGradientEnergy]
      ring

/-- Constants precede every mesh and each fixed linear interpolation operator. -/
theorem uniform_volume_interpolation :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ N : ℕ, 0 < N →
      ∃ J : (Fin 3 → smoothH1Space) →ₗ[ℝ] velocitySpace N 1,
        ∀ v : Fin 3 → smoothH1Space,
          (∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) →
          velocityEnergy (J v).val ≤ A * inputGradientEnergy v ∧
          (∑ t : Tet N, ∑ j : Fin 3, ∫ x in tetrahedron t,
            ((v j).val.1 x - eval x ((J v).val t j)) ^ 2) ≤
              B * (meshScale N) ^ 2 * inputGradientEnergy v := by
  refine ⟨373248, 995328, by norm_num, by norm_num, ?_⟩
  intro N hN
  exact ⟨volumeNodalInterpolation hN, fun v hv =>
    ⟨volumeNodalInterpolation_gradient_bound hN v hv, volumeNodalInterpolation_error_bound hN v hv⟩⟩

end FreudenthalSVLean.StableVolumeInterpolation
