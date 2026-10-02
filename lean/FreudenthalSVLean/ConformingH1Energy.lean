import FreudenthalSVLean.SmoothCubePoincare
import FreudenthalSVLean.ZeroElementMeanRightInverse

/-!
# Complete physical H1 energy and uniform stability

For the manuscript's gradient-seminorm formulation and its equivalent
H1-stability statement, smooth approximation transports an explicit
cube Poincare bound to every actual conforming finite-element velocity.
Its genuine complete H1 energy is at most five times its genuine gradient
energy, uniformly in all meshes and degrees.  In particular, the proved
zero-element-mean quartic and quintic right inverses are uniformly stable
in this complete H1 energy.  This theorem does not discharge the initial
mean lift required by the unrestricted right inverse.
-/

open scoped BigOperators ContDiff Topology
open MvPolynomial MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.BoundedMeshFunctions
open FreudenthalSVLean.InteriorMollification
open FreudenthalSVLean.InteriorMollificationL2
open FreudenthalSVLean.SmoothCubePoincare
open FreudenthalSVLean.ZeroElementMeanRightInverse

noncomputable section

namespace FreudenthalSVLean.ConformingH1Energy

set_option backward.isDefEq.respectTransparency false

theorem smooth_value_energy_tendsto {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    Tendsto (fun n => ∫ x, (interiorMollify n (velocityFunction hN v j) x) ^ 2)
      atTop (𝓝 (∫ x, (velocityFunction hN v j x) ^ 2)) := by
  obtain ⟨M, hM, hb⟩ := velocityFunction_uniform_bound hN v j
  have hs : Function.support (velocityFunction hN v j) ⊆ cube := by
    intro x hx
    by_contra hc
    exact hx (velocityFunction_zero_off_cube hN v j x hc)
  simpa only [one_mul] using interior_scaled_square_integral_tendsto
    ((velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)) hM.le hb hs
    (Eventually.of_forall (fun _ => (velocityFunction_continuous hN v j).continuousAt))
    (fun _ => 1) tendsto_const_nhds (fun _ => by constructor <;> norm_num)

theorem smooth_gradient_energy_tendsto {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    Tendsto (fun n => ∫ x,
      (fderiv ℝ (interiorMollify n (velocityFunction hN v j)) x (Pi.single i 1)) ^ 2)
      atTop (𝓝 (∫ x, (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2)) := by
  obtain ⟨M, hM, hb⟩ := piecewisePressure_uniform_bound hN (fun t => pderiv i (v.val t j))
  have hf := (velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)
  simp only [interiorMollify_partial _ hf i (velocityFunction_hasWeakPartial hN v j i)]
  exact interior_scaled_square_integral_tendsto
    ((piecewisePressure_memLp hN _).locallyIntegrable (by norm_num)) hM.le hb
    (piecewisePressure_support_cube hN _) (piecewisePressure_ae_continuousAt hN _) factor
    factor_tendsto (fun n => ⟨(factor_pos n).le, factor_le_five n⟩)

theorem velocityFunction_poincare {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    (∫ x, (velocityFunction hN v j x) ^ 2) ≤
      4 * ∫ x, (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2 := by
  have hf := (velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)
  have hs : Function.support (velocityFunction hN v j) ⊆ cube := by
    intro x hx
    by_contra hc
    exact hx (velocityFunction_zero_off_cube hN v j x hc)
  apply le_of_tendsto_of_tendsto (smooth_value_energy_tendsto hN v j)
    ((smooth_gradient_energy_tendsto hN v j i).const_mul 4)
  apply Eventually.of_forall
  intro n
  exact smooth_cube_poincare (interiorMollify_contDiff n hf) (interiorMollify_hasCompactSupport n hs)
    ((interiorMollify_support_box n hs).trans (innerBox_subset_openCube n |>.trans openCube_subset_cube)) i

def h1Energy {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) : ℝ :=
  (∑ j : Fin 3, ∫ x, (velocityFunction hN v j x) ^ 2) + velocityEnergy v.val

theorem h1Energy_bound {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k) :
    h1Energy hN v ≤ 5 * velocityEnergy v.val := by
  have hj (j : Fin 3) : (∫ x, (velocityFunction hN v j x) ^ 2) ≤
      4 * ∑ i : Fin 3, ∫ x, (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2 := by
    exact (velocityFunction_poincare hN v j 0).trans
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ => integral_nonneg (fun _ => sq_nonneg _))
          (f := fun i : Fin 3 => ∫ x,
            (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2)
          (Finset.mem_univ (0 : Fin 3))) (by norm_num))
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [← Finset.mul_sum, velocityFunction_weak_gradient_energy hN v] at hs
  dsimp [h1Energy]
  linarith

theorem uniform_zero_element_mean_h1_inverse :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ (R₄ : zeroElementMeanSpace (by omega) 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : zeroElementMeanSpace (by omega) 5 →ₗ[ℝ] velocitySpace N 5),
        (∀ q, divergence N (R₄ q).val = q.val.val) ∧
        (∀ q, divergence N (R₅ q).val = q.val.val) ∧
        (∀ q, h1Energy (by omega) (R₄ q) ≤ C * pressureEnergy q.val.val) ∧
        (∀ q, h1Energy (by omega) (R₅ q) ≤ C * pressureEnergy q.val.val) := by
  obtain ⟨A, hA, hR⟩ := uniform_zero_element_mean_right_inverse
  refine ⟨5 * A, by positivity, fun N hN => ?_⟩
  obtain ⟨R₄, R₅, h4, h5⟩ := hR N hN
  refine ⟨R₄, R₅, h4.right_inverse, h5.right_inverse, fun q => ?_, fun q => ?_⟩
  · exact (h1Energy_bound (by omega) (R₄ q)).trans
      ((mul_le_mul_of_nonneg_left (h4.energy q) (by norm_num)).trans_eq (by ring))
  · exact (h1Energy_bound (by omega) (R₅ q)).trans
      ((mul_le_mul_of_nonneg_left (h5.energy q) (by norm_num)).trans_eq (by ring))

end FreudenthalSVLean.ConformingH1Energy
