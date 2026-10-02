import FreudenthalSVLean.H1ZeroLinearity
import FreudenthalSVLean.SmoothCubePoincare
import FreudenthalSVLean.H1ApproximationL2
import FreudenthalSVLean.UniformMeanFortin
import FreudenthalSVLean.ConformingH1Energy

/-!
# Genuine full H1 energy on the weak H1_0 cube space

For the H1 interpretation of manuscript Lemma `means`, the explicit
cube Poincare bound is transported to every actual weak H1_0 function,
not only finite-element velocities. A single actual C-infinity
interior-supported approximation and genuine L2 convergence of its
values and derivatives yield the estimate. Full physical H1 energy of
the proved fixed mean Fortin operator is uniformly bounded as well.
This does not prove continuous divergence solvability.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.SmoothCubePoincare
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.StableVolumeInterpolation
open FreudenthalSVLean.UniformMeanFortin
open FreudenthalSVLean.ConformingH1Energy

noncomputable section

namespace FreudenthalSVLean.WeakH1ZeroCubeEnergy

set_option backward.isDefEq.respectTransparency false

theorem inH1ZeroCube_poincare {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) : (∫ x, (f x) ^ 2) ≤ 4 * ∫ x, (g i x) ^ 2 := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hl : Tendsto (fun n => ∫ x, (u n x) ^ 2) atTop (𝓝 (∫ x, (f x) ^ 2)) := by
    simpa only [setIntegral_univ] using smooth_value_local_square_integral_tendsto ha univ
  have hg : Tendsto (fun n => ∫ x, (fderiv ℝ (u n) x (Pi.single i 1)) ^ 2)
      atTop (𝓝 (∫ x, (g i x) ^ 2)) := by
    simpa only [setIntegral_univ] using smooth_gradient_local_square_integral_tendsto ha univ i
  apply le_of_tendsto_of_tendsto hl (hg.const_mul 4)
  apply Eventually.of_forall
  intro n
  exact smooth_cube_poincare (hu n).1 (hu n).2.1
    ((subset_tsupport (u n)).trans ((hu n).2.2.1.trans openCube_subset_cube)) i

theorem weak_full_h1_energy_bound {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) :
    (∫ x, (f x) ^ 2) + (∑ i : Fin 3, ∫ x, (g i x) ^ 2) ≤
      5 * ∑ i : Fin 3, ∫ x, (g i x) ^ 2 := by
  have hb := (inH1ZeroCube_poincare hf 0).trans
    (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun i _ => integral_nonneg (fun _ => sq_nonneg _))
        (s := Finset.univ) (f := fun i : Fin 3 => ∫ x, (g i x) ^ 2)
        (Finset.mem_univ (0 : Fin 3))) (by norm_num : (0 : ℝ) ≤ 4))
  linarith

def fullInputEnergy (v : Fin 3 → smoothH1Space) : ℝ :=
  (∑ j : Fin 3, ∫ x, ((v j).val.1 x) ^ 2) + inputGradientEnergy v

theorem fullInputEnergy_bound (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    fullInputEnergy v ≤ 5 * inputGradientEnergy v := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => weak_full_h1_energy_bound (hv j))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, fullInputEnergy, inputGradientEnergy] using ht

theorem meanFortin_full_h1_bound {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space)
    (hv : ∀ j : Fin 3, InH1ZeroCube (v j).val.1 (v j).val.2) :
    h1Energy hN (meanFortinLinear hN v) ≤ (5 * meanFortinConstant) * inputGradientEnergy v := by
  exact (h1Energy_bound hN (meanFortinLinear hN v)).trans
    ((mul_le_mul_of_nonneg_left (meanFortin_energy hN v hv) (by norm_num)).trans_eq (by ring))

def zeroMeanFortin {N : ℕ} (hN : 0 < N) :
    (Fin 3 → h1ZeroSpace) →ₗ[ℝ] velocitySpace N 3 :=
  (meanFortinLinear hN).comp (LinearMap.pi (fun j => smoothInclusion.comp (LinearMap.proj j)))

theorem zeroMeanFortin_energy {N : ℕ} (hN : 0 < N) (v : Fin 3 → h1ZeroSpace) :
    h1Energy hN (zeroMeanFortin hN v) ≤ (5 * meanFortinConstant) *
      (∑ j : Fin 3, ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2) :=
  meanFortin_full_h1_bound hN (fun j => smoothInclusion (v j)) (fun j => (v j).property)

end FreudenthalSVLean.WeakH1ZeroCubeEnergy
