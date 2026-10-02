import FreudenthalSVLean.GlobalMeanPreservingEdgeLift
import FreudenthalSVLean.GlobalSkeletonLift

/-!
# Uniform skeleton lifting preserving every actual element mean

For manuscript Proposition `skeleton` and the main proof's vertex/edge
stages, the actual stable vertex lift and mean-preserving global edge lift
compose on the exact pressure image.  The resulting fixed linear map
matches all full element-edge restrictions and has zero genuine divergence
mean on every element.  Its pressure residual stays in the exact image,
vanishes on every full edge, and preserves the input element means.
The theorem covers `N >= 2`; the initial stable mean lift and the global
element-bubble assembly remain separate obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.GlobalVertexLift
open FreudenthalSVLean.GlobalSkeletonLift
open FreudenthalSVLean.GlobalMeanPreservingEdgeLift
open FreudenthalSVLean.DivergenceEnergy

noncomputable section

namespace FreudenthalSVLean.MeanPreservingSkeletonLift

set_option backward.isDefEq.respectTransparency false

structure MeanPreservingSkeletonSpec {N k : ℕ} (hN : 0 < N)
    (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop extends SkeletonSpec R C where
  means_zero : ∀ q, elementMeans hN k (R q) = 0

theorem skeletonLift_spec {N k : ℕ} (hN : 0 < N)
    (V : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hV : ∀ q t a, eval (vertex t a) (divergence N (V q).val t) = eval (vertex t a) (q.val t))
    (hVm : ∀ q t, tetIntegral hN t (divergence N (V q).val t) = 0)
    (E : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (A B : ℝ) (hB : 0 ≤ B)
    (hVe : ∀ q, velocityEnergy (V q).val ≤ A * pressureEnergy q.val)
    (hE : GlobalMeanPreservingSpec hN E B) :
    MeanPreservingSkeletonSpec hN (skeletonLift V hV E) (2 * (A + B * (2 + 6 * A))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro q t a b hab s
    rw [skeletonLift_val, map_add]
    simp only [Pi.add_apply, map_add]
    rw [hE.match_edges _ t a b hab s, vertexResidual_val]
    simp only [Pi.sub_apply, map_sub]
    ring
  · intro q
    rw [skeletonLift_val]
    have hs := StableCanonicalEdgeLift.add_energy_bound hN (V q).val (E (vertexResidual V hV q)).val
    have hv := hVe q
    have he := hE.energy (vertexResidual V hV q)
    have hr := mul_le_mul_of_nonneg_left (vertexResidual_energy hN V hV A hVe q) hB
    nlinarith
  · intro q
    funext t
    rw [elementMeans_apply, skeletonLift_val]
    simp only [map_add, Pi.add_apply]
    rw [hVm q t]
    exact zero_add (tetIntegral hN t (divergence N (E (vertexResidual V hV q)).val t)) |>.trans
      (congrFun (hE.means_zero (vertexResidual V hV q)) t)

theorem residual_element_mean {N k : ℕ} (hN : 0 < N)
    (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : MeanPreservingSkeletonSpec hN R C) (q : pressureSpace N k) (t : Tet N) :
    tetIntegral hN t ((pressureResidual R q).val t) = tetIntegral hN t (q.val t) := by
  rw [pressureResidual_val]
  simp only [Pi.sub_apply, map_sub]
  have hm := congrFun (hR.means_zero q) t
  change tetIntegral hN t (divergence N (R q).val t) = 0 at hm
  rw [hm, sub_zero]

/-- Actual fixed linear quartic/quintic mean-preserving skeleton lifts,
with the common positive energy constant chosen before every mesh. -/
theorem uniform_mean_preserving_skeleton_stage : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ (R₄ : pressureSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : pressureSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        MeanPreservingSkeletonSpec (by omega) R₄ C ∧ MeanPreservingSkeletonSpec (by omega) R₅ C := by
  obtain ⟨A, hA, hV₄⟩ := vertex_stage 4 (by norm_num)
  obtain ⟨B, hB, hV₅⟩ := vertex_stage 5 (by norm_num)
  obtain ⟨D, hD, hE⟩ := uniform_global_mean_preserving_edge_stage
  let C := 2 * ((A + B) + D * (2 + 6 * (A + B)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN
  obtain ⟨V₄, hv₄, hvm₄, hve₄⟩ := hV₄ N (by omega)
  obtain ⟨V₅, hv₅, hvm₅, hve₅⟩ := hV₅ N (by omega)
  obtain ⟨E₄, E₅, he₄, he₅⟩ := hE N hN
  have hb₄ (q : pressureSpace N 4) : velocityEnergy (V₄ q).val ≤
      (A + B) * pressureEnergy q.val :=
    (hve₄ q).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le)
      (pressureEnergy_nonneg q.val))
  have hb₅ (q : pressureSpace N 5) : velocityEnergy (V₅ q).val ≤
      (A + B) * pressureEnergy q.val :=
    (hve₅ q).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le)
      (pressureEnergy_nonneg q.val))
  exact ⟨skeletonLift V₄ hv₄ E₄, skeletonLift V₅ hv₅ E₅,
    skeletonLift_spec (by omega) V₄ hv₄ hvm₄ E₄ (A + B) D hD.le hb₄ he₄,
    skeletonLift_spec (by omega) V₅ hv₅ hvm₅ E₅ (A + B) D hD.le hb₅ he₅⟩

end FreudenthalSVLean.MeanPreservingSkeletonLift
