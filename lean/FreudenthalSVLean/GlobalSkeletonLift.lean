import FreudenthalSVLean.GlobalVertexLift
import FreudenthalSVLean.GlobalEdgeLift
import FreudenthalSVLean.DivergenceEnergy

/-!
# Uniform combined vertex and edge skeleton lifting

For the manuscript's successive vertex and edge stages, this module
constructs one fixed linear map on the actual pressure image whose
divergence agrees with the input on every complete tetrahedral edge.
The vertex residual remains in the exact divergence image and vanishes
at every actual vertex.  Its actual pressure integral energy is bounded
using the proved divergence/gradient inequality, so composing the two
uniform stages does not introduce a mesh-dependent constant.

The element-mean adjustment, final element bubbles and weak Sobolev
interpretation are not asserted here.  The skeleton residual can still
have nonzero element means.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.GlobalVertexLift
open FreudenthalSVLean.GlobalEdgeLift
open FreudenthalSVLean.DivergenceEnergy

noncomputable section

namespace FreudenthalSVLean.GlobalSkeletonLift

set_option backward.isDefEq.respectTransparency false

def conformingDivergence (N k : ℕ) : velocitySpace N k →ₗ[ℝ] pressureSpace N k :=
  ((divergence N).comp (velocitySpace N k).subtype).codRestrict _
    (fun v => ⟨v.val, v.property, rfl⟩)

def pressureResidual {N k : ℕ} (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) :
    pressureSpace N k →ₗ[ℝ] pressureSpace N k :=
  LinearMap.id - (conformingDivergence N k).comp R

theorem pressureResidual_val {N k : ℕ} (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (q : pressureSpace N k) : (pressureResidual R q).val = q.val - divergence N (R q).val := rfl

def vertexResidual {N k : ℕ} (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hR : ∀ q t l, eval (vertex t l) (divergence N (R q).val t) = eval (vertex t l) (q.val t)) :
    pressureSpace N k →ₗ[ℝ] vertexZeroSpace N k :=
  ((pressureSpace N k).subtype.comp (pressureResidual R)).codRestrict _ (by
    intro q
    refine ⟨(pressureResidual R q).property, ?_⟩
    intro t l
    change eval (vertex t l) ((pressureResidual R q).val t) = 0
    rw [pressureResidual_val]
    simp only [Pi.sub_apply, map_sub, hR, sub_self])

theorem vertexResidual_val {N k : ℕ} (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hR : ∀ q t l, eval (vertex t l) (divergence N (R q).val t) = eval (vertex t l) (q.val t))
    (q : pressureSpace N k) : (vertexResidual R hR q).val = q.val - divergence N (R q).val := rfl

theorem vertexResidual_energy {N k : ℕ} (hN : 0 < N)
    (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hR : ∀ q t l, eval (vertex t l) (divergence N (R q).val t) = eval (vertex t l) (q.val t))
    (C : ℝ) (hb : ∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val)
    (q : pressureSpace N k) :
    pressureEnergy (vertexResidual R hR q).val ≤ (2 + 6 * C) * pressureEnergy q.val := by
  rw [vertexResidual_val]
  have hs := pressureEnergy_sub hN q.val (divergence N (R q).val)
  have hd := divergence_energy_bound hN (R q).val
  have hv := hb q
  nlinarith

def skeletonLift {N k : ℕ} (V : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hV : ∀ q t l, eval (vertex t l) (divergence N (V q).val t) = eval (vertex t l) (q.val t))
    (E : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) :
    pressureSpace N k →ₗ[ℝ] velocitySpace N k := V + E.comp (vertexResidual V hV)

theorem skeletonLift_val {N k : ℕ} (V : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hV : ∀ q t l, eval (vertex t l) (divergence N (V q).val t) = eval (vertex t l) (q.val t))
    (E : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (q : pressureSpace N k) :
    (skeletonLift V hV E q).val = (V q).val + (E (vertexResidual V hV q)).val := rfl

structure SkeletonSpec {N k : ℕ} (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  match_edges : ∀ (q : pressureSpace N k) (t : Tet N) (l m : Vertex), l ≠ m → ∀ s : ℝ,
    eval (segmentPoint (vertex t l) (vertex t m) s) (divergence N (R q).val t) =
      eval (segmentPoint (vertex t l) (vertex t m) s) (q.val t)
  energy_bound : ∀ q : pressureSpace N k, velocityEnergy (R q).val ≤ C * pressureEnergy q.val

theorem skeletonLift_spec {N k : ℕ} (hN : 0 < N)
    (V : pressureSpace N k →ₗ[ℝ] velocitySpace N k)
    (hV : ∀ q t l, eval (vertex t l) (divergence N (V q).val t) = eval (vertex t l) (q.val t))
    (E : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (A B : ℝ) (hB : 0 ≤ B)
    (hVe : ∀ q, velocityEnergy (V q).val ≤ A * pressureEnergy q.val)
    (hE : GlobalEdgeSpec E B) :
    SkeletonSpec (skeletonLift V hV E) (2 * (A + B * (2 + 6 * A))) := by
  constructor
  · intro q t l m hlm s
    rw [skeletonLift_val, map_add]
    simp only [Pi.add_apply, map_add]
    rw [hE.match_edges _ t l m hlm s, vertexResidual_val]
    simp only [Pi.sub_apply, map_sub]
    ring
  · intro q
    rw [skeletonLift_val]
    have hs := StableCanonicalEdgeLift.add_energy_bound hN (V q).val (E (vertexResidual V hV q)).val
    have hv := hVe q
    have he := hE.energy_bound (vertexResidual V hV q)
    have hr := mul_le_mul_of_nonneg_left (vertexResidual_energy hN V hV A hVe q) hB
    nlinarith

theorem skeleton_residual_zero_edge {N k : ℕ}
    (R : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) (hR : SkeletonSpec R C)
    (q : pressureSpace N k) (t : Tet N) (l m : Vertex) (hlm : l ≠ m) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s) ((pressureResidual R q).val t) = 0 := by
  rw [pressureResidual_val]
  simp only [Pi.sub_apply, map_sub, hR.match_edges q t l m hlm s, sub_self]

/-- Every mesh size has fixed quartic and quintic skeleton lifts with one
integral energy constant quantified before the mesh size. -/
theorem uniform_skeleton_stage : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_hN : 0 < N),
    ∃ (R₄ : pressureSpace N 4 →ₗ[ℝ] velocitySpace N 4)
      (R₅ : pressureSpace N 5 →ₗ[ℝ] velocitySpace N 5),
      SkeletonSpec R₄ C ∧ SkeletonSpec R₅ C := by
  obtain ⟨A, hA, hV₄⟩ := vertex_stage 4 (by norm_num)
  obtain ⟨B, hB, hV₅⟩ := vertex_stage 5 (by norm_num)
  obtain ⟨D, hD, hE⟩ := uniform_global_edge_stage
  let C := 2 * ((A + B) + D * (2 + 6 * (A + B)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN
  obtain ⟨V₄, hv₄, _, hve₄⟩ := hV₄ N hN
  obtain ⟨V₅, hv₅, _, hve₅⟩ := hV₅ N hN
  obtain ⟨E₄, E₅, he₄, he₅⟩ := hE N hN
  have hb₄ (q : pressureSpace N 4) : velocityEnergy (V₄ q).val ≤
      (A + B) * pressureEnergy q.val :=
    (hve₄ q).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (pressureEnergy_nonneg q.val))
  have hb₅ (q : pressureSpace N 5) : velocityEnergy (V₅ q).val ≤
      (A + B) * pressureEnergy q.val :=
    (hve₅ q).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (pressureEnergy_nonneg q.val))
  exact ⟨skeletonLift V₄ hv₄ E₄, skeletonLift V₅ hv₅ E₅,
    skeletonLift_spec hN V₄ hv₄ E₄ (A + B) D hD.le hb₄ he₄,
    skeletonLift_spec hN V₅ hv₅ E₅ (A + B) D hD.le hb₅ he₅⟩

end FreudenthalSVLean.GlobalSkeletonLift
