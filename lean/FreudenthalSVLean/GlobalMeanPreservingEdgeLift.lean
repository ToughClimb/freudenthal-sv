import FreudenthalSVLean.MeanPreservingEdgeLift
import FreudenthalSVLean.EdgeRoutingOverlap
import FreudenthalSVLean.GlobalEdgeLift

/-!
# Uniform simultaneous mean-preserving edge correction

For manuscript Proposition `edge`, the mean-preserving local quartic and
quintic edge maps are summed over the actual mesh edges.  Exact six-fold
pressure incidence counting and the proved 875-fold routing-neighborhood
overlap give a uniform actual gradient-energy bound.  Every actual element
mean is zero, while all full edge traces are matched simultaneously.
This theorem covers every `N >= 2`; it is not the final divergence inverse.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.EdgeAssemblyGeometry
open FreudenthalSVLean.GlobalEdgeLift
open FreudenthalSVLean.MeanPreservingEdgeLift
open FreudenthalSVLean.EdgeRoutingOverlap
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.BoundedOverlapEnergy

noncomputable section

namespace FreudenthalSVLean.GlobalMeanPreservingEdgeLift

set_option backward.isDefEq.respectTransparency false

theorem correction_vertex_zero {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C)
    (q : vertexZeroSpace N k) (t : Tet N) (a : Fin 4) :
    eval (vertex t a) (divergence N (edgeCorrection R q).val t) = 0 := by
  simp only [edgeCorrection_val, map_sum, Finset.sum_apply,
    (hR _).vertex_zero q t a, Finset.sum_const_zero]

theorem correction_means_zero {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C) (q : vertexZeroSpace N k) :
    elementMeans hN k (edgeCorrection R q) = 0 := by
  simp only [edgeCorrection, LinearMap.sum_apply, map_sum, (hR _).means_zero q,
    Finset.sum_const_zero]

theorem correction_local_edge {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C)
    (q : vertexZeroSpace N k) (t : Tet N) (lm : LocalEdge) (s : ℝ) :
    eval (segmentPoint (vertex t lm.val.1) (vertex t lm.val.2) s)
      (divergence N (edgeCorrection R q).val t) =
    eval (segmentPoint (vertex t lm.val.1) (vertex t lm.val.2) s) (q.val t) := by
  rw [edgeCorrection_val, map_sum]
  simp only [Finset.sum_apply, map_sum]
  rw [Finset.sum_eq_single (localMeshEdge t lm)]
  · have he := (hR (localMeshEdge t lm)).match_trace q (localIncidence t lm) s
    change eval (segmentPoint (gridPoint (gridVertexOfTet t lm.val.1))
      (gridPoint (gridVertexOfTet t lm.val.2)) s)
      (divergence N (R (localMeshEdge t lm) q).val t) =
      eval (segmentPoint (gridPoint (gridVertexOfTet t lm.val.1))
        (gridPoint (gridVertexOfTet t lm.val.2)) s) (q.val t) at he
    simpa only [gridVertexOfTet_point] using he
  · intro e _ he
    apply (hR e).protect_edges q t lm.val.1 lm.val.2
      (fun h => lm.property.ne (congrArg Fin.val h)) _ s
    intro hp
    exact he (meshEdge_pair_injective e (localMeshEdge t lm) hp.symm)
  · simp

theorem correction_edge {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C)
    (q : vertexZeroSpace N k) (t : Tet N) (a b : Fin 4) (hab : a ≠ b) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N (edgeCorrection R q).val t) =
      eval (segmentPoint (vertex t a) (vertex t b) s) (q.val t) := by
  by_cases ho : a.val < b.val
  · exact correction_local_edge hN R C hR q t ⟨(a, b), ho⟩ s
  · have ho' : b.val < a.val := by
      have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    have he := correction_local_edge hN R C hR q t ⟨(b, a), ho'⟩ (1 - s)
    simpa only [segment_swap] using he

theorem correction_energy {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C) (q : vertexZeroSpace N k) :
    velocityEnergy (edgeCorrection R q).val ≤ (875 * (6 * C)) * pressureEnergy q.val := by
  classical
  have hlocal (t : Tet N) : ∃ F : Finset (MeshEdge N),
      F ⊆ Finset.univ ∧ (F.card : ℝ) ≤ 875 ∧
        ∀ e ∈ (Finset.univ : Finset (MeshEdge N)), e ∉ F → (R e q).val t = 0 := by
    refine ⟨nearBoxEdges hN t, Finset.subset_univ _, by exact_mod_cast nearBoxEdges_card hN t, ?_⟩
    intro e _ he
    exact (hR e).support q t (fun h => he ((nearBoxEdges_iff hN t e).mpr h))
  rw [edgeCorrection_val]
  calc
    _ ≤ 875 * ∑ e : MeshEdge N, velocityEnergy (R e q).val :=
      velocityEnergy_sum_overlap hN Finset.univ (fun e => (R e q).val) 875 (by norm_num) hlocal
    _ ≤ 875 * ∑ e : MeshEdge N, C * starPressureEnergy e.val.1 e.val.2 q.val := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun e _ => (hR e).energy q)
    _ = _ := by rw [← Finset.mul_sum, edge_star_energy_sum]; ring

structure GlobalMeanPreservingSpec {N k : ℕ} (hN : 0 < N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  match_edges : ∀ q t a b, a ≠ b → ∀ s,
    eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N (R q).val t) =
      eval (segmentPoint (vertex t a) (vertex t b) s) (q.val t)
  vertex_zero : ∀ q t a, eval (vertex t a) (divergence N (R q).val t) = 0
  means_zero : ∀ q, elementMeans hN k (R q) = 0
  energy : ∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val

theorem edgeCorrection_spec {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e, MeanPreservingSpec hN e (R e) C) :
    GlobalMeanPreservingSpec hN (edgeCorrection R) (875 * (6 * C)) :=
  ⟨correction_edge hN R C hR, correction_vertex_zero hN R C hR,
    correction_means_zero hN R C hR, correction_energy hN R C hR⟩

/-- The full actual mean-preserving edge stage in both degrees, with one
constant before every admissible mesh and one fixed global linear map. -/
theorem uniform_global_mean_preserving_edge_stage : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        GlobalMeanPreservingSpec (by omega) R₄ C ∧ GlobalMeanPreservingSpec (by omega) R₅ C := by
  obtain ⟨C, hC, hLift⟩ := uniform_mean_preserving_edge_stage
  refine ⟨875 * (6 * C), by positivity, ?_⟩
  intro N hN
  have hex (e : MeshEdge N) :
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        MeanPreservingSpec (by omega) e R₄ C ∧ MeanPreservingSpec (by omega) e R₅ C := hLift N hN e
  choose R₄ R₅ h₄ h₅ using hex
  exact ⟨edgeCorrection R₄, edgeCorrection R₅,
    edgeCorrection_spec (by omega) R₄ C h₄, edgeCorrection_spec (by omega) R₅ C h₅⟩

end FreudenthalSVLean.GlobalMeanPreservingEdgeLift
