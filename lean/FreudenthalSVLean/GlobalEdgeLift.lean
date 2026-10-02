import FreudenthalSVLean.EdgeAssemblyGeometry
import FreudenthalSVLean.BoundedOverlapEnergy

/-!
# Global uniform edge-jet correction for degrees four and five

For the manuscript's edge-stage assembly, each increasing mesh edge is
processed once by a fixed linear local lift.  Other-edge protection makes
the full sum match every edge polynomial simultaneously.  All vertex
gradients remain zero.  The actual integral energy bound follows from
the proved fifty-six-fold endpoint-star overlap and exact six-fold
pressure incidence identity, not from the total number of mesh edges.

This is the edge correction prior to element-mean adjustment.  The
uniform divergence right inverse and the Sobolev interpretation remain
separate theorems, not consequences asserted by this module.
-/

open scoped BigOperators Classical
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.EdgePressureData
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.UniformEdgeLift
open FreudenthalSVLean.EdgeAssemblyGeometry
open FreudenthalSVLean.BoundedOverlapEnergy

noncomputable section

namespace FreudenthalSVLean.GlobalEdgeLift

set_option backward.isDefEq.respectTransparency false

def edgeCorrection {N k : ℕ}
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) :
    vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k := ∑ e : MeshEdge N, R e

theorem edgeCorrection_val {N k : ℕ}
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (q : vertexZeroSpace N k) :
    (edgeCorrection R q).val = ∑ e : MeshEdge N, (R e q).val := by
  simp only [edgeCorrection, LinearMap.sum_apply, Submodule.coe_sum]

theorem correction_vertex {N k : ℕ}
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e : MeshEdge N, EdgeLiftSpec e.val.1 e.val.2 (R e) C)
    (q : vertexZeroSpace N k) (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((edgeCorrection R q).val t j)) = 0 := by
  simp only [edgeCorrection_val, Finset.sum_apply, map_sum,
    (hR _).vertex_gradient q t l i j, Finset.sum_const_zero]

theorem correction_local_edge {N k : ℕ}
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e : MeshEdge N, EdgeLiftSpec e.val.1 e.val.2 (R e) C)
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

theorem segment_swap (x y : ChainMeasureTransport.Space) (s : ℝ) :
    segmentPoint y x (1 - s) = segmentPoint x y s := by
  funext j
  simp only [segmentPoint]
  ring

theorem correction_edge {N k : ℕ}
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : ∀ e : MeshEdge N, EdgeLiftSpec e.val.1 e.val.2 (R e) C)
    (q : vertexZeroSpace N k) (t : Tet N) (l m : Vertex) (hlm : l ≠ m) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s) (divergence N (edgeCorrection R q).val t) =
      eval (segmentPoint (vertex t l) (vertex t m) s) (q.val t) := by
  by_cases horder : l.val < m.val
  · exact correction_local_edge R C hR q t ⟨(l, m), horder⟩ s
  · have horder' : m.val < l.val := by
      have hn : l.val ≠ m.val := fun h => hlm (Fin.ext h)
      omega
    have he := correction_local_edge R C hR q t ⟨(m, l), horder'⟩ (1 - s)
    simpa only [segment_swap] using he

theorem correction_energy {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) (_hC : 0 ≤ C)
    (hR : ∀ e : MeshEdge N, EdgeLiftSpec e.val.1 e.val.2 (R e) C)
    (q : vertexZeroSpace N k) :
    velocityEnergy (edgeCorrection R q).val ≤ (56 * (6 * C)) * pressureEnergy q.val := by
  have hlocal (t : Tet N) : ∃ F : Finset (MeshEdge N),
      F ⊆ Finset.univ ∧ (F.card : ℝ) ≤ 56 ∧
        ∀ e ∈ (Finset.univ : Finset (MeshEdge N)), e ∉ F → (R e q).val t = 0 := by
    refine ⟨nearTet t, Finset.subset_univ _, by exact_mod_cast nearTet_card t, ?_⟩
    intro e _ he
    apply (hR e).off_endpoints q t
    intro l
    constructor
    · intro hl
      exact he ((nearTet_iff t e).mpr ⟨l, Or.inl hl⟩)
    · intro hl
      exact he ((nearTet_iff t e).mpr ⟨l, Or.inr hl⟩)
  rw [edgeCorrection_val]
  calc
    _ ≤ 56 * ∑ e : MeshEdge N, velocityEnergy (R e q).val :=
      velocityEnergy_sum_overlap hN Finset.univ (fun e => (R e q).val) 56 (by norm_num) hlocal
    _ ≤ 56 * ∑ e : MeshEdge N, C * starPressureEnergy e.val.1 e.val.2 q.val := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun e _ => (hR e).energy_bound q)
    _ = _ := by rw [← Finset.mul_sum, edge_star_energy_sum]; ring

structure GlobalEdgeSpec {N k : ℕ} (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k)
    (C : ℝ) : Prop where
  match_edges : ∀ (q : vertexZeroSpace N k) (t : Tet N) (l m : Vertex), l ≠ m → ∀ s : ℝ,
    eval (segmentPoint (vertex t l) (vertex t m) s) (divergence N (R q).val t) =
      eval (segmentPoint (vertex t l) (vertex t m) s) (q.val t)
  vertex_gradient : ∀ (q : vertexZeroSpace N k) (t : Tet N) (l : Vertex) (i j : Coordinate),
    eval (vertex t l) (pderiv i ((R q).val t j)) = 0
  energy_bound : ∀ q : vertexZeroSpace N k, velocityEnergy (R q).val ≤ C * pressureEnergy q.val

theorem edgeCorrection_spec {N k : ℕ} (hN : 0 < N)
    (R : MeshEdge N → vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ e : MeshEdge N, EdgeLiftSpec e.val.1 e.val.2 (R e) C) :
    GlobalEdgeSpec (edgeCorrection R) (56 * (6 * C)) :=
  ⟨correction_edge R C hR, correction_vertex R C hR, correction_energy hN R C hC hR⟩

/-- One fixed global linear map in each degree corrects every actual edge
trace of a vertex-zero divergence-image pressure with a uniform bound. -/
theorem uniform_global_edge_stage : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N),
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        GlobalEdgeSpec R₄ C ∧ GlobalEdgeSpec R₅ C := by
  obtain ⟨C, hC, hLift⟩ := uniform_edge_lifts
  refine ⟨56 * (6 * C), by positivity, ?_⟩
  intro N hN
  have hex (e : MeshEdge N) :
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        EdgeLiftSpec e.val.1 e.val.2 R₄ C ∧ EdgeLiftSpec e.val.1 e.val.2 R₅ C :=
    hLift N hN e.val.1 e.val.2 e.property.1 (Classical.choice e.property.2.2)
  choose R₄ R₅ h₄ h₅ using hex
  exact ⟨edgeCorrection R₄, edgeCorrection R₅,
    edgeCorrection_spec hN R₄ C hC.le h₄, edgeCorrection_spec hN R₅ C hC.le h₅⟩

end FreudenthalSVLean.GlobalEdgeLift
