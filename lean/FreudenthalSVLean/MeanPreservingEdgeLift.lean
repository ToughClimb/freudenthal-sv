import FreudenthalSVLean.ZeroTotalEdgeLift
import FreudenthalSVLean.ClusterMeanRemoval
import FreudenthalSVLean.EdgeRoutingBox

/-!
# Uniform mean-preserving actual quartic and quintic edge lifts

For manuscript Proposition `edge`, the proved zero-total-mean identity of
each actual edge lift is supplied to the fixed 27-cube router.  The resulting
operator preserves all desired edge restrictions, protects every other
edge and vertex divergence, has zero actual divergence mean on each
element and is uniformly stable.  The routing box and linear operator are
chosen before the input pressure.  This local theorem covers `N >= 2`;
the remaining single-cube case belongs to the global small-mesh argument.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.EdgePressureData
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.UniformEdgeLift
open FreudenthalSVLean.ZeroTotalEdgeLift
open FreudenthalSVLean.EdgeAssemblyGeometry
open FreudenthalSVLean.EdgeRoutingBox
open FreudenthalSVLean.RectangularCubeCluster
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.ClusterMeanRemoval
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.DivergenceMean

noncomputable section

namespace FreudenthalSVLean.MeanPreservingEdgeLift

set_option backward.isDefEq.respectTransparency false

def localizedMap {N k : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : EdgeLiftSpec e.val.1 e.val.2 R C) (hM : ∀ q, totalMean hN (R q).val = 0) :
    vertexZeroSpace N k →ₗ[ℝ] localSpace hN (cells (edgeBox hN e)) k :=
  R.codRestrict _ (fun q => by
    constructor
    · intro t ht
      obtain ⟨ha, hb⟩ := off_box_has_no_endpoints hN e t ht
      exact hR.off_endpoints q t (fun l => ⟨ha l, hb l⟩)
    · rw [elementMeans_sum, hM q])

def correctedMap {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k) (e : MeshEdge N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : EdgeLiftSpec e.val.1 e.val.2 R C) (hM : ∀ q, totalMean (by omega) (R q).val = 0) :
    vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k :=
  (meanFreeLift hN hk (cells (edgeBox (by omega) e)) (edgeBox_connected (by omega) e)).comp
    (localizedMap (by omega) e R C hR hM)

theorem correctedMap_preserves_local_edges {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k)
    (e : MeshEdge N) (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (hR : EdgeLiftSpec e.val.1 e.val.2 R C) (hM : ∀ q, totalMean (by omega) (R q).val = 0)
    (q : vertexZeroSpace N k) (t : Tet N) (a b : Fin 4) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (correctedMap hN hk e R C hR hM q).val t) =
    eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N (R q).val t) := by
  exact meanFreeLift_preserves_edges hN hk _ _ (localizedMap (by omega) e R C hR hM q) t a b s

structure MeanPreservingSpec {N k : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  match_trace : ∀ q x s, pressureTrace e.val.1 e.val.2 s (divergence N (R q).val) x =
    pressureTrace e.val.1 e.val.2 s q.val x
  vertex_zero : ∀ q t a, eval (vertex t a) (divergence N (R q).val t) = 0
  protect_edges : ∀ q t a b, a ≠ b →
    ({gridVertexOfTet t a, gridVertexOfTet t b} : Finset (GridVertex N)) ≠ {e.val.1, e.val.2} →
      ∀ s, eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N (R q).val t) = 0
  means_zero : ∀ q, elementMeans hN k (R q) = 0
  energy : ∀ q, velocityEnergy (R q).val ≤ C * starPressureEnergy e.val.1 e.val.2 q.val
  support : ∀ q t, ¬ nearCluster (cells (edgeBox hN e)) t → (R q).val t = 0

theorem correctedMap_spec {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k) (e : MeshEdge N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C D : ℝ)
    (hR : EdgeLiftSpec e.val.1 e.val.2 R C) (hM : ∀ q, totalMean (by omega) (R q).val = 0)
    (hD : 0 ≤ D)
    (hE : ∀ v : localSpace (by omega) (cells (edgeBox (by omega) e)) k,
      velocityEnergy (meanFreeLift hN hk _ (edgeBox_connected (by omega) e) v).val ≤
        D * velocityEnergy v.val.val) :
    MeanPreservingSpec (by omega) e (correctedMap hN hk e R C hR hM) (D * C) := by
  constructor
  · intro q x s
    have he := correctedMap_preserves_local_edges hN hk e R C hR hM q
      x.val.1.val.1 x.val.1.val.2 x.val.2 s
    rw [first_physical_endpoint e.val.1 e.val.2 x,
      second_physical_endpoint e.val.1 e.val.2 x] at he
    exact he.trans (hR.match_trace q x s)
  · intro q t a
    have he := correctedMap_preserves_local_edges hN hk e R C hR hM q t a a 0
    have hp : segmentPoint (vertex t a) (vertex t a) (0 : ℝ) = vertex t a := by
      funext j
      simp [ChainGeometry.segmentPoint]
    rw [hp] at he
    rw [he]
    change eval (vertex t a) (∑ j : Fin 3, pderiv j ((R q).val t j)) = 0
    simp only [map_sum, hR.vertex_gradient q t a, Finset.sum_const_zero]
  · intro q t a b hab he s
    rw [correctedMap_preserves_local_edges hN hk e R C hR hM q t a b s]
    exact hR.protect_edges q t a b hab he s
  · intro q
    exact meanFreeLift_means_zero hN hk _ _ (localizedMap (by omega) e R C hR hM q)
  · intro q
    calc
      _ ≤ D * velocityEnergy (R q).val := hE (localizedMap (by omega) e R C hR hM q)
      _ ≤ D * (C * starPressureEnergy e.val.1 e.val.2 q.val) :=
        mul_le_mul_of_nonneg_left (hR.energy_bound q) hD
      _ = _ := by ring
  · intro q t ht
    exact meanFreeLift_support hN hk _ _ (localizedMap (by omega) e R C hR hM q) t ht

/-- Complete actual mean-preserving local edge stage for both degrees,
with one constant before all mesh, edge and pressure quantifiers. -/
theorem uniform_mean_preserving_edge_stage : ∃ A : ℝ, 0 < A ∧
    ∀ (N : ℕ) (hN : 2 ≤ N) (e : MeshEdge N),
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        MeanPreservingSpec (by omega) e R₄ A ∧ MeanPreservingSpec (by omega) e R₅ A := by
  obtain ⟨C, hC, hRaw⟩ := uniform_zero_total_edge_lifts
  obtain ⟨D, hD, hRouter⟩ := meanFreeLift_uniform_energy 27
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro N hN e
  obtain ⟨R₄, R₅, h4, h5, hm4, hm5⟩ := hRaw N (by omega) e
  refine ⟨correctedMap hN (by norm_num) e R₄ C h4 hm4,
    correctedMap hN (by norm_num) e R₅ C h5 hm5, ?_, ?_⟩
  · exact correctedMap_spec hN (by norm_num) e R₄ C D h4 hm4 hD.le
      (hRouter N 4 hN (by norm_num) _ (edgeBox_connected (by omega) e) (edgeBox_card (by omega) e))
  · exact correctedMap_spec hN (by norm_num) e R₅ C D h5 hm5 hD.le
      (hRouter N 5 hN (by norm_num) _ (edgeBox_connected (by omega) e) (edgeBox_card (by omega) e))

end FreudenthalSVLean.MeanPreservingEdgeLift
