import FreudenthalSVLean.CubeClusterGraph

/-!
# Fixed linear, edge-protecting mean routing on actual cube clusters

For manuscript Lemma `routing`, a face-connected cube cluster is fixed
before the mean data.  The constructed quartic velocity has exactly the
prescribed actual element means, zero means on all other elements, zero
divergence on every complete element edge, and polynomial support in the
fixed one-cube face neighborhood.  The subsequent stability module supplies
the genuine gradient-energy bound.
-/

open scoped BigOperators
open MvPolynomial SimpleGraph
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.MeanRoutingAlgebra

noncomputable section

namespace FreudenthalSVLean.CubeClusterRouting

set_option backward.isDefEq.respectTransparency false

/-- The protection and support conditions are linear subspace conditions
on the actual homogeneous quartic velocity space. -/
def protectedSpace {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) :
    Submodule ℝ (velocitySpace N 4) where
  carrier v :=
    (∀ t : Tet N, ¬ nearCluster C t → v.val t = 0) ∧
    (∀ (t : Tet N) (a b : Fin 4) (s : ℝ),
      eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N v.val t) = 0) ∧
    (∀ t : Tet N, t.1 ∉ C → elementMeans hN 4 v t = 0)
  zero_mem' := by constructor; · intros; rfl
                  constructor <;> intros <;> simp
  add_mem' := by
    intro v w hv hw
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      simp only [Submodule.coe_add, Pi.add_apply, hv.1 t ht, hw.1 t ht, add_zero]
    · intro t a b s
      simp only [Submodule.coe_add, map_add, Pi.add_apply, hv.2.1 t a b s,
        hw.2.1 t a b s, add_zero]
    · intro t ht
      simp only [map_add, Pi.add_apply, hv.2.2 t ht, hw.2.2 t ht, add_zero]
  smul_mem' := by
    intro c v hv
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      simp only [Submodule.coe_smul, Pi.smul_apply, hv.1 t ht, smul_zero]
    · intro t a b s
      simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_C_mul, map_mul,
        eval_C, hv.2.1 t a b s, mul_zero]
    · intro t ht
      simp only [map_smul, Pi.smul_apply, hv.2.2 t ht, smul_zero]

def protectedTransfer {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) : protectedSpace (by omega) C :=
  ⟨graphTransfer hN C t u h, by
    refine ⟨graphTransfer_support hN C t u h, graphTransfer_zero_edges hN C t u h, ?_⟩
    intro v hv
    have hvt : v ≠ t.val := by intro he; exact hv (he ▸ t.property)
    have hvu : v ≠ u.val := by intro he; exact hv (he ▸ u.property)
    rw [graphTransfer_means]
    simp [hvt, hvu]⟩

def clusterMeans {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) :
    protectedSpace hN C →ₗ[ℝ] (ClusterTet C → ℝ) :=
  LinearMap.pi (fun t => (LinearMap.proj t.val).comp
    ((elementMeans hN 4).comp (protectedSpace hN C).subtype))

theorem protectedTransfer_means {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) :
    clusterMeans (by omega) C (protectedTransfer hN C t u h) =
      Pi.single t 1 - Pi.single u 1 := by
  classical
  funext v
  change elementMeans (by omega) 4 (graphTransfer hN C t u h) v.val = _
  rw [graphTransfer_means]
  simp only [Pi.sub_apply, Pi.single_apply, Subtype.val_inj]

def root {N : ℕ} (C : Finset (Cell N)) (hC : (cubeGraph C).Connected) : ClusterTet C :=
  Classical.choice (elementGraph_connected C hC).nonempty

def clusterRouting {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) :
    zeroSum (V := ClusterTet C) →ₗ[ℝ] protectedSpace (by omega) C :=
  routingLinear (elementGraph C) (elementGraph_connected C hC) (root C hC)
    (protectedTransfer hN C)

theorem clusterRouting_means {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) (m : zeroSum (V := ClusterTet C)) :
    clusterMeans (by omega) C (clusterRouting hN C hC m) = m.val := by
  exact routingLinear_means (elementGraph C) (elementGraph_connected C hC) (root C hC)
    (protectedTransfer hN C) (clusterMeans (by omega) C) (protectedTransfer_means hN C) m

theorem clusterRouting_actual_mean {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) (m : zeroSum (V := ClusterTet C))
    (t : Tet N) (ht : t.1 ∈ C) :
    tetIntegral (by omega) t (divergence N (clusterRouting hN C hC m).val.val t) =
      m.val ⟨t, ht⟩ := by
  exact congrFun (clusterRouting_means hN C hC m) ⟨t, ht⟩

theorem clusterRouting_mean_off_cluster {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) (m : zeroSum (V := ClusterTet C))
    (t : Tet N) (ht : t.1 ∉ C) :
    tetIntegral (by omega) t (divergence N (clusterRouting hN C hC m).val.val t) = 0 :=
  (clusterRouting hN C hC m).property.2.2 t ht

theorem clusterRouting_support {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) (m : zeroSum (V := ClusterTet C))
    (t : Tet N) (ht : ¬ nearCluster C t) :
    (clusterRouting hN C hC m).val.val t = 0 :=
  (clusterRouting hN C hC m).property.1 t ht

theorem clusterRouting_zero_edges {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) (m : zeroSum (V := ClusterTet C))
    (t : Tet N) (a b : Fin 4) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (clusterRouting hN C hC m).val.val t) = 0 :=
  (clusterRouting hN C hC m).property.2.1 t a b s

end FreudenthalSVLean.CubeClusterRouting
