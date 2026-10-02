import FreudenthalSVLean.StableCubeClusterRouting
import FreudenthalSVLean.ElementMeanEnergy
import FreudenthalSVLean.GlobalVertexLift

/-!
# Stable fixed local mean removal preserving all edge restrictions

For manuscript Lemma `routing` in Proposition `edge`, the quartic cluster
router removes the actual element means of every supported velocity whose
total divergence mean is zero.  The domain records exactly this necessary
compatibility, rather than assuming it for an arbitrary input.  The result
is linear, preserves every complete edge-divergence restriction and has a
mesh-independent energy bound on clusters of prescribed bounded size.
Applicability to concrete edge fields additionally requires proving their
zero-total-mean identity; that identity is not asserted in this module.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.CubeClusterRouting
open FreudenthalSVLean.MeanRoutingAlgebra
open FreudenthalSVLean.ElementMeanEnergy
open FreudenthalSVLean.GlobalVertexLift
open FreudenthalSVLean.StableVertexLift

noncomputable section

namespace FreudenthalSVLean.ClusterMeanRemoval

set_option backward.isDefEq.respectTransparency false

def localSpace {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ) :
    Submodule ℝ (velocitySpace N k) where
  carrier v := (∀ t : Tet N, t.1 ∉ C → v.val t = 0) ∧
    (∑ t : Tet N, elementMeans hN k v t) = 0
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro v w hv hw
    constructor
    · intro t ht
      simp only [Submodule.coe_add, Pi.add_apply, hv.1 t ht, hw.1 t ht, add_zero]
    · simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, hv.2, hw.2, add_zero]
  smul_mem' := by
    intro c v hv
    constructor
    · intro t ht
      simp only [Submodule.coe_smul, Pi.smul_apply, hv.1 t ht, smul_zero]
    · simp only [map_smul, Pi.smul_apply, ← Finset.smul_sum, hv.2, smul_zero]

theorem local_mean_zero_off {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ)
    (v : localSpace hN C k) (t : Tet N) (ht : t.1 ∉ C) :
    elementMeans hN k v.val t = 0 := by
  change tetIntegral hN t (PolynomialCalculus.polynomialDivergence (v.val.val t)) = 0
  rw [v.property.1 t ht]
  simp [PolynomialCalculus.polynomialDivergence]

def localMeans {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ) :
    localSpace hN C k →ₗ[ℝ] (ClusterTet C → ℝ) :=
  LinearMap.pi (fun t => (LinearMap.proj t.val).comp
    ((elementMeans hN k).comp (localSpace hN C k).subtype))

theorem localMeans_zeroSum {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ)
    (v : localSpace hN C k) : localMeans hN C k v ∈ zeroSum := by
  classical
  rw [mem_zeroSum]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun t : Tet N => t.1 ∈ C)
    (fun t => elementMeans hN k v.val t)
  have hz : (∑ t : {t : Tet N // t.1 ∉ C}, elementMeans hN k v.val t.val) = 0 :=
    Finset.sum_eq_zero (fun t _ => local_mean_zero_off hN C k v t.val t.property)
  rw [hz, add_zero, v.property.2] at hs
  exact hs

def compatibleLocalMeans {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ) :
    localSpace hN C k →ₗ[ℝ] zeroSum (V := ClusterTet C) :=
  (localMeans hN C k).codRestrict _ (localMeans_zeroSum hN C k)

theorem localMeans_square_sum_bound {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) (k : ℕ)
    (v : localSpace hN C k) : (∑ t : ClusterTet C, (localMeans hN C k v t) ^ 2) ≤
      ((meshScale N) ^ 3 / 2) * velocityEnergy v.val.val := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun t : Tet N => t.1 ∈ C)
    (fun t => (elementMeans hN k v.val t) ^ 2)
  have hz : (∑ t : {t : Tet N // t.1 ∉ C}, (elementMeans hN k v.val t.val) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    rw [local_mean_zero_off hN C k v t.val t.property]
    norm_num
  rw [hz, add_zero] at hs
  change (∑ t : ClusterTet C, (elementMeans hN k v.val t.val) ^ 2) ≤ _
  rw [hs]
  exact globalMeans_square_sum_bound hN k v.val

def meanCorrection {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) : localSpace (by omega) C k →ₗ[ℝ] velocitySpace N k :=
  (degreeInclusion hk).comp ((protectedSpace (by omega) C).subtype.comp
    ((clusterRouting hN C hC).comp (compatibleLocalMeans (by omega) C k)))

theorem meanCorrection_means {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k)
    (C : Finset (Cell N)) (hC : (cubeGraph C).Connected)
    (v : localSpace (by omega) C k) :
    elementMeans (by omega) k (meanCorrection hN hk C hC v) = elementMeans (by omega) k v.val := by
  classical
  funext t
  by_cases ht : t.1 ∈ C
  · exact clusterRouting_actual_mean hN C hC (compatibleLocalMeans (by omega) C k v) t ht
  · change tetIntegral (by omega) t (divergence N
      (clusterRouting hN C hC (compatibleLocalMeans (by omega) C k v)).val.val t) = _
    rw [clusterRouting_mean_off_cluster hN C hC _ t ht, local_mean_zero_off _ C k v t ht]

def meanFreeLift {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k) (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) : localSpace (by omega) C k →ₗ[ℝ] velocitySpace N k :=
  (localSpace (show 0 < N from by omega) C k).subtype - meanCorrection hN hk C hC

theorem meanFreeLift_means_zero {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k)
    (C : Finset (Cell N)) (hC : (cubeGraph C).Connected)
    (v : localSpace (by omega) C k) :
    elementMeans (by omega) k (meanFreeLift hN hk C hC v) = 0 := by
  simp only [meanFreeLift, LinearMap.sub_apply, map_sub, Submodule.subtype_apply,
    meanCorrection_means hN hk C hC, sub_self]

theorem meanFreeLift_preserves_edges {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k)
    (C : Finset (Cell N)) (hC : (cubeGraph C).Connected)
    (v : localSpace (by omega) C k) (t : Tet N) (a b : Fin 4) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (meanFreeLift hN hk C hC v).val t) =
    eval (segmentPoint (vertex t a) (vertex t b) s) (divergence N v.val.val t) := by
  change eval _ (divergence N (v.val.val -
    (clusterRouting hN C hC (compatibleLocalMeans (by omega) C k v)).val.val) t) = _
  simp only [map_sub, Pi.sub_apply, clusterRouting_zero_edges, sub_zero]

theorem meanFreeLift_support {N k : ℕ} (hN : 2 ≤ N) (hk : 4 ≤ k)
    (C : Finset (Cell N)) (hC : (cubeGraph C).Connected)
    (v : localSpace (by omega) C k) (t : Tet N) (ht : ¬ nearCluster C t) :
    (meanFreeLift hN hk C hC v).val t = 0 := by
  have hc : t.1 ∉ C := fun hc => ht ⟨t.1, hc, Or.inl rfl⟩
  change v.val.val t - (clusterRouting hN C hC
    (compatibleLocalMeans (by omega) C k v)).val.val t = 0
  rw [v.property.1 t hc, clusterRouting_support hN C hC _ t ht, sub_self]

theorem meanFreeLift_uniform_energy (L : ℕ) : ∃ A : ℝ, 0 < A ∧
    ∀ (N k : ℕ) (hN : 2 ≤ N) (hk : 4 ≤ k) (C : Finset (Cell N))
      (hC : (cubeGraph C).Connected) (_hL : C.card ≤ L) (v : localSpace (by omega) C k),
      velocityEnergy (meanFreeLift hN hk C hC v).val ≤ A * velocityEnergy v.val.val := by
  obtain ⟨A, hA, hR⟩ := StableCubeClusterRouting.clusterRouting_uniform_energy L
  refine ⟨2 + A, by positivity, ?_⟩
  intro N k hN hk C hC hL v
  have hmean := localMeans_square_sum_bound (by omega) C k v
  have hcor := hR N hN C hC hL (compatibleLocalMeans (by omega) C k v)
  have hscale : 0 ≤ A * ((meshScale N) ^ 3)⁻¹ := by positivity [meshScale_pos N (by omega)]
  have hE : velocityEnergy (meanCorrection hN hk C hC v).val ≤
      (A / 2) * velocityEnergy v.val.val := by
    calc
      _ ≤ A * ((meshScale N) ^ 3)⁻¹ * ∑ t : ClusterTet C,
          (localMeans (by omega) C k v t) ^ 2 := hcor
      _ ≤ A * ((meshScale N) ^ 3)⁻¹ * (((meshScale N) ^ 3 / 2) * velocityEnergy v.val.val) :=
        mul_le_mul_of_nonneg_left hmean hscale
      _ = _ := by field_simp [(meshScale_pos N (by omega)).ne']
  have hs := velocityEnergy_sub (by omega) v.val.val (meanCorrection hN hk C hC v).val
  change velocityEnergy (v.val.val - (meanCorrection hN hk C hC v).val) ≤ _
  calc
    _ ≤ 2 * (velocityEnergy v.val.val + velocityEnergy (meanCorrection hN hk C hC v).val) := hs
    _ ≤ 2 * (velocityEnergy v.val.val + (A / 2) * velocityEnergy v.val.val) := by linarith
    _ = _ := by ring

end FreudenthalSVLean.ClusterMeanRemoval
