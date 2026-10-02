import FreudenthalSVLean.CubeClusterRouting
import FreudenthalSVLean.StableStarMeanRouting

/-!
# Uniform stability of fixed actual cube-cluster routing

For manuscript Lemma `routing` and inequality `routing-stability`, every
face-connected cluster of at most `L` cubes admits a fixed quartic routing
operator with actual energy at most `C(L) h^{-3} sum m_T^2`.  The estimate
uses the exact `6 L` element count, simple root paths and the physical
macro-transfer bound.  In particular its constant is chosen before the
mesh, cluster location and mean input.
-/

open scoped BigOperators
open SimpleGraph
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.CubeClusterRouting
open FreudenthalSVLean.MeanRoutingAlgebra
open FreudenthalSVLean.StableStarMeanRouting
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableCubeClusterRouting

def fieldInclusion {N : ℕ} (hN : 0 < N) (C : Finset (Cell N)) :
    protectedSpace hN C →ₗ[ℝ] BrokenVelocity N :=
  (velocitySpace N 4).subtype.comp (protectedSpace hN C).subtype

/-- The bound is deliberately explicit but need not be sharp.  Its only
geometric parameter is the prescribed upper bound on cluster size. -/
theorem clusterRouting_uniform_energy (L : ℕ) : ∃ A : ℝ, 0 < A ∧
    ∀ (N : ℕ) (hN : 2 ≤ N) (C : Finset (Cell N)) (hC : (cubeGraph C).Connected)
      (_hL : C.card ≤ L) (m : zeroSum (V := ClusterTet C)),
      velocityEnergy (clusterRouting hN C hC m).val.val ≤
        A * ((meshScale N) ^ 3)⁻¹ * ∑ t : ClusterTet C, (m.val t) ^ 2 := by
  classical
  obtain ⟨A, hA, hT⟩ := graphTransfer_uniform_energy
  refine ⟨(6 * L + 1 : ℝ) ^ 3 * A, by positivity, ?_⟩
  intro N hN C hC hL m
  let G := elementGraph C
  let hG := elementGraph_connected C hC
  let Z := protectedTransfer hN C
  let I := fieldInclusion (by omega) C
  let B := A * ((meshScale N) ^ 3)⁻¹
  let K : ℝ := 6 * L + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity [meshScale_pos N (by omega)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc : (Fintype.card (ClusterTet C) : ℝ) ≤ K := by
    rw [clusterTet_card]
    have hL' : (C.card : ℝ) ≤ L := Nat.cast_le.mpr hL
    dsimp [K]
    push_cast
    linarith
  have hZ : ∀ t u h, velocityEnergy (I (Z t u h)) ≤ B := by
    intro t u h
    exact hT N hN C t u h
  let W := fun t : ClusterTet C => I (walkLift G Z (rootPath G hG (root C hC) t))
  have hW (t : ClusterTet C) : velocityEnergy (W t) ≤ K ^ 2 * B := by
    have hw := walkLift_energy_bound (by omega) G (fun t u h => I (Z t u h)) B hZ
      (rootPath G hG (root C hC) t)
    rw [← map_walkLift G Z I (rootPath G hG (root C hC) t)] at hw
    have hl : ((rootPath G hG (root C hC) t).length : ℝ) ≤ K := by
      have hb := rootPath_length_bound G hG (root C hC) t
      have hb' : (rootPath G hG (root C hC) t).length ≤ Fintype.card (ClusterTet C) :=
        hb.trans (Nat.sub_le _ _)
      exact (Nat.cast_le.mpr hb').trans hc
    have hs : ((rootPath G hG (root C hC) t).length : ℝ) ^ 2 ≤ K ^ 2 := by
      have hp : (0 : ℝ) ≤ ((rootPath G hG (root C hC) t).length : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact hw.trans (mul_le_mul_of_nonneg_right hs hB)
  have he : (clusterRouting hN C hC m).val.val = ∑ t : ClusterTet C, m.val t • W t := by
    change I (routingLinear G hG (root C hC) Z m) = _
    simp only [routingLinear, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
    rfl
  rw [he]
  calc
    _ ≤ (Fintype.card (ClusterTet C) : ℝ) *
        ∑ t : ClusterTet C, velocityEnergy (m.val t • W t) := by
      simpa only [Finset.card_univ] using velocityEnergy_sum (by omega) Finset.univ
        (fun t : ClusterTet C => m.val t • W t)
    _ ≤ (Fintype.card (ClusterTet C) : ℝ) *
        ∑ t : ClusterTet C, (m.val t) ^ 2 * (K ^ 2 * B) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro t _
      rw [velocityEnergy_smul]
      exact mul_le_mul_of_nonneg_left (hW t) (sq_nonneg _)
    _ = (Fintype.card (ClusterTet C) : ℝ) *
        ((∑ t : ClusterTet C, (m.val t) ^ 2) * (K ^ 2 * B)) := by rw [Finset.sum_mul]
    _ ≤ K * ((∑ t : ClusterTet C, (m.val t) ^ 2) * (K ^ 2 * B)) := by
      apply mul_le_mul_of_nonneg_right hc
      positivity
    _ = _ := by dsimp [K, B]; ring

end FreudenthalSVLean.StableCubeClusterRouting
