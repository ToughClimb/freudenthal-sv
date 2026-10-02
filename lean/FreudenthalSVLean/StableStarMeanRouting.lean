import FreudenthalSVLean.StarMeanRouting
import FreudenthalSVLean.StableFaceTransfer

/-!
# Uniform physical energy bound for actual vertex-star mean routing

For manuscript Lemma `vertex-local`, the actual supported cubic routing
operator satisfies `energy ≤ C h^{-3} sum m_T^2`, with one constant before
all mesh and vertex parameters.  The proof uses pointwise Cauchy--Schwarz,
the proved physical energy of each transfer, at most twenty-three edges
per fixed root path, and at most twenty-four star elements.  The result
includes every interior and boundary star and does not assume Zhang's
mesh-specific vertex lemma.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.MeanRoutingAlgebra
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.StableFaceTransfer
open FreudenthalSVLean.VelocityEnergy
open SimpleGraph

noncomputable section

namespace FreudenthalSVLean.StableStarMeanRouting

def fieldInclusion {N : ℕ} (n : GridVertex N) :
    supportedZeroVertexCubic n →ₗ[ℝ] BrokenVelocity N :=
  (velocitySpace N 3).subtype.comp (supportedZeroVertexCubic n).subtype

theorem map_walkLift {V E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → E) (L : E →ₗ[ℝ] F) {u v : V} (p : G.Walk u v) :
    L (walkLift G Z p) = walkLift G (fun a b h => L (Z a b h)) p := by
  induction p with
  | nil => simp [walkLift]
  | @cons a b c h p ih => simp only [walkLift, map_add, ih]

def walkTransferList {V : Type*} {N : ℕ} (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → BrokenVelocity N) {u v : V} (p : G.Walk u v) :
    List (BrokenVelocity N) :=
  match p with
  | .nil => []
  | .cons h q => Z _ _ h :: walkTransferList G Z q

theorem walkTransferList_length {V : Type*} {N : ℕ} (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → BrokenVelocity N) {u v : V} (p : G.Walk u v) :
    (walkTransferList G Z p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [walkTransferList, List.length_cons, Walk.length_cons, ih]

theorem walkTransferList_sum {V : Type*} {N : ℕ} (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → BrokenVelocity N) {u v : V} (p : G.Walk u v) :
    (walkTransferList G Z p).sum = walkLift G Z p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [walkTransferList, List.sum_cons, walkLift, ih]

theorem walkTransferList_bound {V : Type*} {N : ℕ} (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → BrokenVelocity N) (B : ℝ)
    (hZ : ∀ a b h, velocityEnergy (Z a b h) ≤ B)
    {u v : V} (p : G.Walk u v) :
    ∀ w ∈ walkTransferList G Z p, velocityEnergy w ≤ B := by
  induction p with
  | nil => simp [walkTransferList]
  | @cons a b c h p ih =>
    intro w hw
    simp only [walkTransferList, List.mem_cons] at hw
    rcases hw with he | he
    · subst w
      exact hZ a b h
    · exact ih w he

theorem velocityEnergy_list_sum {N : ℕ} (hN : 0 < N) (l : List (BrokenVelocity N))
    (B : ℝ) (hl : ∀ v ∈ l, velocityEnergy v ≤ B) :
    velocityEnergy l.sum ≤ (l.length : ℝ) ^ 2 * B := by
  have hs : (∑ i : Fin l.length, l.get i) = l.sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  have hsum := velocityEnergy_sum hN Finset.univ (fun i : Fin l.length => l.get i)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  rw [hs] at hsum
  calc
    _ ≤ (l.length : ℝ) * ∑ i : Fin l.length, velocityEnergy (l.get i) := hsum
    _ ≤ (l.length : ℝ) * ((l.length : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ ∑ _i : Fin l.length, B :=
          Finset.sum_le_sum (fun i _ => hl _ (l.get_mem i))
        _ = _ := by simp
    _ = _ := by ring

theorem walkLift_energy_bound {V : Type*} {N : ℕ} (hN : 0 < N) (G : SimpleGraph V)
    (Z : ∀ u v, G.Adj u v → BrokenVelocity N) (B : ℝ)
    (hZ : ∀ a b h, velocityEnergy (Z a b h) ≤ B) {u v : V} (p : G.Walk u v) :
    velocityEnergy (walkLift G Z p) ≤ (p.length : ℝ) ^ 2 * B := by
  have h := velocityEnergy_list_sum hN (walkTransferList G Z p) B
    (walkTransferList_bound G Z B hZ p)
  simpa only [walkTransferList_sum, walkTransferList_length] using h

theorem star_size_bound {N : ℕ} (n : GridVertex N) : Fintype.card (VertexStar n) ≤ 24 := by
  classical
  calc
    _ = Fintype.card {s : State // admissible n s} := Fintype.card_congr (starStateEquiv n)
    _ ≤ Fintype.card State := Fintype.card_subtype_le _
    _ = 24 := state_count

/-- Uniform stability of the actual fixed linear routing operator.
Exact means, support, and vertex protection are proved in `StarMeanRouting`;
this theorem supplies its genuine whole-mesh gradient-energy estimate. -/
theorem starRouting_uniform_energy : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N)
    (n : GridVertex N) (m : zeroSum (V := VertexStar n)),
    velocityEnergy (starRouting hN n m).val.val ≤
      C * ((meshScale N) ^ 3)⁻¹ * ∑ ta : VertexStar n, (m.val ta) ^ 2 := by
  classical
  obtain ⟨C, hC, hT⟩ := transfer_uniform_energy
  refine ⟨24 * 23 ^ 2 * C, by positivity, ?_⟩
  intro N hN n m
  let G := actualGraph n
  let hG := actualGraph_connected hN n
  let Z := orientedTransfer hN n
  let L := fieldInclusion n
  let B := C * ((meshScale N) ^ 3)⁻¹
  have hB : 0 ≤ B := mul_nonneg hC.le
    (inv_nonneg.mpr (pow_nonneg (meshScale_pos N hN).le _))
  have hZ : ∀ ta tb h, velocityEnergy (L (Z ta tb h)) ≤ B := by
    intro ta tb h
    let p := facePair ta tb h
    have hf := facePair_spec ta tb h
    change velocityEnergy (transferField N ta.val.1 p.1) ≤ B
    exact hT N hN n ta tb p.1 p.2 hf.1 hf.2.1 h.1 hf.2.2
  let W := fun ta : VertexStar n => L (walkLift G Z (rootPath G hG (starRoot hN n) ta))
  have hW (ta : VertexStar n) : velocityEnergy (W ta) ≤ 23 ^ 2 * B := by
    have hw := walkLift_energy_bound hN G (fun a b h => L (Z a b h)) B hZ
      (rootPath G hG (starRoot hN n) ta)
    rw [← map_walkLift G Z L (rootPath G hG (starRoot hN n) ta)] at hw
    have hl : ((rootPath G hG (starRoot hN n) ta).length : ℝ) ≤ 23 := by
      exact_mod_cast star_path_length_bound hN n ta
    have hlsq : ((rootPath G hG (starRoot hN n) ta).length : ℝ) ^ 2 ≤ 23 ^ 2 := by
      have hp : (0 : ℝ) ≤ ((rootPath G hG (starRoot hN n) ta).length : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact hw.trans (mul_le_mul_of_nonneg_right hlsq hB)
  have he : (starRouting hN n m).val.val = ∑ ta : VertexStar n, m.val ta • W ta := by
    change L (routingLinear G hG (starRoot hN n) Z m) = _
    simp only [routingLinear, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
    rfl
  have hc : (Fintype.card (VertexStar n) : ℝ) ≤ 24 := by
    exact_mod_cast star_size_bound n
  rw [he]
  calc
    _ ≤ (Fintype.card (VertexStar n) : ℝ) *
        ∑ ta : VertexStar n, velocityEnergy (m.val ta • W ta) := by
      simpa only [Finset.card_univ] using velocityEnergy_sum hN Finset.univ
        (fun ta : VertexStar n => m.val ta • W ta)
    _ ≤ (Fintype.card (VertexStar n) : ℝ) *
        ∑ ta : VertexStar n, (m.val ta) ^ 2 * (23 ^ 2 * B) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro ta _
      rw [velocityEnergy_smul]
      exact mul_le_mul_of_nonneg_left (hW ta) (sq_nonneg _)
    _ = (Fintype.card (VertexStar n) : ℝ) *
        ((∑ ta : VertexStar n, (m.val ta) ^ 2) * (23 ^ 2 * B)) := by rw [Finset.sum_mul]
    _ ≤ 24 * ((∑ ta : VertexStar n, (m.val ta) ^ 2) * (23 ^ 2 * B)) := by
      apply mul_le_mul_of_nonneg_right hc
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg (sq_nonneg (23 : ℝ)) hB)
    _ = _ := by dsimp [B]; ring

end FreudenthalSVLean.StableStarMeanRouting
