import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Fixed linear mean routing on a connected finite dual graph

The manuscript's supported vertex-star lift and geometric mean-routing
lemma use face transfers with means `δ_u-δ_v`.  This module proves the
algebraic routing step: choose paths from every vertex to a fixed root
before receiving the means, sum the face transfers along those paths, and
obtain a single linear right inverse on the zero-sum mean space.  Each
chosen simple path has at most `card(V)-1` edges.  No input-dependent
graph, patch, or path is chosen.

The geometric dual graphs' connectivity and the actual face fields'
normalization remain separate obligations; they are explicit hypotheses
here, not project axioms or unproved assertions.
-/

open scoped BigOperators
open SimpleGraph

noncomputable section

namespace FreudenthalSVLean.MeanRoutingAlgebra

section Algebra

variable {V E : Type*} [Fintype V] [DecidableEq V] [AddCommGroup E] [Module ℝ E]

def zeroSum : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (∑ v : V, (LinearMap.proj v : (V → ℝ) →ₗ[ℝ] ℝ))

omit [DecidableEq V] in
theorem mem_zeroSum (m : V → ℝ) : m ∈ zeroSum ↔ ∑ v : V, m v = 0 := by
  simp [zeroSum, LinearMap.mem_ker, LinearMap.sum_apply]

def walkLift (G : SimpleGraph V) (Z : ∀ u v, G.Adj u v → E)
    {u v : V} (p : G.Walk u v) : E :=
  match p with
  | .nil => 0
  | .cons h q => Z _ _ h + walkLift G Z q

omit [Fintype V] in
/-- The transfer means telescope along every walk. -/
theorem walkLift_means (G : SimpleGraph V) (Z : ∀ u v, G.Adj u v → E)
    (M : E →ₗ[ℝ] (V → ℝ))
    (hZ : ∀ u v h, M (Z u v h) = Pi.single u 1 - Pi.single v 1)
    {u v : V} (p : G.Walk u v) :
    M (walkLift G Z p) = Pi.single u 1 - Pi.single v 1 := by
  induction p with
  | nil => simp [walkLift]
  | @cons u w v h p ih =>
    rw [walkLift, map_add, hZ, ih]
    abel

/-- Simple paths are fixed solely from the graph and root. -/
def rootPath (G : SimpleGraph V) (hG : G.Connected) (root v : V) : G.Walk v root :=
  Classical.choose (hG.exists_isPath v root)

omit [Fintype V] [DecidableEq V] in
theorem rootPath_isPath (G : SimpleGraph V) (hG : G.Connected) (root v : V) :
    (rootPath G hG root v).IsPath :=
  Classical.choose_spec (hG.exists_isPath v root)

omit [DecidableEq V] in
theorem rootPath_length_bound (G : SimpleGraph V) (hG : G.Connected) (root v : V) :
    (rootPath G hG root v).length ≤ Fintype.card V - 1 := by
  have h := (rootPath_isPath G hG root v).length_lt
  omega

def routingLinear (G : SimpleGraph V) (hG : G.Connected) (root : V)
    (Z : ∀ u v, G.Adj u v → E) : zeroSum (V := V) →ₗ[ℝ] E where
  toFun m := ∑ v : V, m.val v • walkLift G Z (rootPath G hG root v)
  map_add' m n := by
    simp only [Submodule.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c m := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

/-- Exact right-inverse property on all compatible mean data. -/
theorem routingLinear_means (G : SimpleGraph V) (hG : G.Connected) (root : V)
    (Z : ∀ u v, G.Adj u v → E) (M : E →ₗ[ℝ] (V → ℝ))
    (hZ : ∀ u v h, M (Z u v h) = Pi.single u 1 - Pi.single v 1)
    (m : zeroSum (V := V)) : M (routingLinear G hG root Z m) = m.val := by
  simp only [routingLinear, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    walkLift_means G Z M hZ, smul_sub, Finset.sum_sub_distrib]
  have hm : ∑ v : V, m.val v = 0 := (mem_zeroSum m.val).mp m.property
  rw [← Finset.sum_smul, hm, zero_smul, sub_zero]
  funext w
  simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]

end Algebra

section NormBounds

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype V] [DecidableEq V] [NormedSpace ℝ E] in
theorem walkLift_norm_bound (G : SimpleGraph V) (Z : ∀ u v, G.Adj u v → E)
    (C : ℝ) (hZ : ∀ u v h, ‖Z u v h‖ ≤ C) {u v : V} (p : G.Walk u v) :
    ‖walkLift G Z p‖ ≤ (p.length : ℝ) * C := by
  induction p with
  | nil => simp [walkLift]
  | @cons u w v h p ih =>
    calc
      ‖walkLift G Z (.cons h p)‖ ≤ ‖Z u w h‖ + ‖walkLift G Z p‖ := norm_add_le _ _
      _ ≤ C + (p.length : ℝ) * C := add_le_add (hZ u w h) ih
      _ = ((Walk.cons h p).length : ℝ) * C := by
        simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

omit [DecidableEq V] in
/-- Explicit graph-size bound for the fixed routing operator.  The
bound applies to any normed realization of the actual transfer fields. -/
theorem routingLinear_norm_bound (G : SimpleGraph V) (hG : G.Connected) (root : V)
    (Z : ∀ u v, G.Adj u v → E) (C : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ u v h, ‖Z u v h‖ ≤ C) (m : zeroSum (V := V)) :
    ‖routingLinear G hG root Z m‖ ≤
      ((Fintype.card V - 1 : ℕ) : ℝ) * C * ∑ v : V, |m.val v| := by
  calc
    _ ≤ ∑ v : V, ‖m.val v • walkLift G Z (rootPath G hG root v)‖ := norm_sum_le _ _
    _ = ∑ v : V, |m.val v| * ‖walkLift G Z (rootPath G hG root v)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ v : V, |m.val v| * (((Fintype.card V - 1 : ℕ) : ℝ) * C) := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (walkLift_norm_bound G Z C hZ _).trans
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rootPath_length_bound G hG root v)) hC)
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

end NormBounds

end FreudenthalSVLean.MeanRoutingAlgebra
