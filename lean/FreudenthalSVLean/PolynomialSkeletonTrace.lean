import FreudenthalSVLean.SkeletonBubble
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# From homogeneous coefficients to actual skeleton traces

The quartic macroelement proof identifies edge-carried Bernstein indices
with indices having at most two nonzero barycentric entries.  This module
proves the general finite-to-functional implication: when the corresponding
coefficients vanish, evaluation on the skeleton vanishes identically.
It applies to actual polynomial evaluation and does not define the trace
to be the coefficient expression being tested.
-/

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace FreudenthalSVLean.PolynomialSkeletonTrace

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

/-- A homogeneous polynomial vanishes on a coordinate skeleton if every
coefficient carried by that skeleton vanishes. -/
theorem eval_zero_on_skeleton (p : MvPolynomial σ R) (d : ℕ)
    (hp : IsHomogeneous p d) (s : Finset σ) (x : σ → R)
    (hx : ∀ j, j ∉ s → x j = 0)
    (hc : ∀ α : σ →₀ ℕ, α.degree = d → α.support ⊆ s → coeff α p = 0) :
    eval x p = 0 := by
  rw [eval_eq']
  apply Finset.sum_eq_zero
  intro α hα
  have hne : coeff α p ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have hd : α.degree = d := by
    simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hp hne
  by_cases hs : α.support ⊆ s
  · rw [hc α hd hs, zero_mul]
  · obtain ⟨j, hj, hjs⟩ := Finset.not_subset.mp hs
    have hpos : 0 < α j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
    have hpow : x j ^ α j = 0 := by simp [hx j hjs, Nat.ne_of_gt hpos]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hpow, mul_zero]

/-- In particular, vanishing of all degree-`d` coefficients with at most two
nonzero entries implies zero restriction to every tetrahedron edge. -/
theorem eval_zero_on_edge (p : MvPolynomial σ R) (d : ℕ)
    (hp : IsHomogeneous p d) (s : Finset σ) (hs : s.card ≤ 2) (x : σ → R)
    (hx : ∀ j, j ∉ s → x j = 0)
    (hc : ∀ α : σ →₀ ℕ, α.degree = d → α.support.card ≤ 2 → coeff α p = 0) :
    eval x p = 0 := by
  apply eval_zero_on_skeleton p d hp s x hx
  intro α hd hα
  exact hc α hd ((Finset.card_le_card hα).trans hs)

end FreudenthalSVLean.PolynomialSkeletonTrace
