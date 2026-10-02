import FreudenthalSVLean.LowDegreeBubbleExpansion

/-!
# Complete barycentric edge-mode expansions

The trace decomposition used in manuscript Lemma `edge-star` is a
structural two-variable statement.  Projection to the two edge variables
preserves precisely the coefficients supported on them.  A homogeneous
degree-`d` index supported on two distinct vertices is uniquely determined
by one exponent in `Fin (d+1)`.  Consequently the full edge trace is the
sum of these Bernstein monomials.  Endpoint values recover the two pure
coefficients.  In degrees three and four, zero endpoint values leave
exactly the two endpoint modes, or the two endpoint and one middle mode.

All coefficients are extracted from the input polynomial; no separately
postulated coefficient representation or numerical rank test is used.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.HomogeneousSkeletonCompleteness
open FreudenthalSVLean.LowDegreeBubbleExpansion

noncomputable section

namespace FreudenthalSVLean.HomogeneousEdgeModes

set_option backward.isDefEq.respectTransparency false

theorem projection_coefficient_all (s : Finset Vertex) (α : Vertex →₀ ℕ)
    (p : MvPolynomial Vertex ℝ) :
    coeff α (projection s p) = if α.support ⊆ s then coeff α p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
      rw [projection_monomial]
      by_cases hβ : β.support ⊆ s
      · rw [if_pos hβ]
        by_cases he : β = α
        · subst β
          rw [if_pos hβ]
        · simp [coeff_monomial, he]
      · rw [if_neg hβ, coeff_zero]
        by_cases he : β = α
        · subst β
          rw [if_neg hβ]
        · simp [coeff_monomial, he]
  | add p q hp hq =>
      simp only [map_add, coeff_add, hp, hq]
      split_ifs <;> simp

theorem projection_homogeneous (s : Finset Vertex) (p : MvPolynomial Vertex ℝ)
    (d : ℕ) (hp : IsHomogeneous p d) : IsHomogeneous (projection s p) d := by
  intro α hα
  rw [projection_coefficient_all] at hα
  split_ifs at hα with hs
  · exact hp hα
  · exact False.elim (hα rfl)

def edgeExponent (a b : Vertex) (d : ℕ) (ν : Fin (d + 1)) : Vertex →₀ ℕ :=
  Finsupp.single a (d - ν.val) + Finsupp.single b ν.val

theorem edgeExponent_at_b (a b : Vertex) (hab : a ≠ b) (d : ℕ) (ν : Fin (d + 1)) :
    edgeExponent a b d ν b = ν.val := by
  simp [edgeExponent, hab]

theorem edgeExponent_injective (a b : Vertex) (hab : a ≠ b) (d : ℕ) :
    Function.Injective (edgeExponent a b d) := by
  intro ν μ he
  apply Fin.ext
  have hv := congrArg (fun α : Vertex →₀ ℕ => α b) he
  simpa only [edgeExponent_at_b a b hab] using hv

theorem edgeExponent_support (a b : Vertex) (d : ℕ) (ν : Fin (d + 1)) :
    (edgeExponent a b d ν).support ⊆ {a, b} := by
  intro i hi
  by_contra hn
  have hne : i ≠ a ∧ i ≠ b := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn
  have hz : edgeExponent a b d ν i = 0 := by
    simp [edgeExponent, Ne.symm hne.1, Ne.symm hne.2]
  exact (Finsupp.mem_support_iff.mp hi) hz

theorem index_supported_pair (α : Vertex →₀ ℕ) (a b : Vertex) (hab : a ≠ b)
    (hs : α.support ⊆ {a, b}) :
    α = Finsupp.single a (α a) + Finsupp.single b (α b) := by
  ext i
  by_cases ha : i = a
  · subst i
    simp [hab]
  · by_cases hb : i = b
    · subst i
      simp [hab]
    · have hz : α i = 0 := by
        by_contra hn
        have hm := hs (Finsupp.mem_support_iff.mpr hn)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        exact hm.elim ha hb
      simp [hz, Ne.symm ha, Ne.symm hb]

theorem pair_degree (α : Vertex →₀ ℕ) (a b : Vertex) (hab : a ≠ b)
    (hs : α.support ⊆ {a, b}) : α.degree = α a + α b := by
  have he := congrArg Finsupp.degree (index_supported_pair α a b hab hs)
  simpa only [map_add, Finsupp.degree_single] using he

theorem edge_index_coverage (α : Vertex →₀ ℕ) (a b : Vertex) (hab : a ≠ b)
    (d : ℕ) (hd : α.degree = d) (hs : α.support ⊆ {a, b}) :
    ∃ ν : Fin (d + 1), edgeExponent a b d ν = α := by
  have hsum : α a + α b = d := (pair_degree α a b hab hs).symm.trans hd
  refine ⟨⟨α b, by omega⟩, ?_⟩
  dsimp [edgeExponent]
  have ha : d - α b = α a := by omega
  rw [ha]
  exact (index_supported_pair α a b hab hs).symm

theorem projected_edge_expansion (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d) (a b : Vertex) (hab : a ≠ b) :
    projection {a, b} p = ∑ ν : Fin (d + 1),
      monomial (edgeExponent a b d ν) (coeff (edgeExponent a b d ν) p) := by
  have hh : projection {a, b} p = ∑ ν : Fin (d + 1),
      monomial (edgeExponent a b d ν) (coeff (edgeExponent a b d ν) (projection {a, b} p)) := by
    apply expansion_of_coefficient_coverage (edgeExponent a b d) (edgeExponent_injective a b hab d)
    intro α hα
    have hc := hα
    rw [projection_coefficient_all] at hc
    have hs : α.support ⊆ {a, b} := by
      by_contra hn
      simp only [if_neg hn] at hc
      exact hc rfl
    have hd : α.degree = d := by
      simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using
        projection_homogeneous {a, b} p d hp hα
    exact edge_index_coverage α a b hab d hd hs
  rw [hh]
  apply Finset.sum_congr rfl
  intro ν _
  rw [projection_coefficient {a, b} _ (edgeExponent_support a b d ν)]

def edgeBarycentric (a b : Vertex) (s : ℝ) : Vertex → ℝ :=
  fun i => (1 - s) * (if i = a then 1 else 0) + s * (if i = b then 1 else 0)

theorem edge_eval_projection (a b : Vertex) (s : ℝ) (p : MvPolynomial Vertex ℝ) :
    eval (edgeBarycentric a b s) (projection {a, b} p) = eval (edgeBarycentric a b s) p := by
  rw [projection_eval]
  apply congrArg (fun z : Vertex → ℝ => eval z p)
  funext i
  by_cases hi : i ∈ ({a, b} : Finset Vertex)
  · rw [if_pos hi]
  · have hn : i ≠ a ∧ i ≠ b := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi
    simp [hi, edgeBarycentric, hn.1, hn.2]

theorem eval_edge_monomial (a b : Vertex) (hab : a ≠ b) (d : ℕ)
    (ν : Fin (d + 1)) (c s : ℝ) :
    eval (edgeBarycentric a b s) (monomial (edgeExponent a b d ν) c) =
      c * (1 - s) ^ (d - ν.val) * s ^ ν.val := by
  rw [edgeExponent, monomial_add_single, ← C_mul_X_pow_eq_monomial]
  simp [edgeBarycentric, hab, Ne.symm hab]

/-- The complete trace formula, in every degree. -/
theorem homogeneous_edge_expansion (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d) (a b : Vertex) (hab : a ≠ b) (s : ℝ) :
    eval (edgeBarycentric a b s) p = ∑ ν : Fin (d + 1),
      coeff (edgeExponent a b d ν) p * (1 - s) ^ (d - ν.val) * s ^ ν.val := by
  rw [← edge_eval_projection a b s p, projected_edge_expansion p d hp a b hab, map_sum]
  apply Finset.sum_congr rfl
  intro ν _
  exact eval_edge_monomial a b hab d ν _ s

theorem first_endpoint_coefficient (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d) (a b : Vertex) (hab : a ≠ b) :
    eval (edgeBarycentric a b 0) p = coeff (edgeExponent a b d 0) p := by
  rw [homogeneous_edge_expansion p d hp a b hab]
  calc
    _ = coeff (edgeExponent a b d 0) p * (1 - 0) ^ (d - 0) * 0 ^ (0 : ℕ) := by
      apply Finset.sum_eq_single 0
      · intro ν _ hν
        have hn : ν.val ≠ 0 := fun h => hν (Fin.ext h)
        simp [zero_pow hn]
      · simp
    _ = _ := by simp

theorem last_endpoint_coefficient (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d) (a b : Vertex) (hab : a ≠ b) :
    eval (edgeBarycentric a b 1) p = coeff (edgeExponent a b d ⟨d, by omega⟩) p := by
  rw [homogeneous_edge_expansion p d hp a b hab]
  calc
    _ = coeff (edgeExponent a b d ⟨d, by omega⟩) p * (1 - 1) ^ (d - d) * 1 ^ d := by
      apply Finset.sum_eq_single (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1))
      · intro ν _ hν
        have hn : d - ν.val ≠ 0 := by
          have hl : ν.val < d + 1 := ν.isLt
          have hne : ν.val ≠ d := fun h => hν (Fin.ext h)
          omega
        simp [zero_pow hn]
      · simp
    _ = _ := by simp

theorem cubic_zero_endpoint_trace (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 3)
    (a b : Vertex) (hab : a ≠ b) (ha : eval (edgeBarycentric a b 0) p = 0)
    (hb : eval (edgeBarycentric a b 1) p = 0) (s : ℝ) :
    eval (edgeBarycentric a b s) p =
      coeff (edgeExponent a b 3 1) p * (1 - s) ^ 2 * s +
      coeff (edgeExponent a b 3 2) p * (1 - s) * s ^ 2 := by
  have h₀ : coeff (edgeExponent a b 3 0) p = 0 :=
    (first_endpoint_coefficient p 3 hp a b hab).symm.trans ha
  have h₃ : coeff (edgeExponent a b 3 3) p = 0 :=
    (last_endpoint_coefficient p 3 hp a b hab).symm.trans hb
  rw [homogeneous_edge_expansion p 3 hp a b hab]
  simp [Fin.sum_univ_succ, h₀, h₃]

theorem quartic_zero_endpoint_trace (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 4)
    (a b : Vertex) (hab : a ≠ b) (ha : eval (edgeBarycentric a b 0) p = 0)
    (hb : eval (edgeBarycentric a b 1) p = 0) (s : ℝ) :
    eval (edgeBarycentric a b s) p =
      coeff (edgeExponent a b 4 1) p * (1 - s) ^ 3 * s +
      coeff (edgeExponent a b 4 2) p * (1 - s) ^ 2 * s ^ 2 +
      coeff (edgeExponent a b 4 3) p * (1 - s) * s ^ 3 := by
  have h₀ : coeff (edgeExponent a b 4 0) p = 0 :=
    (first_endpoint_coefficient p 4 hp a b hab).symm.trans ha
  have h₄ : coeff (edgeExponent a b 4 4) p = 0 :=
    (last_endpoint_coefficient p 4 hp a b hab).symm.trans hb
  rw [homogeneous_edge_expansion p 4 hp a b hab]
  simp [Fin.sum_univ_succ, h₀, h₄]
  ring

end FreudenthalSVLean.HomogeneousEdgeModes
