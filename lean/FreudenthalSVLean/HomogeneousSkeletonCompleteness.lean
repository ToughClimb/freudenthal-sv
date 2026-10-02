import FreudenthalSVLean.HomogeneousBarycentric
import FreudenthalSVLean.PolynomialSkeletonTrace
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# Completeness of homogeneous edge coefficient conditions

Manuscript Lemma `bubble` identifies polynomials vanishing on every
tetrahedron edge with homogeneous barycentric expansions whose coefficients
on at most two variables vanish.  The forward implication is proved in
`PolynomialSkeletonTrace`.  Here the converse is proved from actual values
on closed edges: homogeneity extends a trace to the positive cone, polynomial
identity on an open box proves a projected polynomial is zero, and an
algebraic projection preserves precisely the coefficients carried by that
edge.  The result applies to every degree and every translated coordinate
chain, rather than to an enumerated list of coefficients.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.HomogeneousSkeletonCompleteness

set_option backward.isDefEq.respectTransparency false

section Algebra

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

omit [DecidableEq σ] in
theorem eval_scaled (p : MvPolynomial σ R) (d : ℕ) (hp : IsHomogeneous p d)
    (c : R) (x : σ → R) :
    eval (fun i => c * x i) p = c ^ d * eval x p := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hd : α.degree = d := by
    simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using
      hp (MvPolynomial.mem_support_iff.mp hα)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finsupp.degree_eq_sum, hd]
  ring

def projection (s : Finset σ) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => if i ∈ s then X i else 0)

omit [Fintype σ] in
theorem projection_monomial (s : Finset σ) (α : σ →₀ ℕ) (c : R) :
    projection s (monomial α c) = if α.support ⊆ s then monomial α c else 0 := by
  rw [projection, eval₂Hom_monomial]
  by_cases hs : α.support ⊆ s
  · rw [if_pos hs, monomial_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp only [if_pos (hs hi)]
  · rw [if_neg hs]
    obtain ⟨i, hi, his⟩ := Finset.not_subset.mp hs
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero hi
    simp [his, zero_pow (Finsupp.mem_support_iff.mp hi)]

omit [Fintype σ] in
/-- Restricting variables outside an edge to zero leaves every coefficient
supported on that edge unchanged. -/
theorem projection_coefficient (s : Finset σ) (α : σ →₀ ℕ) (hα : α.support ⊆ s)
    (p : MvPolynomial σ R) : coeff α (projection s p) = coeff α p := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
      rw [projection_monomial]
      by_cases hβ : β.support ⊆ s
      · rw [if_pos hβ]
      · have hne : β ≠ α := fun he => hβ (he ▸ hα)
        simp [hβ, coeff_monomial, hne]
  | add p q hp hq =>
      simp only [map_add, coeff_add, hp, hq]

omit [Fintype σ] in
theorem projection_eval (s : Finset σ) (p : MvPolynomial σ R) (x : σ → R) :
    eval x (projection s p) = eval (fun i => if i ∈ s then x i else 0) p := by
  rw [projection, PolynomialCalculus.eval_substitution]
  apply congrArg (fun z : σ → R => eval z p)
  funext i
  split_ifs <;> simp

end Algebra

/-- This is only a statement about subsets of the four vertices of a single
arbitrary tetrahedron; it does not assert coverage by sample meshes. -/
theorem support_in_distinct_pair (s : Finset Vertex) (hs : s.card ≤ 2) :
    ∃ a b : Vertex, a ≠ b ∧ s ⊆ {a, b} := by
  decide +kernel +revert

/-- A zero trace on the normalized edge forces its homogeneous projection
to be the zero polynomial. -/
theorem projection_zero_of_edge_trace (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d) (a b : Vertex) (hab : a ≠ b)
    (he : ∀ t ∈ Icc (0 : ℝ) 1,
      eval (fun i => (1 - t) * (if i = a then 1 else 0) +
        t * (if i = b then 1 else 0)) p = 0) :
    projection {a, b} p = 0 := by
  apply MvPolynomial.funext_set (fun _ : Vertex => Ioo (1 : ℝ) 2)
    (fun _ => Ioo_infinite (by norm_num))
  intro x hx
  rw [projection_eval, map_zero]
  have ha : 0 < x a := lt_trans (by norm_num) (hx a (mem_univ a)).1
  have hb : 0 < x b := lt_trans (by norm_num) (hx b (mem_univ b)).1
  have hc : 0 < x a + x b := add_pos ha hb
  let t : ℝ := x b / (x a + x b)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hb.le hc.le
    · apply (div_le_one hc).mpr
      linarith
  have hv : (fun i => if i ∈ ({a, b} : Finset Vertex) then x i else 0) =
      (fun i => (x a + x b) * ((1 - t) * (if i = a then 1 else 0) +
        t * (if i = b then 1 else 0))) := by
    funext i
    by_cases hia : i = a
    · subst i
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, if_true,
        hab, if_false, mul_one, mul_zero, add_zero]
      dsimp [t]
      field_simp
      ring
    · by_cases hib : i = b
      · subst i
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true, if_true,
          hia, if_false, mul_one, mul_zero, zero_add]
        exact (mul_div_cancel₀ _ (ne_of_gt hc)).symm
      · simp [hia, hib]
  rw [hv, eval_scaled p d hp, he t ht, mul_zero]

/-- Completeness: geometric zero traces imply every edge-carried homogeneous
coefficient is zero. -/
theorem coefficients_zero_of_edge_traces (p : MvPolynomial Vertex ℝ) (d : ℕ)
    (hp : IsHomogeneous p d)
    (he : ∀ a b : Vertex, a ≠ b → ∀ t ∈ Icc (0 : ℝ) 1,
      eval (fun i => (1 - t) * (if i = a then 1 else 0) +
        t * (if i = b then 1 else 0)) p = 0)
    (α : Vertex →₀ ℕ) (hα : α.support.card ≤ 2) : coeff α p = 0 := by
  obtain ⟨a, b, hab, hs⟩ := support_in_distinct_pair α.support hα
  rw [← projection_coefficient {a, b} α hs p,
    projection_zero_of_edge_trace p d hp a b hab (he a b hab), coeff_zero]

/-- The coefficient condition used in Lemma `bubble` follows from the
actual spatial pressure polynomial's zero traces, through the proved
barycentric representation. -/
theorem representation_coefficients_zero (σ : Equiv.Perm Coordinate)
    (o : Coordinate → ℝ) (d : ℕ) (p : MvPolynomial Coordinate ℝ)
    (hp : p.totalDegree ≤ d)
    (he : ∀ a b : Vertex, a ≠ b → ∀ t ∈ Icc (0 : ℝ) 1,
      eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) t) p = 0)
    (α : Vertex →₀ ℕ) (hα : α.support.card ≤ 2) :
    coeff α (HomogeneousBarycentric.representation σ o d p) = 0 := by
  apply coefficients_zero_of_edge_traces _ d
    (HomogeneousBarycentric.representation_homogeneous σ o d p) _ α hα
  intro a b hab t ht
  have hh := congrArg (eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) t))
    (HomogeneousBarycentric.substitute_representation σ o d p hp)
  rw [PolynomialCalculus.eval_substitution] at hh
  simp only [barycentric_edge] at hh
  rw [hh]
  exact he a b hab t ht

end FreudenthalSVLean.HomogeneousSkeletonCompleteness
