import FreudenthalSVLean.ChainGeometry
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Local skeleton-bubble identities

This module formalizes the local polynomial content of manuscript
`lem:skeleton-bubble`, `eq:vertex-raw-bubble`,
`eq:vertex-raw-properties`, and `eq:vertex-face-transfer`.

The product rule is proved for arbitrary finite products, and vanishing
after differentiation is proved from the number of missing barycentric
factors.  The cubic vertex bubble has exactly one prescribed vertex jet;
the cubic face bubble has zero value and zero gradient at every vertex.
The latter facts are about the actual polynomials on every translated
coordinate-chain tetrahedron, not just an enumerated coefficient table.

Global conformity, support, flux normalization, and mean routing are not
asserted here.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.SkeletonBubble

section ProductRule

variable {ι σ R : Type*} [DecidableEq ι] [CommSemiring R]

/-- The product rule in a form suitable for all skeleton bubbles. -/
theorem pderiv_prod (s : Finset ι) (p : ι → MvPolynomial σ R) (j : σ) :
    pderiv j (∏ i ∈ s, p i) =
      ∑ i ∈ s, pderiv j (p i) * ∏ l ∈ s.erase i, p l := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, pderiv_mul, ih, Finset.sum_insert ha,
        Finset.erase_insert ha]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
      rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert]
      · ac_rfl
      · exact fun h => ha (Finset.mem_of_mem_erase h)

/-- The manuscript's skeleton-bubble differentiation rule, for any degree
and any chosen barycentric factors. -/
theorem pderiv_prod_powers (s : Finset ι) (p : ι → MvPolynomial σ R)
    (α : ι → ℕ) (j : σ) :
    pderiv j (∏ i ∈ s, p i ^ α i) =
      ∑ i ∈ s, (α i : MvPolynomial σ R) * p i ^ (α i - 1) *
        pderiv j (p i) * ∏ l ∈ s.erase i, p l ^ α l := by
  rw [pderiv_prod]
  simp only [pderiv_pow]

end ProductRule

section MissingFactors

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

omit [DecidableEq σ] in
/-- A positive power of a missing barycentric coordinate annihilates the
whole monomial. -/
theorem eval_monomial_zero (α : σ →₀ ℕ) (c : R) (x : σ → R)
    (j : σ) (hα : 0 < α j) (hx : x j = 0) :
    eval x (monomial α c) = 0 := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (x i))]
  have hp : ∏ i : σ, x i ^ α i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hx, Nat.ne_of_gt hα])
  rw [hp, mul_zero]

/-- One derivative can remove at most one factor.  Two distinct missing
positive factors therefore annihilate every first derivative. -/
theorem eval_pderiv_zero_of_two_missing (α : σ →₀ ℕ) (c : R) (x : σ → R)
    (a b i : σ) (hab : a ≠ b) (ha : 0 < α a) (hb : 0 < α b)
    (hxa : x a = 0) (hxb : x b = 0) :
    eval x (pderiv i (monomial α c)) = 0 := by
  rw [pderiv_monomial]
  by_cases hia : i = a
  · subst i
    apply eval_monomial_zero _ _ _ b _ hxb
    simpa [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hab] using hb
  · apply eval_monomial_zero _ _ _ a _ hxa
    simpa [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hia] using ha

/-- A repeated missing factor remains after every first derivative. -/
theorem eval_pderiv_zero_of_repeated_missing (α : σ →₀ ℕ) (c : R)
    (x : σ → R) (a i : σ) (ha : 2 ≤ α a) (hxa : x a = 0) :
    eval x (pderiv i (monomial α c)) = 0 := by
  rw [pderiv_monomial]
  apply eval_monomial_zero _ _ _ a _ hxa
  simp only [Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> omega

end MissingFactors

section VertexJets

variable {R : Type*} [CommRing R]

/-- Actual scalar cubic giving the vertex-stage edge jet. -/
def vertexBubble (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b : Vertex) : MvPolynomial Coordinate R :=
  barycentric σ o a ^ 2 * barycentric σ o b

/-- The scalar vertex bubble has zero values at all four vertices. -/
theorem vertexBubble_vertex (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b l : Vertex) (hab : a ≠ b) :
    eval (chainVertex σ o l) (vertexBubble σ o a b) = 0 := by
  simp only [vertexBubble, map_mul, map_pow, barycentric_vertex]
  by_cases ha : a = l
  · subst l
    simp [Ne.symm hab]
  · simp [ha]

/-- Its derivative at `a` is the gradient of the other endpoint's
barycentric coordinate, and it vanishes at all other vertices. -/
theorem pderiv_vertexBubble_vertex (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (a b l : Vertex) (j : Coordinate) (hab : a ≠ b) :
    eval (chainVertex σ o l) (pderiv j (vertexBubble σ o a b)) =
      if l = a then barycentricGradient σ b j else 0 := by
  simp only [vertexBubble, pderiv_mul, pderiv_pow, pderiv_barycentric,
    map_add, map_mul, map_pow, map_natCast, eval_C, barycentric_vertex]
  by_cases ha : a = l
  · subst l
    simp [Ne.symm hab]
  · simp [ha, Ne.symm ha]

/-- The scalar cubic used for face-flux transfers. -/
def faceBubble (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b c : Vertex) : MvPolynomial Coordinate R :=
  barycentric σ o a * barycentric σ o b * barycentric σ o c

/-- Three distinct face vertices give zero value at every tetrahedron
vertex. -/
theorem faceBubble_vertex (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b c l : Vertex) (hab : a ≠ b) :
    eval (chainVertex σ o l) (faceBubble σ o a b c) = 0 := by
  simp only [faceBubble, map_mul, barycentric_vertex]
  by_cases ha : a = l
  · subst l
    simp [Ne.symm hab]
  · simp [ha]

/-- Face-flux transfers preserve all vertex-divergence data because the
gradient of the face bubble vanishes at every vertex. -/
theorem pderiv_faceBubble_vertex (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (a b c l : Vertex) (j : Coordinate)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    eval (chainVertex σ o l) (pderiv j (faceBubble σ o a b c)) = 0 := by
  simp only [faceBubble, pderiv_mul, pderiv_barycentric,
    map_add, map_mul, eval_C, barycentric_vertex]
  by_cases ha : a = l
  · subst l
    simp [Ne.symm hab, Ne.symm hac]
  · by_cases hb : b = l
    · subst l
      simp [hab, Ne.symm hbc]
    · simp [ha, hb]

end VertexJets

end FreudenthalSVLean.SkeletonBubble
