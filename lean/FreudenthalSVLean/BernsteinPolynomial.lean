import FreudenthalSVLean.PolynomialCalculus
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Bernstein differentiation from actual multivariate polynomials

This module proves the algebraic content of manuscript equation
`bernstein-divergence`.  A Bernstein polynomial is an actual
`MvPolynomial`, with its factorial normalization.  Its derivative is
Mathlib's `pderiv`, not a separately defined coefficient rule.

The statements are generic in the number of barycentric variables, degree,
and characteristic-zero coefficient field.  Polynomial substitution and
real Fréchet differentiation are supplied by `PolynomialCalculus.lean`.
No integration statement is made in this module.
-/

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace FreudenthalSVLean.BernsteinPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [Field R] [CharZero R]

/-- Product of the multi-index factorials, viewed in the scalar field. -/
def factorialProduct (α : σ →₀ ℕ) : R :=
  ∏ i : σ, (Nat.factorial (α i) : R)

omit [DecidableEq σ] in
theorem factorialProduct_ne_zero (α : σ →₀ ℕ) :
    factorialProduct (R := R) α ≠ 0 := by
  unfold factorialProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (α i)

omit [CharZero R] in
/-- Increasing one exponent multiplies its factorial by the new exponent. -/
theorem factorialProduct_raised (α : σ →₀ ℕ) (i : σ) :
    factorialProduct (R := R) (α + Finsupp.single i 1) =
      (α i + 1 : R) * factorialProduct α := by
  have h : ∀ j : σ,
      (Nat.factorial ((α + Finsupp.single i 1 : σ →₀ ℕ) j) : R) =
        (if i = j then (α i + 1 : R) else 1) * (Nat.factorial (α j) : R) := by
    intro j
    by_cases hij : i = j
    · subst j
      simp [Nat.factorial_succ]
    · simp [hij]
  simp only [factorialProduct, h, Finset.prod_mul_distrib]
  simp

/-- The usual factorial normalization `d! / ∏ᵢ αᵢ!`.  Its interpretation as
a degree-`d` Bernstein basis function uses the additional condition `|α|=d`. -/
def normalization (d : ℕ) (α : σ →₀ ℕ) : R :=
  (Nat.factorial d : R) / factorialProduct α

omit [DecidableEq σ] in
theorem normalization_ne_zero (d : ℕ) (α : σ →₀ ℕ) :
    normalization (R := R) d α ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero d
  · exact factorialProduct_ne_zero α

/-- The normalization identity that yields the degree factor in the
Bernstein differentiation formula. -/
theorem normalization_raised (d : ℕ) (α : σ →₀ ℕ) (i : σ) :
    normalization (R := R) (d + 1) (α + Finsupp.single i 1) * (α i + 1) =
      (d + 1) * normalization d α := by
  rw [normalization, normalization, factorialProduct_raised, Nat.factorial_succ]
  push_cast
  have hα : (α i + 1 : R) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (α i)
  field_simp

/-- A normalized barycentric monomial in the polynomial ring. -/
def bernstein (d : ℕ) (α : σ →₀ ℕ) : MvPolynomial σ R :=
  monomial α (normalization d α)

omit [DecidableEq σ] [CharZero R] in
/-- Bernstein normalization is preserved by field homomorphisms. -/
theorem map_bernstein {S : Type*} [Field S] (f : R →+* S)
    (d : ℕ) (α : σ →₀ ℕ) :
    map f (bernstein d α) = bernstein (R := S) d α := by
  simp [bernstein, normalization, factorialProduct]

omit [DecidableEq σ] [CharZero R] in
/-- The normalized barycentric monomial has its declared total degree. -/
theorem bernstein_isHomogeneous (d : ℕ) (α : σ →₀ ℕ) (hα : α.degree = d) :
    IsHomogeneous (bernstein (R := R) d α) d :=
  isHomogeneous_monomial _ hα

omit [Fintype σ] [DecidableEq σ] [CharZero R] in
/-- Differentiation lowers the homogeneous degree by one. -/
theorem isHomogeneous_pderiv (d : ℕ) (p : MvPolynomial σ R)
    (hp : IsHomogeneous p (d + 1)) (i : σ) : IsHomogeneous (pderiv i p) d := by
  intro α hα
  have hc : coeff (α + Finsupp.single i 1) p ≠ 0 := by
    rw [coeff_pderiv] at hα
    exact left_ne_zero_of_mul hα
  have hd : (α + Finsupp.single i 1).degree = d + 1 := by
    simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hp hc
  rw [map_add, Finsupp.degree_single] at hd
  simp only [Pi.one_def, ← Finsupp.degree_eq_weight_one]
  omega

/-- Differentiating a raised Bernstein monomial gives the lower-degree
Bernstein monomial with the exact degree multiplier. -/
theorem pderiv_bernstein_raised (d : ℕ) (α : σ →₀ ℕ) (i : σ) :
    pderiv i (bernstein (R := R) (d + 1) (α + Finsupp.single i 1)) =
      (d + 1 : R) • bernstein d α := by
  simp only [bernstein, pderiv_monomial, add_tsub_cancel_right,
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one,
    smul_monomial, smul_eq_mul]
  rw [normalization_raised]

/-- Coefficient in the normalized Bernstein monomial basis. -/
def bernsteinCoefficient (d : ℕ) (α : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  coeff α p / normalization d α

/-- The normalized monomials have exactly their prescribed Bernstein
coefficients, with no extra basis assumptions. -/
theorem bernsteinCoefficient_basis (d : ℕ) (α β : σ →₀ ℕ) (c : R) :
    bernsteinCoefficient d β (c • bernstein d α) = if α = β then c else 0 := by
  simp only [bernsteinCoefficient, bernstein, coeff_smul, coeff_monomial, smul_eq_mul]
  by_cases h : α = β
  · subst α
    simp [normalization_ne_zero]
  · simp [h]

/-- Generic Bernstein coefficient differentiation, deduced from Mathlib's
proved monomial derivative and the factorial normalization identity. -/
theorem bernsteinCoefficient_pderiv (d : ℕ) (α : σ →₀ ℕ)
    (p : MvPolynomial σ R) (i : σ) :
    bernsteinCoefficient d α (pderiv i p) =
      (d + 1 : R) *
        bernsteinCoefficient (d + 1) (α + Finsupp.single i 1) p := by
  rw [bernsteinCoefficient, bernsteinCoefficient, coeff_pderiv]
  have h := normalization_raised (R := R) d α i
  have h₀ := normalization_ne_zero (R := R) d α
  have h₁ := normalization_ne_zero (R := R) (d + 1) (α + Finsupp.single i 1)
  field_simp
  linear_combination (coeff (α + Finsupp.single i 1) p) * h

omit [DecidableEq σ] [CharZero R] in
/-- Bernstein coefficient extraction is additive over finite sums. -/
theorem bernsteinCoefficient_sum {ι : Type*} (s : Finset ι)
    (d : ℕ) (α : σ →₀ ℕ) (p : ι → MvPolynomial σ R) :
    bernsteinCoefficient d α (∑ j ∈ s, p j) =
      ∑ j ∈ s, bernsteinCoefficient d α (p j) := by
  simp [bernsteinCoefficient, coeff_sum, div_eq_mul_inv, Finset.sum_mul]

omit [DecidableEq σ] [CharZero R] in
/-- Multiplication by a scalar acts on every Bernstein coefficient. -/
theorem bernsteinCoefficient_C_mul (d : ℕ) (α : σ →₀ ℕ)
    (c : R) (p : MvPolynomial σ R) :
    bernsteinCoefficient d α (C c * p) =
      c * bernsteinCoefficient d α p := by
  simp [bernsteinCoefficient, mul_div_assoc]

/-- Divergence written in independent barycentric variables, with the
geometric gradients used as scalar coefficients. -/
def barycentricDivergence {τ : Type*} [Fintype τ]
    (g : σ → τ → R) (v : τ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ j : τ, ∑ i : σ, C (g i j) * pderiv i (v j)

omit [DecidableEq σ] [CharZero R] in
theorem barycentricDivergence_sum {τ ι : Type*} [Fintype τ] [Fintype ι]
    (g : σ → τ → R) (v : ι → τ → MvPolynomial σ R) :
    barycentricDivergence g (fun j => ∑ r : ι, v r j) =
      ∑ r : ι, barycentricDivergence g (v r) := by
  simp only [barycentricDivergence, map_sum, Finset.mul_sum]
  have hi (j : τ) :
      (∑ i : σ, ∑ r : ι, C (g i j) * pderiv i (v r j)) =
        ∑ r : ι, ∑ i : σ, C (g i j) * pderiv i (v r j) := Finset.sum_comm
  simp only [hi]
  exact Finset.sum_comm

omit [DecidableEq σ] [CharZero R] in
theorem barycentricDivergence_coordinate {τ : Type*} [Fintype τ] [DecidableEq τ]
    (g : σ → τ → R) (j₀ : τ) (c : R) (p : MvPolynomial σ R) :
    barycentricDivergence g (fun j => if j₀ = j then c • p else 0) =
      ∑ i : σ, C (c * g i j₀) * pderiv i p := by
  unfold barycentricDivergence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [apply_ite, smul_eq_C_mul, mul_assoc, C_mul,
    mul_comm c]

omit [DecidableEq σ] [CharZero R] in
theorem map_barycentricDivergence {S τ : Type*} [Field S] [Fintype τ]
    (f : R →+* S) (g : σ → τ → R) (v : τ → MvPolynomial σ R) :
    map f (barycentricDivergence g v) =
      barycentricDivergence (fun i j => f (g i j)) (fun j => map f (v j)) := by
  simp [barycentricDivergence, pderiv_map]

/-- Manuscript equation `bernstein-divergence`, proved for arbitrary degree
and number of barycentric variables.  This coefficient formula is a theorem
about the previously defined polynomial derivative. -/
theorem bernsteinCoefficient_divergence {τ : Type*} [Fintype τ]
    (d : ℕ) (α : σ →₀ ℕ) (g : σ → τ → R)
    (v : τ → MvPolynomial σ R) :
    bernsteinCoefficient d α (barycentricDivergence g v) =
      (d + 1 : R) * ∑ i : σ, ∑ j : τ,
        bernsteinCoefficient (d + 1) (α + Finsupp.single i 1) (v j) * g i j := by
  simp only [barycentricDivergence, bernsteinCoefficient_sum,
    bernsteinCoefficient_C_mul, bernsteinCoefficient_pderiv]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum, mul_comm, mul_left_comm]

omit [CharZero R] in
/-- Substituting affine coordinates into a vector polynomial turns the
barycentric divergence into the actual spatial polynomial divergence.
The gradient hypothesis will be supplied by `ChainGeometry.lean`. -/
theorem spatial_divergence_eq_substitution {τ : Type*} [Fintype τ]
    (bary : σ → MvPolynomial τ R) (g : σ → τ → R)
    (hg : ∀ i j, pderiv j (bary i) = C (g i j))
    (v : τ → MvPolynomial σ R) :
    (∑ j : τ, pderiv j (eval₂Hom C bary (v j))) =
      eval₂Hom C bary (barycentricDivergence g v) := by
  simp only [PolynomialCalculus.pderiv_substitution, hg,
    barycentricDivergence, map_sum, map_mul]
  simp [mul_comm]

end FreudenthalSVLean.BernsteinPolynomial
