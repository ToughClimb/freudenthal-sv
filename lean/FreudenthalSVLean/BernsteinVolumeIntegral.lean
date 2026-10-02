import FreudenthalSVLean.BernsteinNestedIntegral
import FreudenthalSVLean.ReferenceChainMeasure
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Actual Bernstein volume integrals on the reference tetrahedron

This module proves the volume-integral part of manuscript equation
`bernstein-mean`.  The integrand is the evaluation of the actual
`MvPolynomial` Bernstein monomial, rather than a coefficient-only functional.
The proof applies to every multi-index and degree.  Fubini and the fundamental
theorem of calculus are supplied by the preceding integration modules.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BernsteinNestedIntegral

noncomputable section

namespace FreudenthalSVLean.BernsteinVolumeIntegral

def referenceBarycentric (p : Point) : Fin 4 → ℝ :=
  ![1 - p.1, p.1 - p.2.1, p.2.1 - p.2.2, p.2.2]

theorem referenceBarycentric_continuous : Continuous referenceBarycentric := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [referenceBarycentric] <;> fun_prop

theorem exponent_degree (α : Fin 4 →₀ ℕ) :
    α.degree = α 0 + α 1 + α 2 + α 3 := by
  rw [Finsupp.degree_eq_sum]
  simp [Fin.sum_univ_succ]
  omega

theorem exponent_factorials (α : Fin 4 →₀ ℕ) :
    factorialProduct (R := ℝ) α =
      (Nat.factorial (α 0) : ℝ) * (Nat.factorial (α 1) : ℝ) *
        (Nat.factorial (α 2) : ℝ) * (Nat.factorial (α 3) : ℝ) := by
  simp [factorialProduct, Fin.prod_univ_succ]
  ring

theorem eval_bernstein_reference (d : ℕ) (α : Fin 4 →₀ ℕ) (p : Point) :
    eval (referenceBarycentric p) (bernstein (R := ℝ) d α) =
      normalization d α *
        ((1 - p.1) ^ (α 0) * ((p.1 - p.2.1) ^ (α 1) *
          ((p.2.1 - p.2.2) ^ (α 2) * p.2.2 ^ (α 3)))) := by
  rw [bernstein, eval_monomial]
  congr 1
  simp [Finsupp.prod_fintype, referenceBarycentric, Fin.prod_univ_succ]

/-- The integral formula for an actual normalized barycentric monomial;
`d` is its normalization degree and `α.degree` its actual monomial degree. -/
theorem bernstein_volume_integral (d : ℕ) (α : Fin 4 →₀ ℕ) :
    (∫ p in chainSet, eval (referenceBarycentric p) (bernstein (R := ℝ) d α)) =
      (Nat.factorial d : ℝ) / (Nat.factorial (α.degree + 3) : ℝ) := by
  have hf : Continuous (fun p : Point =>
      eval (referenceBarycentric p) (bernstein (R := ℝ) d α)) :=
    (MvPolynomial.continuous_eval _).comp referenceBarycentric_continuous
  rw [chain_integral_interval _ hf]
  simp_rw [eval_bernstein_reference]
  simp_rw [intervalIntegral.integral_const_mul (normalization (R := ℝ) d α)]
  rw [nested_barycentric_powers, normalization, exponent_factorials, exponent_degree]
  have hfac : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfac]

/-- Degree-`d` Bernstein basis functions have a common volume integral. -/
theorem bernstein_volume_integral_of_degree (d : ℕ) (α : Fin 4 →₀ ℕ)
    (hα : α.degree = d) :
    (∫ p in chainSet, eval (referenceBarycentric p) (bernstein (R := ℝ) d α)) =
      (Nat.factorial d : ℝ) / (Nat.factorial (d + 3) : ℝ) := by
  rw [bernstein_volume_integral, hα]

theorem cubic_bernstein_volume_integral (α : Fin 4 →₀ ℕ) (hα : α.degree = 3) :
    (∫ p in chainSet, eval (referenceBarycentric p) (bernstein (R := ℝ) 3 α)) =
      1 / 120 := by
  rw [bernstein_volume_integral_of_degree 3 α hα]
  norm_num

end FreudenthalSVLean.BernsteinVolumeIntegral
