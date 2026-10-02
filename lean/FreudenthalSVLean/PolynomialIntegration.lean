import FreudenthalSVLean.PolynomialCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.NormNum

/-!
# Exact integration of multivariate polynomial coordinate sections

This is an integration foundation for manuscript equation `bernstein-mean`.
The polynomial antiderivative is defined coefficientwise and proved to have
the required actual derivative.  The fundamental theorem of calculus then
identifies its endpoint difference with the Lebesgue interval integral.

This module does not yet identify a nested interval integral with volume
integration over a tetrahedron.  That measure-theoretic bridge remains a
separate obligation; the antiderivative is not declared to be the simplex
integral by definition.
-/

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace FreudenthalSVLean.PolynomialIntegration

section Algebra

variable {σ R : Type*} [DecidableEq σ] [Field R] [CharZero R]

/-- Algebraic integration in the `j`th polynomial variable, with zero
constant term in that variable. -/
def antiderivative (j : σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  Finsupp.sum (AddMonoidAlgebra.coeff p) fun α c =>
    monomial (α + Finsupp.single j 1) (c / (α j + 1))

omit [DecidableEq σ] [CharZero R] in
@[simp]
theorem antiderivative_monomial (j : σ) (α : σ →₀ ℕ) (c : R) :
    antiderivative j (monomial α c) =
      monomial (α + Finsupp.single j 1) (c / (α j + 1)) := by
  simp [antiderivative]

omit [DecidableEq σ] [CharZero R] in
theorem antiderivative_add (j : σ) (p q : MvPolynomial σ R) :
    antiderivative j (p + q) = antiderivative j p + antiderivative j q := by
  unfold antiderivative
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_div])

omit [DecidableEq σ] in
/-- The algebraic primitive differentiates back to the original polynomial. -/
theorem pderiv_antiderivative (j : σ) (p : MvPolynomial σ R) :
    pderiv j (antiderivative j p) = p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [antiderivative_add, map_add, hp, hq]
  | monomial α c =>
      have h : (α j + 1 : R) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (α j)
      simp [pderiv_monomial, h]

/-- Algebraic integration with polynomial lower and upper bounds. -/
def coordinateIntegral (j : σ) (a b : MvPolynomial σ R)
    (p : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂Hom C (Function.update X j b) (antiderivative j p) -
    eval₂Hom C (Function.update X j a) (antiderivative j p)

end Algebra

section Analysis

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Actual one-variable derivative of the evaluated algebraic primitive. -/
theorem hasDerivAt_antiderivative (j : σ) (p : MvPolynomial σ ℝ)
    (x : σ → ℝ) (s : ℝ) :
    HasDerivAt (fun t => eval (Function.update x j t) (antiderivative j p))
      (eval (Function.update x j s) p) s := by
  simpa [pderiv_antiderivative] using
    PolynomialCalculus.hasDerivAt_update_eval (antiderivative j p) x j s

/-- An exact coordinate-section integration theorem in Lebesgue measure. -/
theorem integral_update_eval (j : σ) (p : MvPolynomial σ ℝ)
    (x : σ → ℝ) (a b : ℝ) :
    (∫ t in a..b, eval (Function.update x j t) p) =
      eval (Function.update x j b) (antiderivative j p) -
        eval (Function.update x j a) (antiderivative j p) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_antiderivative j p x t
  · have hcont : Continuous (fun t : ℝ => Function.update x j t) :=
      continuous_const.update j continuous_id
    exact (MvPolynomial.continuous_eval p |>.comp hcont).intervalIntegrable a b

/-- Exact symbolic integration with variable polynomial bounds is connected
to actual Lebesgue interval integration at every parameter point. -/
theorem coordinateIntegral_eval (j : σ) (a b p : MvPolynomial σ ℝ)
    (x : σ → ℝ) :
    eval x (coordinateIntegral j a b p) =
      ∫ t in eval x a..eval x b, eval (Function.update x j t) p := by
  rw [coordinateIntegral, map_sub, PolynomialCalculus.eval_substitution,
    PolynomialCalculus.eval_substitution, integral_update_eval]
  have hupdate : ∀ q : MvPolynomial σ ℝ,
      (fun i => eval x (Function.update X j q i)) = Function.update x j (eval x q) := by
    intro q
    funext i
    by_cases hij : i = j <;> simp [hij]
  rw [hupdate, hupdate]

end Analysis

end FreudenthalSVLean.PolynomialIntegration
