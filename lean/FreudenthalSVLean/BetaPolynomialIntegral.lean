import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomial beta integrals

The manuscript's Bernstein simplex integral is obtained by successive
integration of barycentric powers.  This module proves the polynomial beta
integral from the fundamental theorem of calculus and the elementary power
integral.  It does not import a simplex integration formula or use a
computer algebra oracle.

The integration interval has an arbitrary real endpoint; its orientation
is the usual signed interval-integral convention.
-/

noncomputable section

namespace FreudenthalSVLean.BetaPolynomialIntegral

open intervalIntegral

/-- Integration by parts recurrence for two nonnegative integer powers. -/
theorem polynomial_beta_recurrence (t : ℝ) (m n : ℕ) :
    (n + 1 : ℝ) * (∫ x in 0..t, (t - x) ^ (m + 1) * x ^ n) =
      (m + 1 : ℝ) * (∫ x in 0..t, (t - x) ^ m * x ^ (n + 1)) := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y => (t - y) ^ (m + 1) * y ^ (n + 1))
        (-(m + 1 : ℝ) * ((t - x) ^ m * x ^ (n + 1)) +
          (n + 1 : ℝ) * ((t - x) ^ (m + 1) * x ^ n)) x := by
    intro x
    convert (((hasDerivAt_const x t).sub (hasDerivAt_id x)).pow (m + 1)).mul
      ((hasDerivAt_id x).pow (n + 1)) using 1 <;>
      first | rfl | (simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        id_eq, Pi.pow_apply, Pi.sub_apply]; ring)
  have hc₁ : Continuous (fun x : ℝ =>
      -(m + 1 : ℝ) * ((t - x) ^ m * x ^ (n + 1))) := by fun_prop
  have hc₂ : Continuous (fun x : ℝ =>
      (n + 1 : ℝ) * ((t - x) ^ (m + 1) * x ^ n)) := by fun_prop
  have he := integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hc₁.add hc₂).intervalIntegrable 0 t)
  rw [integral_add (hc₁.intervalIntegrable 0 t) (hc₂.intervalIntegrable 0 t),
    integral_const_mul, integral_const_mul] at he
  simp only [sub_self, zero_pow (by omega : m + 1 ≠ 0),
    zero_pow (by omega : n + 1 ≠ 0), zero_mul, mul_zero, sub_zero] at he
  linear_combination he

/-- Polynomial beta integral, with the factorial constant proved exactly. -/
theorem polynomial_beta (t : ℝ) (m n : ℕ) :
    (∫ x in 0..t, (t - x) ^ m * x ^ n) =
      (Nat.factorial m : ℝ) * (Nat.factorial n : ℝ) /
        (Nat.factorial (m + n + 1) : ℝ) * t ^ (m + n + 1) := by
  induction m generalizing n with
  | zero =>
      simp only [pow_zero, one_mul, zero_add, Nat.factorial_zero, Nat.cast_one]
      rw [integral_pow]
      simp only [zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
  | succ m ih =>
      have hn : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (mul_left_cancel₀ hn)
      rw [polynomial_beta_recurrence, ih]
      have hexp : m + (n + 1) + 1 = m + 1 + n + 1 := by omega
      simp only [hexp, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

end FreudenthalSVLean.BetaPolynomialIntegral
