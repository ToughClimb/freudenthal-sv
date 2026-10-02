import FreudenthalSVLean.BetaPolynomialIntegral
import FreudenthalSVLean.BernsteinPolynomial
import FreudenthalSVLean.ChainGeometry

/-!
# Bernstein integration on the reference coordinate chain

The manuscript's equation `bernstein-mean` uses the common integral of all
degree-`d` Bernstein functions on a unit-determinant tetrahedron.  This
module proves the nested Lebesgue interval-integral formula for the
reference chain `0 ≤ z ≤ y ≤ x ≤ 1`, from polynomial beta integrals.

The factorial constant is proved for arbitrary barycentric exponents;
there is no finite enumeration of cubic indices in this integration proof.
The identification with a volume set integral and transport to the other
coordinate permutations are separate measure-theoretic obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.BetaPolynomialIntegral

noncomputable section

namespace FreudenthalSVLean.BernsteinNestedIntegral

/-- Unnormalized barycentric-power integral on the reference chain. -/
theorem nested_barycentric_powers (a b c d : ℕ) :
    (∫ x in 0..(1 : ℝ), ∫ y in 0..x, ∫ z in 0..y,
      (1 - x) ^ a * ((x - y) ^ b * ((y - z) ^ c * z ^ d))) =
      (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) *
        (Nat.factorial c : ℝ) * (Nat.factorial d : ℝ) /
          (Nat.factorial (a + b + c + d + 3) : ℝ) := by
  let K := (Nat.factorial c : ℝ) * (Nat.factorial d : ℝ) /
    (Nat.factorial (c + d + 1) : ℝ)
  let L := (Nat.factorial b : ℝ) * (Nat.factorial (c + d + 1) : ℝ) /
    (Nat.factorial (b + (c + d + 1) + 1) : ℝ)
  have hinner (x y : ℝ) :
      (∫ z in 0..y, (1 - x) ^ a * ((x - y) ^ b * ((y - z) ^ c * z ^ d))) =
        K * ((1 - x) ^ a * ((x - y) ^ b * y ^ (c + d + 1))) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      polynomial_beta]
    dsimp [K]
    ring
  simp_rw [hinner, intervalIntegral.integral_const_mul, polynomial_beta]
  have houter (x : ℝ) :
      (1 - x) ^ a * (L * x ^ (b + (c + d + 1) + 1)) =
        L * ((1 - x) ^ a * x ^ (b + (c + d + 1) + 1)) := by ring
  change K * (∫ x in 0..1, (1 - x) ^ a *
    (L * x ^ (b + (c + d + 1) + 1))) = _
  simp_rw [houter, intervalIntegral.integral_const_mul, polynomial_beta]
  have hdegree : a + (b + (c + d + 1) + 1) + 1 = a + b + c + d + 3 := by omega
  simp only [one_pow, mul_one, hdegree]
  dsimp [K, L]
  have hf : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]

/-- The usual common Bernstein integral constant follows by cancellation of
the factorial normalization against the unnormalized integral. -/
theorem normalized_nested_barycentric_powers (a b c d : ℕ) :
    ((Nat.factorial (a + b + c + d) : ℝ) /
      ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) *
        (Nat.factorial c : ℝ) * (Nat.factorial d : ℝ))) *
      (∫ x in 0..(1 : ℝ), ∫ y in 0..x, ∫ z in 0..y,
        (1 - x) ^ a * ((x - y) ^ b * ((y - z) ^ c * z ^ d))) =
      (Nat.factorial (a + b + c + d) : ℝ) /
        (Nat.factorial (a + b + c + d + 3) : ℝ) := by
  rw [nested_barycentric_powers]
  have hf : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]

/-- In particular every normalized cubic has integral `1/120` in the
reference nested-interval representation. -/
theorem normalized_cubic_nested_integral (a b c d : ℕ)
    (hdegree : a + b + c + d = 3) :
    ((Nat.factorial 3 : ℝ) /
      ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) *
        (Nat.factorial c : ℝ) * (Nat.factorial d : ℝ))) *
      (∫ x in 0..(1 : ℝ), ∫ y in 0..x, ∫ z in 0..y,
        (1 - x) ^ a * ((x - y) ^ b * ((y - z) ^ c * z ^ d))) = 1 / 120 := by
  have h := normalized_nested_barycentric_powers a b c d
  rw [hdegree] at h
  norm_num at h ⊢
  exact h

end FreudenthalSVLean.BernsteinNestedIntegral
