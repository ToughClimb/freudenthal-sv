import FreudenthalSVLean.BetaPolynomialIntegral
import FreudenthalSVLean.ReferenceChainMeasure
import FreudenthalSVLean.BernsteinPolynomial

/-!
# Genuine triangular Bernstein integration for the mean-lift face fluxes

For manuscript Lemma `means`, the integral of the cubic face bubble is
computed on the genuine two-dimensional reference triangle.  Fubini
and the proved polynomial beta integral give the arbitrary-exponent
formula, not a coefficient-defined quadrature rule.  Affine geometric
transport and the outward vector area enter the later face-flux stage.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.BetaPolynomialIntegral
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BernsteinPolynomial

noncomputable section

namespace FreudenthalSVLean.TriangleBernsteinIntegral

abbrev FacePoint := ℝ × ℝ
def triangleBarycentric (p : FacePoint) : Fin 3 → ℝ := ![1 - p.1, p.1 - p.2, p.2]

theorem triangleBarycentric_continuous : Continuous triangleBarycentric := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [triangleBarycentric] <;> fun_prop

theorem triangle_integral_interval (f : FacePoint → ℝ) (hf : Continuous f) :
    (∫ p in triangleSet 1, f p) = ∫ x in 0..(1 : ℝ), ∫ y in 0..x, f (x, y) := by
  rw [triangle_integral 1 f hf, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  change (∫ y in Icc 0 x, f (x, y)) = ∫ y in 0..x, f (x, y)
  rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]

theorem nested_triangle_powers (a b c : ℕ) :
    (∫ x in 0..(1 : ℝ), ∫ y in 0..x, (1 - x) ^ a * ((x - y) ^ b * y ^ c)) =
      (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ) /
        (Nat.factorial (a + b + c + 2) : ℝ) := by
  let K : ℝ := (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ) /
    (Nat.factorial (b + c + 1) : ℝ)
  simp_rw [intervalIntegral.integral_const_mul, polynomial_beta]
  change (∫ x in 0..1, (1 - x) ^ a * (K * x ^ (b + c + 1))) = _
  have he (x : ℝ) : (1 - x) ^ a * (K * x ^ (b + c + 1)) =
      K * ((1 - x) ^ a * x ^ (b + c + 1)) := by ring
  simp_rw [he, intervalIntegral.integral_const_mul, polynomial_beta]
  have hd : a + (b + c + 1) + 1 = a + b + c + 2 := by omega
  simp only [one_pow, mul_one, hd]
  dsimp [K]
  have hf (n : ℕ) : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hf]

theorem triangle_barycentric_powers (a b c : ℕ) :
    (∫ p in triangleSet 1, (1 - p.1) ^ a * ((p.1 - p.2) ^ b * p.2 ^ c)) =
      (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ) /
        (Nat.factorial (a + b + c + 2) : ℝ) := by
  rw [triangle_integral_interval _ (by fun_prop)]
  exact nested_triangle_powers a b c

theorem triangle_monomial_integral (α : Fin 3 →₀ ℕ) (c : ℝ) :
    (∫ p in triangleSet 1, eval (triangleBarycentric p) (monomial α c)) =
      c * factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ) := by
  have he (p : FacePoint) : eval (triangleBarycentric p) (monomial α c) =
      c * ((1 - p.1) ^ (α 0) * ((p.1 - p.2) ^ (α 1) * p.2 ^ (α 2))) := by
    rw [eval_monomial]
    congr 1
    simp [Finsupp.prod_fintype, triangleBarycentric, Fin.prod_univ_succ]
  have hd : α.degree = α 0 + α 1 + α 2 := by
    rw [Finsupp.degree_eq_sum]
    simp [Fin.sum_univ_succ]
    omega
  have hf : factorialProduct (R := ℝ) α =
      (Nat.factorial (α 0) : ℝ) * (Nat.factorial (α 1) : ℝ) * (Nat.factorial (α 2) : ℝ) := by
    simp [factorialProduct, Fin.prod_univ_succ]
    ring
  simp_rw [he, integral_const_mul]
  rw [triangle_barycentric_powers, hd, hf]
  ring

theorem cubic_face_bubble_integral :
    (∫ p in triangleSet 1, (1 - p.1) * ((p.1 - p.2) * p.2)) = 1 / 120 := by
  have h := triangle_barycentric_powers 1 1 1
  norm_num at h ⊢
  exact h

end FreudenthalSVLean.TriangleBernsteinIntegral
