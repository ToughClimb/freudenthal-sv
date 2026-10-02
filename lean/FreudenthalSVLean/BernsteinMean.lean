import FreudenthalSVLean.ChainMeasureTransport

/-!
# Exact divergence means from genuine Lebesgue integration

For manuscript equation `bernstein-mean`, this module derives the integral
of each barycentric partial derivative of a Bernstein monomial on every
translated unit Freudenthal tetrahedron.  The integral is a linear functional
on actual multivariate polynomials.  Its linearity follows from integrability
on the proved compact tetrahedron, not from a coefficient definition.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.BernsteinMean

def spatialBarycentric (σ : Equiv.Perm (Fin 3)) (o x : Space) : Fin 4 → ℝ :=
  fun i => eval x (ChainGeometry.barycentric σ o i)

theorem spatialBarycentric_continuous (σ : Equiv.Perm (Fin 3)) (o : Space) :
    Continuous (spatialBarycentric σ o) := by
  apply continuous_pi
  intro i
  exact MvPolynomial.continuous_eval _

theorem polynomial_integrable (σ : Equiv.Perm (Fin 3)) (o : Space)
    (p : MvPolynomial (Fin 4) ℝ) :
    IntegrableOn (fun x => eval (spatialBarycentric σ o x) p) (unitChainSet σ o) :=
  ((MvPolynomial.continuous_eval p).comp (spatialBarycentric_continuous σ o)).continuousOn
    |>.integrableOn_compact (μ := volume) (unitChainSet_isCompact σ o)

/-- Actual tetrahedron integration as a real-linear functional. -/
def unitPolynomialIntegral (σ : Equiv.Perm (Fin 3)) (o : Space) :
    MvPolynomial (Fin 4) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in unitChainSet σ o, eval (spatialBarycentric σ o x) p
  map_add' p q := by
    simp only [map_add]
    exact integral_add (polynomial_integrable σ o p) (polynomial_integrable σ o q)
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

theorem unitPolynomialIntegral_bernstein (σ : Equiv.Perm (Fin 3)) (o : Space)
    (d : ℕ) (α : Fin 4 →₀ ℕ) :
    unitPolynomialIntegral σ o (bernstein (R := ℝ) d α) =
      (Nat.factorial d : ℝ) / (Nat.factorial (α.degree + 3) : ℝ) :=
  unit_bernstein_integral σ o d α

/-- Generic Bernstein derivative integral, including every zero-exponent
case explicitly.  In degree four the nonzero value is `1/30`. -/
theorem unitPolynomialIntegral_pderiv_bernstein (σ : Equiv.Perm (Fin 3))
    (o : Space) (d : ℕ) (α : Fin 4 →₀ ℕ) (hα : α.degree = d + 1) (i : Fin 4) :
    unitPolynomialIntegral σ o (pderiv i (bernstein (R := ℝ) (d + 1) α)) =
      if α i = 0 then 0 else
        (d + 1 : ℝ) * (Nat.factorial d : ℝ) / (Nat.factorial (d + 3) : ℝ) := by
  by_cases hi : α i = 0
  · simp [hi, bernstein, pderiv_monomial]
  · have hle : Finsupp.single i 1 ≤ α :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    let β := α - Finsupp.single i 1
    have he : β + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
    have hd : β.degree = d := by
      have h := congrArg Finsupp.degree he
      rw [map_add, Finsupp.degree_single, hα] at h
      omega
    rw [if_neg hi, ← he, pderiv_bernstein_raised, map_smul,
      unitPolynomialIntegral_bernstein, hd]
    simp [smul_eq_mul, mul_div_assoc]

theorem quartic_pderiv_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (hα : α.degree = 4) (i : Fin 4) :
    unitPolynomialIntegral σ o (pderiv i (bernstein (R := ℝ) 4 α)) =
      if α i = 0 then 0 else 1 / 30 := by
  have h := unitPolynomialIntegral_pderiv_bernstein σ o 3 α hα i
  norm_num at h ⊢
  exact h

theorem unitPolynomialIntegral_C_mul (σ : Equiv.Perm (Fin 3)) (o : Space)
    (c : ℝ) (p : MvPolynomial (Fin 4) ℝ) :
    unitPolynomialIntegral σ o (C c * p) = c * unitPolynomialIntegral σ o p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

/-- The mean of a single quartic Bernstein vector coefficient, written as
one component of the barycentric divergence. -/
theorem quartic_term_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (hα : α.degree = 4) (g : Fin 4 → ℝ) (c : ℝ) :
    unitPolynomialIntegral σ o
      (∑ i : Fin 4, C (c * g i) * pderiv i (bernstein (R := ℝ) 4 α)) =
      c / 30 * ∑ i : Fin 4, if α i = 0 then 0 else g i := by
  simp only [map_sum, unitPolynomialIntegral_C_mul, quartic_pderiv_mean σ o α hα,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : α i = 0
  · simp [hi]
  · simp only [hi, if_false]
    ring

end FreudenthalSVLean.BernsteinMean
