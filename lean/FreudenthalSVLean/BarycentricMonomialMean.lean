import FreudenthalSVLean.FaceBubbleMean

/-!
# A structural derivative-mean identity for barycentric monomials

For manuscript equations `bernstein-mean` and `endpoint-face-bubble`,
the integral of each nonzero barycentric partial of an unnormalized
monomial has the same value, independent of the differentiated positive
exponent.  Spatial differentiation therefore sums precisely the gradients
of the vertices present in the monomial.  Full-support monomials have zero
derivative mean; face-supported monomials give an omitted-vertex gradient.
These are true volume-integral identities, not coefficient definitions.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BernsteinMean
open FreudenthalSVLean.FaceBubbleMean

noncomputable section

namespace FreudenthalSVLean.BarycentricMonomialMean

theorem monomial_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (i : Fin 4) :
    unitPolynomialIntegral σ o (pderiv i (monomial α (1 : ℝ))) =
      if α i = 0 then 0 else
        factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ) := by
  classical
  by_cases hi : α i = 0
  · simp [hi, pderiv_monomial]
  · have hle : Finsupp.single i 1 ≤ α :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    let β := α - Finsupp.single i 1
    have he : β + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
    have hd : α.degree = β.degree + 1 := by
      rw [← he, map_add, Finsupp.degree_single]
    rw [pderiv_monomial, monomial_mean, if_neg hi]
    simp only [one_mul]
    have hf := factorialProduct_raised (R := ℝ) β i
    rw [he] at hf
    have ha : (α i : ℝ) = (β i : ℝ) + 1 := by
      have ha := congrArg (fun a : Fin 4 →₀ ℕ => a i) he
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at ha
      exact_mod_cast ha.symm
    change (α i : ℝ) * factorialProduct β /
      (Nat.factorial (β.degree + 3) : ℝ) = _
    rw [ha, ← hf, hd]

def spatialMonomial (σ : Equiv.Perm (Fin 3)) (o : Space) (α : Fin 4 →₀ ℕ) :
    MvPolynomial (Fin 3) ℝ := eval₂Hom C (barycentric σ o) (monomial α 1)

theorem spatialMonomial_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialMonomial σ o α)) =
      (factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ)) *
        (∑ a : Fin 4, if α a = 0 then 0 else barycentricGradient (R := ℝ) σ a j) := by
  have he : pderiv j (spatialMonomial σ o α) = eval₂Hom C (barycentric σ o)
      (∑ a : Fin 4, C (barycentricGradient (R := ℝ) σ a j) * pderiv a (monomial α (1 : ℝ))) := by
    rw [spatialMonomial, PolynomialCalculus.pderiv_substitution]
    simp only [map_sum, map_mul, eval₂Hom_C, pderiv_barycentric]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he]
  change (∫ x in unitChainSet σ o, eval x (eval₂Hom C (barycentric σ o)
    (∑ a : Fin 4, C (barycentricGradient (R := ℝ) σ a j) * pderiv a (monomial α (1 : ℝ))))) = _
  simp only [PolynomialCalculus.eval_substitution]
  change unitPolynomialIntegral σ o
    (∑ a : Fin 4, C (barycentricGradient (R := ℝ) σ a j) * pderiv a (monomial α (1 : ℝ))) = _
  simp only [map_sum, unitPolynomialIntegral_C_mul, monomial_derivative_mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : α a = 0
  · simp [ha]
  · simp only [ha, if_false]; ring

/-- Every monomial containing all four barycentric factors has zero
spatial derivative mean, regardless of the positive exponents. -/
theorem fullSupport_derivative_mean_zero (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (hα : ∀ a, α a ≠ 0) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialMonomial σ o α)) = 0 := by
  rw [spatialMonomial_derivative_mean]
  simp only [hα, if_false, barycentricGradient_sum, mul_zero]

/-- For face support the derivative mean depends only on the missing
vertex gradient and the symmetric factorial coefficient. -/
theorem faceSupport_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (r : Fin 4) (hr : α r = 0) (hα : ∀ a, a ≠ r → α a ≠ 0)
    (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialMonomial σ o α)) =
      -(factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ)) *
        barycentricGradient (R := ℝ) σ r j := by
  rw [spatialMonomial_derivative_mean]
  have hs : (∑ a : Fin 4, if α a = 0 then 0 else barycentricGradient (R := ℝ) σ a j) =
      -barycentricGradient (R := ℝ) σ r j := by
    have he : (∑ a : Fin 4, if α a = 0 then 0 else barycentricGradient (R := ℝ) σ a j) +
        barycentricGradient (R := ℝ) σ r j =
          ∑ a : Fin 4, barycentricGradient (R := ℝ) σ a j := by
      have hd : (∑ a : Fin 4, if a = r then barycentricGradient (R := ℝ) σ a j else 0) =
          barycentricGradient (R := ℝ) σ r j := by simp
      rw [← hd, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = r
      · subst a; simp [hr]
      · simp [hα a ha, ha]
    rw [barycentricGradient_sum] at he
    linarith
  rw [hs]
  ring

end FreudenthalSVLean.BarycentricMonomialMean
