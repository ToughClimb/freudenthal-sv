import FreudenthalSVLean.BarycentricFaceIntegral

/-!
# Genuine polynomial volume/face integration identity

For manuscript Lemma `means`, the actual derivative volume integral of
every barycentrically represented spatial polynomial is the sum of its
actual triangular face integrals weighted by minus the omitted-vertex
barycentric gradient.  Both sides are genuine Lebesgue integrals.  The
proof uses the arbitrary-exponent triangle and volume formulas and the
structural sum of the four gradients, then polynomial linearity.  It is
not an assumed divergence theorem.  Identifying the gradient weights
with outward vector area and transporting the chart to physical faces
remain separate geometric results.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.BarycentricMonomialMean
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BernsteinPolynomial

noncomputable section

namespace FreudenthalSVLean.BarycentricPolynomialGauss

set_option backward.isDefEq.respectTransparency false

theorem unit_monomial_gauss (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialMonomial σ o α)) =
      ∑ r : Fin 4, -barycentricGradient (R := ℝ) σ r j * faceIntegral r (monomial α 1) := by
  classical
  let c : ℝ := factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ)
  have hs : (∑ r : Fin 4, if α r = 0 then barycentricGradient (R := ℝ) σ r j else 0) +
      (∑ r : Fin 4, if α r = 0 then 0 else barycentricGradient (R := ℝ) σ r j) = 0 := by
    calc
      _ = ∑ r : Fin 4, barycentricGradient (R := ℝ) σ r j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : α r = 0 <;> simp [hr]
      _ = 0 := barycentricGradient_sum σ j
  have hrhs : (∑ r : Fin 4, -barycentricGradient (R := ℝ) σ r j * faceIntegral r (monomial α 1)) =
      -c * ∑ r : Fin 4, if α r = 0 then barycentricGradient (R := ℝ) σ r j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [faceIntegral_monomial]
    by_cases hr : α r = 0
    · simp only [hr, if_true, one_mul]
      dsimp [c]
      ring
    · simp [hr]
  rw [spatialMonomial_derivative_mean, hrhs]
  change c * _ = -c * _
  have hm := congrArg (fun x : ℝ => c * x) hs
  simp only [mul_add, mul_zero] at hm
  linarith

theorem unit_polynomial_gauss (σ : Equiv.Perm (Fin 3)) (o : Space)
    (p : MvPolynomial (Fin 4) ℝ) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (eval₂Hom C (barycentric σ o) p)) =
      ∑ r : Fin 4, -barycentricGradient (R := ℝ) σ r j * faceIntegral r p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | monomial α c =>
      have hm : monomial α c = C c * monomial α (1 : ℝ) := by
        simp only [C_mul_monomial, mul_one]
      rw [hm]
      simp only [map_mul, eval₂Hom_C, pderiv_C_mul, unitSpatialIntegral_C_mul, faceIntegral_C_mul]
      rw [show eval₂Hom C (barycentric σ o) (monomial α 1) = spatialMonomial σ o α from rfl,
        unit_monomial_gauss, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

end FreudenthalSVLean.BarycentricPolynomialGauss
