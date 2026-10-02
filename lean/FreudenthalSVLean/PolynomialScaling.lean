import FreudenthalSVLean.ScaledChainGeometry
import FreudenthalSVLean.PolynomialDegree

/-!
# Exact polynomial mean and gradient-energy scaling

The manuscript's equation `macro-scale` uses `h⁻² w(x/h)` to preserve
divergence means, with squared gradient energy scaling as `h⁻³`.
This module proves these identities from actual polynomial differentiation
and Lebesgue integration.  It does not assume a Sobolev scaling law or
derive a global stability constant without the local lifting estimates.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.PolynomialScaling

def rescale (h a : ℝ) (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  C a * eval₂Hom C (fun j => C h⁻¹ * X j) p

def rescaleLinear (h a : ℝ) : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun := rescale h a
  map_add' p q := by simp only [rescale, map_add, mul_add]
  map_smul' c p := by
    simp only [rescale, smul_eq_C_mul, map_mul, eval₂Hom_C, RingHom.id_apply]
    ring

theorem rescale_eval (h a : ℝ) (p : MvPolynomial (Fin 3) ℝ) (x : Space) :
    eval x (rescale h a p) = a * eval (h⁻¹ • x) p := by
  rw [rescale, map_mul, eval_C, PolynomialCalculus.eval_substitution]
  simp [Pi.smul_def, smul_eq_mul]

theorem rescale_degree_le (h a : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (rescale h a p).totalDegree ≤ p.totalDegree := by
  have he : (eval₂Hom C (fun j : Fin 3 => C h⁻¹ * X j) p).totalDegree ≤ p.totalDegree := by
    apply PolynomialDegree.affine_substitution_degree
    intro j
    exact (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using he)

theorem pderiv_rescale (h a : ℝ) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    pderiv i (rescale h a p) = rescale h (a * h⁻¹) (pderiv i p) := by
  rw [rescale, pderiv_C_mul, PolynomialCalculus.pderiv_substitution]
  simp [rescale, pderiv_X, Pi.single_apply, C_mul, mul_assoc, mul_comm]

theorem divergence_rescale (h a : ℝ) (v : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    PolynomialCalculus.polynomialDivergence (fun j => rescale h a (v j)) =
      rescale h (a * h⁻¹) (PolynomialCalculus.polynomialDivergence v) := by
  simp_rw [PolynomialCalculus.polynomialDivergence, pderiv_rescale]
  simp [rescale, map_sum, Finset.mul_sum]

theorem derivative_mean_scaling (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (∫ x in scaledChainSet σ o h, eval x (pderiv i (rescale h a p))) =
      a * h ^ 2 * ∫ y in unitChainSet σ o, eval y (pderiv i p) := by
  simp only [pderiv_rescale, rescale_eval]
  rw [integral_const_mul, scaled_chain_integral σ o h hh
    (fun y => eval y (pderiv i p))]
  field_simp [hh.ne']

/-- The macroelement amplitude `h⁻²` preserves each divergence summand mean. -/
theorem mean_preserving_derivative_scaling (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (∫ x in scaledChainSet σ o h,
      eval x (pderiv i (rescale h (h ^ 2)⁻¹ p))) =
        ∫ y in unitChainSet σ o, eval y (pderiv i p) := by
  rw [derivative_mean_scaling σ o h hh]
  simp [hh.ne']

/-- The mean-preserving macro amplitude preserves the actual polynomial
divergence integral of an arbitrary vector polynomial. -/
theorem mean_preserving_divergence_scaling (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (v : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∫ x in scaledChainSet σ o h, eval x
      (PolynomialCalculus.polynomialDivergence (fun j => rescale h (h ^ 2)⁻¹ (v j)))) =
      ∫ y in unitChainSet σ o, eval y (PolynomialCalculus.polynomialDivergence v) := by
  rw [divergence_rescale]
  simp only [rescale_eval]
  rw [integral_const_mul, scaled_chain_integral σ o h hh
    (fun y => eval y (PolynomialCalculus.polynomialDivergence v))]
  field_simp [hh.ne']

theorem derivative_energy_scaling (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (∫ x in scaledChainSet σ o h, (eval x (pderiv i (rescale h a p))) ^ 2) =
      a ^ 2 * h * ∫ y in unitChainSet σ o, (eval y (pderiv i p)) ^ 2 := by
  simp only [pderiv_rescale, rescale_eval, mul_pow]
  rw [integral_const_mul, scaled_chain_integral σ o h hh
    (fun y => (eval y (pderiv i p)) ^ 2)]
  field_simp [hh.ne']

/-- Squared local gradient energy has exactly the factor used in the
quartic macro's `h⁻³/²` seminorm estimate. -/
theorem macro_derivative_energy_scaling (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (∫ x in scaledChainSet σ o h,
      (eval x (pderiv i (rescale h (h ^ 2)⁻¹ p))) ^ 2) =
        (h ^ 3)⁻¹ * ∫ y in unitChainSet σ o, (eval y (pderiv i p)) ^ 2 := by
  rw [derivative_energy_scaling σ o h hh]
  field_simp [hh.ne']

end FreudenthalSVLean.PolynomialScaling
