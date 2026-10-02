import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Polynomial differentiation used by the skeleton-bubble lifts

The manuscript's skeleton-bubble lemma and equations `chain-gradients` and
`bernstein-divergence` use the product and chain rules for actual polynomial
functions.  This module connects Mathlib's algebraic partial derivatives to
Fréchet derivatives, and proves a substitution chain rule for multivariate
polynomials.  Neither derivative formula is introduced as a definition of
the derivative being verified.

These results do not assert conformity, support, integration, or stability
of a finite-element field; those are separate formalization obligations.
-/

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace FreudenthalSVLean.PolynomialCalculus

section Substitution

variable {R σ τ : Type*} [CommSemiring R] [Fintype σ] [DecidableEq σ]

/-- Algebraic chain rule under an arbitrary polynomial substitution.  In the
manuscript the substituted polynomials are affine barycentric coordinates. -/
theorem pderiv_substitution (bary : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (j : τ) :
    pderiv j (eval₂Hom C bary p) =
      ∑ i : σ, eval₂Hom C bary (pderiv i p) * pderiv j (bary i) := by
  classical
  change pderiv j (eval₂ C bary p) =
    ∑ i : σ, eval₂ C bary (pderiv i p) * pderiv j (bary i)
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [eval₂_add, map_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | mul_X p a hp =>
      have hx : ∑ i : σ, eval₂ C bary (pderiv i (X a)) * pderiv j (bary i) =
          pderiv j (bary a) := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba
          simp [pderiv_X_of_ne (Ne.symm hba)]
        · simp
      have ht : ∑ i : σ, (eval₂ C bary (pderiv i p) * bary a) * pderiv j (bary i) =
          (∑ i : σ, eval₂ C bary (pderiv i p) * pderiv j (bary i)) * bary a := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      simp only [eval₂_mul, eval₂_X, pderiv_mul, hp, eval₂_add,
        add_mul, Finset.sum_add_distrib]
      rw [ht]
      simp_rw [mul_assoc (eval₂ C bary p)]
      rw [← Finset.mul_sum, hx]

end Substitution

section Evaluation

variable {R σ τ : Type*} [CommSemiring R]

/-- Evaluating a polynomial substitution is the actual composition of the
two polynomial evaluations. -/
theorem eval_substitution (bary : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (x : τ → R) :
    eval x (eval₂Hom C bary p) = eval (fun i => eval x (bary i)) p := by
  rw [coe_eval₂Hom, eval_eval₂]
  have hC : (eval x).comp (C : R →+* MvPolynomial τ R) = RingHom.id R := by
    ext c
    simp
  rw [hC, eval₂_id]

end Evaluation

section Analysis

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The continuous linear map given by the evaluated algebraic gradient. -/
def gradientMap (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    (σ → ℝ) →L[ℝ] ℝ :=
  ∑ i : σ, eval x (pderiv i p) • ContinuousLinearMap.proj i

omit [DecidableEq σ] in
@[simp]
theorem gradientMap_C (a : ℝ) (x : σ → ℝ) :
    gradientMap (C a) x = 0 := by
  simp [gradientMap]

@[simp]
theorem gradientMap_X (a : σ) (x : σ → ℝ) :
    gradientMap (X a) x = ContinuousLinearMap.proj a := by
  simp [gradientMap, pderiv_X, Pi.single_apply]

omit [DecidableEq σ] in
@[simp]
theorem gradientMap_add (p q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    gradientMap (p + q) x = gradientMap p x + gradientMap q x := by
  simp [gradientMap, add_smul, Finset.sum_add_distrib]

omit [DecidableEq σ] in
theorem gradientMap_mul (p q : MvPolynomial σ ℝ) (x : σ → ℝ) :
    gradientMap (p * q) x =
      eval x p • gradientMap q x + eval x q • gradientMap p x := by
  ext v
  simp [gradientMap, Finset.sum_add_distrib, Finset.mul_sum,
    mul_add, mul_comm, mul_left_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The evaluated formal partial derivatives are the actual Fréchet
derivative of a multivariate polynomial, at every real point. -/
theorem hasFDerivAt_eval (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y => eval y p) (gradientMap p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (𝕜 := ℝ) a x
  | add p q hp hq => simpa only [gradientMap_add, eval_add] using! hp.add hq
  | mul_X p a hp =>
      simpa [gradientMap_mul] using! hp.mul (hasFDerivAt_apply a x)

/-- Pointwise form of the calculus bridge used for divergence components. -/
theorem fderiv_eval_apply (p : MvPolynomial σ ℝ) (x v : σ → ℝ) :
    fderiv ℝ (fun y => eval y p) x v =
      ∑ i : σ, eval x (pderiv i p) * v i := by
  rw [(hasFDerivAt_eval p x).fderiv]
  simp [gradientMap]

/-- An algebraic partial derivative evaluated at a point is the directional
derivative along the corresponding coordinate unit vector. -/
theorem fderiv_eval_single (p : MvPolynomial σ ℝ) (x : σ → ℝ) (j : σ) :
    fderiv ℝ (fun y => eval y p) x (Pi.single j 1) =
      eval x (pderiv j p) := by
  rw [fderiv_eval_apply]
  simp [Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Differentiation along one coordinate line, for exact interval integration
of multivariate polynomials. -/
theorem hasDerivAt_update_eval (p : MvPolynomial σ ℝ) (x : σ → ℝ)
    (j : σ) (s : ℝ) :
    HasDerivAt (fun t => eval (Function.update x j t) p)
      (eval (Function.update x j s) (pderiv j p)) s := by
  have h := (hasFDerivAt_eval p (Function.update x j s)).comp s
    (hasFDerivAt_update x s)
  have hproj : ∀ i : σ,
      ((Pi.single j (ContinuousLinearMap.id ℝ ℝ) : σ → (ℝ →L[ℝ] ℝ)) i) 1 =
        if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j <;> simp [hij]
  simpa [gradientMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    hproj, Function.comp_def]
    using! h.hasDerivAt

/-- Polynomial divergence, formed using Mathlib's algebraic partials. -/
def polynomialDivergence (v : σ → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ j : σ, pderiv j (v j)

/-- The polynomial divergence evaluates to the trace of the actual spatial
derivative of the polynomial vector field. -/
theorem polynomialDivergence_eval (v : σ → MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval x (polynomialDivergence v) =
      ∑ j : σ, fderiv ℝ (fun y => eval y (v j)) x (Pi.single j 1) := by
  simp [polynomialDivergence, fderiv_eval_single]

end Analysis

end FreudenthalSVLean.PolynomialCalculus
