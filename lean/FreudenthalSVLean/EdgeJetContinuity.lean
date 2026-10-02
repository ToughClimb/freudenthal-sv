import FreudenthalSVLean.VertexJetAlgebra
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# Common edge jets from common polynomial traces

For manuscript Lemma `vertex-jets`, equality of conforming traces on a
closed edge implies equality of the issuing directional derivatives,
including at a boundary endpoint.  Here a segment restriction is an actual
one-variable polynomial substitution.  Equality on the interval gives
polynomial equality, and differentiation gives common jets.  A zero
boundary trace gives a zero jet by the same argument.  No endpoint
differentiability convention or mesh-specific compatibility is assumed.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.EdgeJetContinuity

def segmentRestriction {σ : Type*} (x y : σ → ℝ) (p : MvPolynomial σ ℝ) :
    MvPolynomial (Fin 1) ℝ :=
  eval₂Hom C (fun j => C (x j) + C (y j - x j) * X 0) p

theorem segmentRestriction_eval {σ : Type*} (x y : σ → ℝ)
    (p : MvPolynomial σ ℝ) (z : Fin 1 → ℝ) :
    eval z (segmentRestriction x y p) =
      eval (fun j => (1 - z 0) * x j + z 0 * y j) p := by
  rw [segmentRestriction, PolynomialCalculus.eval_substitution]
  apply congrArg (fun t : σ → ℝ => eval t p)
  funext j
  simp only [map_add, map_mul, eval_C, eval_X]
  ring

def directionalJet {σ : Type*} [Fintype σ] (x y : σ → ℝ)
    (p : MvPolynomial σ ℝ) : ℝ :=
  ∑ j : σ, eval x (pderiv j p) * (y j - x j)

/-- The directional jet is derived from the differentiated segment
restriction, rather than defined by an unchecked coefficient formula. -/
theorem segmentRestriction_derivative_zero {σ : Type*} [Fintype σ]
    (x y : σ → ℝ) (p : MvPolynomial σ ℝ) :
    eval (0 : Fin 1 → ℝ) (pderiv 0 (segmentRestriction x y p)) =
      directionalJet x y p := by
  classical
  rw [segmentRestriction, PolynomialCalculus.pderiv_substitution]
  simp only [map_add, pderiv_C, pderiv_C_mul, pderiv_X, Pi.single_apply,
    if_true, mul_one, zero_add, map_sum, map_mul, eval_C,
    PolynomialCalculus.eval_substitution, eval_X, Pi.zero_apply, mul_zero,
    add_zero, directionalJet]

/-- A polynomial's full segment restriction is determined by its values
on the closed geometric edge; this also includes both endpoints. -/
theorem segmentRestriction_eq_of_trace_eq {σ : Type*} (x y : σ → ℝ)
    (p q : MvPolynomial σ ℝ)
    (he : ∀ s ∈ Icc (0 : ℝ) 1,
      eval (fun j => (1 - s) * x j + s * y j) p =
        eval (fun j => (1 - s) * x j + s * y j) q) :
    segmentRestriction x y p = segmentRestriction x y q := by
  apply MvPolynomial.funext_set (fun _ : Fin 1 => Icc (0 : ℝ) 1)
    (fun _ => Icc_infinite zero_lt_one)
  intro z hz
  rw [segmentRestriction_eval, segmentRestriction_eval]
  exact he (z 0) (hz 0 (mem_univ 0))

theorem directionalJet_eq_of_trace_eq {σ : Type*} [Fintype σ]
    (x y : σ → ℝ) (p q : MvPolynomial σ ℝ)
    (he : ∀ s ∈ Icc (0 : ℝ) 1,
      eval (fun j => (1 - s) * x j + s * y j) p =
        eval (fun j => (1 - s) * x j + s * y j) q) :
    directionalJet x y p = directionalJet x y q := by
  have h := congrArg (fun r : MvPolynomial (Fin 1) ℝ =>
    eval (0 : Fin 1 → ℝ) (pderiv 0 r))
      (segmentRestriction_eq_of_trace_eq x y p q he)
  simpa only [segmentRestriction_derivative_zero] using h

theorem directionalJet_zero_of_trace_zero {σ : Type*} [Fintype σ]
    (x y : σ → ℝ) (p : MvPolynomial σ ℝ)
    (he : ∀ s ∈ Icc (0 : ℝ) 1,
      eval (fun j => (1 - s) * x j + s * y j) p = 0) :
    directionalJet x y p = 0 := by
  have h := directionalJet_eq_of_trace_eq x y p 0 (by simpa using he)
  simpa [directionalJet] using h

theorem directionalJet_eq_edgeJet (σ : Equiv.Perm Coordinate)
    (o : Coordinate → ℝ) (a b : Vertex) (p : MvPolynomial Coordinate ℝ) :
    directionalJet (chainVertex σ o a) (chainVertex σ o b) p =
      VertexJetAlgebra.edgeJet σ o a b p := rfl

end FreudenthalSVLean.EdgeJetContinuity
