import FreudenthalSVLean.ChainMeasureTransport
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nondegeneracy of the actual local polynomial L² norm

The manuscript's local inverse estimates and finite-dimensional reference
norm comparisons require the actual volume `L²` quantity, not an unrelated
coefficient norm.  This module proves that its square integral on the
reference tetrahedron vanishes exactly for the zero spatial polynomial.
The proof uses continuity, a genuinely open box inside the tetrahedron,
and polynomial uniqueness on products of infinite sets.  It applies to
arbitrary polynomial degree, with no finite rank assumption.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.PolynomialL2

def boxLower : Space := ![3 / 4, 1 / 2, 0]
def boxUpper : Space := ![1, 3 / 4, 1 / 2]
def referenceOpenBox : Set Space := pi univ (fun j => Ioo (boxLower j) (boxUpper j))

theorem boxLower_lt_boxUpper (j : Fin 3) : boxLower j < boxUpper j := by
  fin_cases j <;> norm_num [boxLower, boxUpper]

theorem referenceOpenBox_isOpen : IsOpen referenceOpenBox :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem referenceOpenBox_subset : referenceOpenBox ⊆ coordinateChainSet := by
  intro x hx
  have h0 := hx 0 (mem_univ 0)
  have h1 := hx 1 (mem_univ 1)
  have h2 := hx 2 (mem_univ 2)
  norm_num [boxLower, boxUpper] at h0 h1 h2
  change (0 : ℝ) < x 2 ∧ x 2 < 1 / 2 at h2
  apply (coordinateChainSet_mem x).mpr
  constructor
  · linarith
  constructor
  · exact h0.2.le
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · exact h2.1.le
  · linarith

def referenceSquareIntegral (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∫ x in coordinateChainSet, (eval x p) ^ 2

theorem referenceSquareIntegral_nonneg (p : MvPolynomial (Fin 3) ℝ) :
    0 ≤ referenceSquareIntegral p := integral_nonneg (fun _ => sq_nonneg _)

/-- The reference integral defines a genuine positive-definite polynomial
quadratic form at every degree. -/
theorem referenceSquareIntegral_eq_zero_iff (p : MvPolynomial (Fin 3) ℝ) :
    referenceSquareIntegral p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    have hc := (MvPolynomial.continuous_eval p).pow 2
    have hi := hc.continuousOn.integrableOn_compact (μ := volume)
      coordinateChainSet_isCompact
    have ha : (fun x : Space => (eval x p) ^ 2) =ᵐ[volume.restrict coordinateChainSet] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hp
    have hb := ae_restrict_of_ae_restrict_of_subset referenceOpenBox_subset ha
    have he := (volume : Measure Space).eqOn_open_of_ae_eq hb
      referenceOpenBox_isOpen hc.continuousOn continuous_zero.continuousOn
    apply MvPolynomial.funext_set
      (fun j => Ioo (boxLower j) (boxUpper j))
      (fun j => Ioo_infinite (boxLower_lt_boxUpper j))
    intro x hx
    have h := he hx
    change (eval x p) ^ 2 = 0 at h
    have hv : eval x p = 0 := by nlinarith
    simpa using hv
  · rintro rfl
    simp [referenceSquareIntegral]

theorem referenceSquareIntegral_pos (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0) :
    0 < referenceSquareIntegral p := by
  have h0 : referenceSquareIntegral p ≠ 0 := by
    intro h
    exact hp ((referenceSquareIntegral_eq_zero_iff p).mp h)
  exact lt_of_le_of_ne (referenceSquareIntegral_nonneg p) h0.symm

end FreudenthalSVLean.PolynomialL2
