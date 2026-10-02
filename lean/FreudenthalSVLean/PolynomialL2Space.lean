import FreudenthalSVLean.PolynomialL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A genuine L² norm on spatial polynomials and local inverse estimates

The local inverse estimates in the manuscript's vertex and edge stages use
the actual tetrahedron `L²` norm.  This module embeds spatial polynomials
injectively into the Lebesgue `L²` space on the reference tetrahedron and
uses its induced norm.  On each fixed-degree polynomial subspace, evaluation
is then a bounded linear functional by finite-dimensional normed-space
theory.  No assumed coefficient/volume norm equivalence is introduced.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.PolynomialL2

noncomputable section

namespace FreudenthalSVLean.PolynomialL2Space

set_option backward.isDefEq.respectTransparency false

def SpatialPolynomialL2 : Type := MvPolynomial (Fin 3) ℝ

instance : AddCommGroup SpatialPolynomialL2 :=
  inferInstanceAs (AddCommGroup (MvPolynomial (Fin 3) ℝ))

instance : Module ℝ SpatialPolynomialL2 :=
  inferInstanceAs (Module ℝ (MvPolynomial (Fin 3) ℝ))

abbrev ReferenceL2 := Lp ℝ 2 (volume.restrict coordinateChainSet)

theorem polynomial_memLp (p : MvPolynomial (Fin 3) ℝ) :
    MemLp (fun x : Space => eval x p) 2 (volume.restrict coordinateChainSet) := by
  have hc := MvPolynomial.continuous_eval p
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  exact (hc.pow 2).continuousOn.integrableOn_compact (μ := volume)
    coordinateChainSet_isCompact

def toReferenceL2 : SpatialPolynomialL2 →ₗ[ℝ] ReferenceL2 where
  toFun p := (polynomial_memLp p).toLp (fun x => eval x p)
  map_add' p q := by
    have hf : (fun x : Space => eval x (p + q)) =
        (fun x => eval x p) + (fun x => eval x q) := by
      funext x
      change eval x ((p : MvPolynomial (Fin 3) ℝ) + q) = eval x p + eval x q
      exact map_add _ _ _
    exact (MemLp.toLp_congr (polynomial_memLp (p + q))
      ((polynomial_memLp p).add (polynomial_memLp q)) (Filter.Eventually.of_forall
        (congrFun hf))).trans (MemLp.toLp_add (polynomial_memLp p) (polynomial_memLp q))
  map_smul' c p := by
    have hf : (fun x : Space => eval x (c • p)) = c • (fun x => eval x p) := by
      funext x
      change eval x (c • (p : MvPolynomial (Fin 3) ℝ)) = c * eval x p
      exact MvPolynomial.smul_eval x (p : MvPolynomial (Fin 3) ℝ) c
    exact (MemLp.toLp_congr (polynomial_memLp (c • p))
      ((polynomial_memLp p).const_smul c) (Filter.Eventually.of_forall
        (congrFun hf))).trans (MemLp.toLp_const_smul c (polynomial_memLp p))

theorem toReferenceL2_injective : Function.Injective toReferenceL2 := by
  intro p q hpq
  have ha : (fun x : Space => eval x p) =ᵐ[volume.restrict coordinateChainSet]
      (fun x => eval x q) :=
    (MemLp.toLp_eq_toLp_iff (polynomial_memLp p) (polynomial_memLp q)).mp hpq
  have hb := ae_restrict_of_ae_restrict_of_subset referenceOpenBox_subset ha
  have he := (volume : Measure Space).eqOn_open_of_ae_eq hb referenceOpenBox_isOpen
    (MvPolynomial.continuous_eval p).continuousOn (MvPolynomial.continuous_eval q).continuousOn
  exact MvPolynomial.funext_set (fun j => Ioo (boxLower j) (boxUpper j))
    (fun j => Set.Ioo_infinite (boxLower_lt_boxUpper j)) (fun _ hx => he hx)

instance : NormedAddCommGroup SpatialPolynomialL2 :=
  NormedAddCommGroup.induced SpatialPolynomialL2 ReferenceL2
    toReferenceL2.toAddMonoidHom toReferenceL2_injective

instance : NormedSpace ℝ SpatialPolynomialL2 :=
  NormedSpace.induced ℝ SpatialPolynomialL2 ReferenceL2 toReferenceL2

/-- The induced norm is literally the actual volume `L²` norm. -/
theorem norm_square_eq_integral (p : SpatialPolynomialL2) :
    ‖p‖ ^ 2 = referenceSquareIntegral p := by
  change ‖toReferenceL2 p‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (polynomial_memLp p)] with x hx
  simp [toReferenceL2, hx, pow_two]

def degreeSpace (d : ℕ) : Submodule ℝ SpatialPolynomialL2 :=
  restrictTotalDegree (Fin 3) ℝ d

instance (d : ℕ) : FiniteDimensional ℝ (degreeSpace d) :=
  inferInstanceAs (FiniteDimensional ℝ (restrictTotalDegree (Fin 3) ℝ d))

def pointEvaluation (d : ℕ) (x : Space) : degreeSpace d →ₗ[ℝ] ℝ where
  toFun p := eval x p.val
  map_add' p q := by
    change eval x ((p.val : MvPolynomial (Fin 3) ℝ) + q.val) = eval x p.val + eval x q.val
    exact map_add _ _ _
  map_smul' c p := by
    change eval x (c • (p.val : MvPolynomial (Fin 3) ℝ)) = c * eval x p.val
    exact MvPolynomial.smul_eval x (p.val : MvPolynomial (Fin 3) ℝ) c

/-- Fixed-degree evaluation is uniformly bounded on the reference element
in the genuine volume norm.  The constant is independent of a mesh size. -/
theorem point_evaluation_bound (d : ℕ) (x : Space) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : degreeSpace d, |eval x p.val| ≤ C * ‖p‖ := by
  let T : degreeSpace d →L[ℝ] ℝ := (pointEvaluation d x).toContinuousLinearMap
  refine ⟨max 1 ‖T‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro p
  have h := T.le_opNorm p
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg p))

/-- The point estimate expressed entirely in terms of a Lebesgue integral,
as needed by the manuscript's vertex-data inverse estimate. -/
theorem point_evaluation_squared_bound (d : ℕ) (x : Space) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : degreeSpace d,
      (eval x p.val) ^ 2 ≤ C * referenceSquareIntegral p.val := by
  obtain ⟨C, hC, h⟩ := point_evaluation_bound d x
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro p
  have hs := (sq_le_sq₀ (abs_nonneg (eval x p.val))
    (mul_nonneg hC.le (norm_nonneg p))).mpr (h p)
  have hnorm : ‖p‖ ^ 2 = referenceSquareIntegral p.val :=
    norm_square_eq_integral p.val
  simpa only [sq_abs, mul_pow, hnorm] using hs

/-- A fixed linear polynomial lift has a genuine integral-norm bound on a
fixed-degree reference input space.  This is the finite-dimensional norm
step in the manuscript's local lifting estimates, not a global mesh claim. -/
theorem linear_map_energy_bound (d : ℕ)
    (L : degreeSpace d →ₗ[ℝ] SpatialPolynomialL2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : degreeSpace d,
      referenceSquareIntegral (L p) ≤ C * referenceSquareIntegral p.val := by
  let T : degreeSpace d →L[ℝ] SpatialPolynomialL2 := L.toContinuousLinearMap
  let C : ℝ := max 1 ‖T‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro p
  have h : ‖T p‖ ≤ C * ‖p‖ :=
    (T.le_opNorm p).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg p))
  have hs := (sq_le_sq₀ (norm_nonneg (T p))
    (mul_nonneg hC.le (norm_nonneg p))).mpr h
  have hnorm : ‖p‖ ^ 2 = referenceSquareIntegral p.val :=
    norm_square_eq_integral p.val
  simpa only [mul_pow, hnorm, norm_square_eq_integral] using! hs

def derivativeLinear (d : ℕ) (i : Fin 3) : degreeSpace d →ₗ[ℝ] SpatialPolynomialL2 where
  toFun p := pderiv i p.val
  map_add' p q := by
    change pderiv i ((p.val : MvPolynomial (Fin 3) ℝ) + q.val) =
      pderiv i p.val + pderiv i q.val
    exact map_add _ _ _
  map_smul' c p := by
    change pderiv i (c • (p.val : MvPolynomial (Fin 3) ℝ)) = c • pderiv i p.val
    exact (pderiv i).map_smul c (p.val : MvPolynomial (Fin 3) ℝ)

/-- A derivative inverse estimate with the actual volume norm. -/
theorem derivative_energy_bound (d : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : degreeSpace d,
      referenceSquareIntegral (pderiv i p.val) ≤ C * referenceSquareIntegral p.val :=
  linear_map_energy_bound d (derivativeLinear d i)

def vectorComponentDerivative (d : ℕ)
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] (Fin 3 → MvPolynomial (Fin 3) ℝ))
    (j i : Fin 3) : degreeSpace d →ₗ[ℝ] SpatialPolynomialL2 where
  toFun p := pderiv i (L p.val j)
  map_add' p q := by
    change pderiv i (L ((p.val : MvPolynomial (Fin 3) ℝ) + q.val) j) =
      pderiv i (L p.val j) + pderiv i (L q.val j)
    rw [L.map_add]
    simp only [Pi.add_apply, map_add]
  map_smul' c p := by
    change pderiv i (L (c • (p.val : MvPolynomial (Fin 3) ℝ)) j) =
      c • pderiv i (L p.val j)
    rw [L.map_smul]
    simp only [Pi.smul_apply]
    exact (pderiv i).map_smul c (L p.val j)

/-- The manuscript's fixed-reference lifting estimate in the actual
gradient energy.  All nine derivative components of any fixed linear
polynomial lifting operator are controlled by the input's volume norm. -/
theorem vector_linear_lift_energy_bound (d : ℕ)
    (L : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] (Fin 3 → MvPolynomial (Fin 3) ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : degreeSpace d,
      (∑ j : Fin 3, ∑ i : Fin 3, referenceSquareIntegral (pderiv i (L p.val j))) ≤
        C * referenceSquareIntegral p.val := by
  choose C hC hb using fun j i : Fin 3 =>
    linear_map_energy_bound d (vectorComponentDerivative d L j i)
  refine ⟨∑ j : Fin 3, ∑ i : Fin 3, C j i, ?_, ?_⟩
  · apply Finset.sum_pos _ Finset.univ_nonempty
    intro j _
    exact Finset.sum_pos (fun i _ => hC j i) Finset.univ_nonempty
  · intro p
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    exact hb j i p

end FreudenthalSVLean.PolynomialL2Space
