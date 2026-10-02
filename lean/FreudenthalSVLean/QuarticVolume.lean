import FreudenthalSVLean.BernsteinMean
import FreudenthalSVLean.QuarticSpatial

/-!
# Genuine volume means of the eleven quartic macro fields

This module connects the manuscript's displayed fields and equations
`bernstein-mean` and `quartic-mean-matrix` to actual Lebesgue volume
integrals of their spatial divergence.  It uses the generic proved
Bernstein integration rule, not the original coefficient functional as
the definition of a mean.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticPolynomial
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BernsteinMean
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.QuarticVolume

def realTermDivergence (t : TetIndex) (w : FieldIndex) (r : TermIndex) :
    MvPolynomial LocalVertex ℝ :=
  if pointInTet t (macroTerms w r).point = true then
    ∑ i : LocalVertex,
      C ((macroTerms w r).coefficient *
        (barycentricGradient t i (macroTerms w r).component : ℝ)) *
          pderiv i (bernstein 4
            (integerExponent (scaledBarycentric t (macroTerms w r).point)))
  else 0

theorem realLocalDivergence_terms (t : TetIndex) (w : FieldIndex) :
    map (Rat.castHom ℝ) (localDivergencePolynomial t w) =
      ∑ r : TermIndex, realTermDivergence t w r := by
  rw [localDivergencePolynomial, map_barycentricDivergence]
  have hv : (fun j => map (Rat.castHom ℝ) (localVectorPolynomial t w j)) =
      fun j => ∑ r : TermIndex,
        if pointInTet t (macroTerms w r).point = true ∧
          (macroTerms w r).component = j then
            ((macroTerms w r).coefficient : ℝ) • bernstein 4
              (integerExponent (scaledBarycentric t (macroTerms w r).point))
        else 0 := by
    funext j
    simp only [localVectorPolynomial, map_sum, smul_eq_C_mul]
    simp_rw [apply_ite, map_mul, map_C, map_bernstein, map_zero]
    rfl
  rw [hv, barycentricDivergence_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : pointInTet t (macroTerms w r).point = true
  · simp only [realTermDivergence, hp, true_and, if_true]
    exact barycentricDivergence_coordinate _ _ _ _
  · simp [realTermDivergence, hp, barycentricDivergence]

theorem realTermDivergence_integral (t : TetIndex) (w : FieldIndex) (r : TermIndex) :
    unitPolynomialIntegral (tetEquiv t) (realCellCorner t) (realTermDivergence t w r) =
      if pointInTet t (macroTerms w r).point = true then
        ((macroTerms w r).coefficient : ℝ) / 30 *
          ∑ i : LocalVertex,
            if 0 < scaledBarycentric t (macroTerms w r).point i then
              (barycentricGradient t i (macroTerms w r).component : ℝ)
            else 0
      else 0 := by
  by_cases hp : pointInTet t (macroTerms w r).point = true
  · rw [realTermDivergence, if_pos hp, if_pos hp,
      quartic_term_mean _ _ _ (integerExponent_degree t _ hp)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpos : 0 < scaledBarycentric t (macroTerms w r).point i
    · have hn : (scaledBarycentric t (macroTerms w r).point i).toNat ≠ 0 :=
        by omega
      simp [integerExponent, hpos, hn]
    · have hn : (scaledBarycentric t (macroTerms w r).point i).toNat = 0 :=
        Int.toNat_eq_zero.mpr (le_of_not_gt hpos)
      simp [integerExponent, hpos, hn]
  · simp [realTermDivergence, hp]

/-- The exact coefficient mean in the original certificate equals the actual
Lebesgue integral on the corresponding unit tetrahedron. -/
theorem localDivergence_integral_eq_certificate (t : TetIndex) (w : FieldIndex) :
    unitPolynomialIntegral (tetEquiv t) (realCellCorner t)
      (map (Rat.castHom ℝ) (localDivergencePolynomial t w)) =
        (divergenceMean t w : ℝ) := by
  rw [realLocalDivergence_terms, map_sum]
  simp_rw [realTermDivergence_integral]
  change _ = (Rat.castHom ℝ) (scaledDivergenceMean t w / 30)
  rw [map_div₀]
  simp only [scaledDivergenceMean, map_sum]
  simp only [apply_ite, map_mul, map_sum, map_zero]
  simp [div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm]

/-- The finite exact matrix is the matrix of genuine real-volume means. -/
theorem localDivergence_integral_eq_matrix (i j : FieldIndex) :
    unitPolynomialIntegral (tetEquiv (firstElevenTet i))
      (realCellCorner (firstElevenTet i))
      (map (Rat.castHom ℝ) (localDivergencePolynomial (firstElevenTet i) j)) =
        (FreudenthalSVLean.QuarticMacro.quarticMeanMatrix i j : ℝ) / 30 := by
  rw [localDivergence_integral_eq_certificate, divergenceMean_eq_matrix_div_thirty]
  push_cast
  rfl

/-- Actual spatial polynomial divergence, integrated with Cartesian
Lebesgue volume on its translated/permuted tetrahedron. -/
theorem spatialDivergence_volume_mean (t : TetIndex) (w : FieldIndex) :
    (∫ x in unitChainSet (tetEquiv t) (realCellCorner t),
      eval x (realSpatialDivergence t w)) = (divergenceMean t w : ℝ) := by
  simp only [realSpatialDivergence_eq_substitution,
    PolynomialCalculus.eval_substitution]
  exact localDivergence_integral_eq_certificate t w

/-- The mean identity holds for the trace of the actual Fréchet derivative,
not only for the syntactic polynomial derivative. -/
theorem actualDivergence_volume_mean (t : TetIndex) (w : FieldIndex) :
    (∫ x in unitChainSet (tetEquiv t) (realCellCorner t),
      ∑ j : SpatialIndex,
        fderiv ℝ (fun y => eval y (realSpatialVector t w j)) x (Pi.single j 1)) =
          (divergenceMean t w : ℝ) := by
  simp_rw [← realSpatialDivergence_eval]
  exact spatialDivergence_volume_mean t w

/-- The first eleven genuine means are exactly the displayed matrix `A/30`. -/
theorem actualDivergence_mean_matrix (i j : FieldIndex) :
    (∫ x in unitChainSet (tetEquiv (firstElevenTet i))
      (realCellCorner (firstElevenTet i)),
        ∑ k : SpatialIndex,
          fderiv ℝ (fun y => eval y (realSpatialVector (firstElevenTet i) j k)) x
            (Pi.single k 1)) =
      (FreudenthalSVLean.QuarticMacro.quarticMeanMatrix i j : ℝ) / 30 := by
  rw [actualDivergence_volume_mean, divergenceMean_eq_matrix_div_thirty]
  push_cast
  rfl

/-- The twelve genuine means have zero sum, as verified from their exact
formula.  This theorem does not itself assert conformity of the fields. -/
theorem actualDivergence_means_sum_zero (w : FieldIndex) :
    (∑ t : TetIndex,
      ∫ x in unitChainSet (tetEquiv t) (realCellCorner t),
        eval x (realSpatialDivergence t w)) = 0 := by
  simp_rw [spatialDivergence_volume_mean]
  have hq : (∑ t : TetIndex, divergenceMean t w) = 0 := by
    simp [divergenceMean, div_eq_mul_inv, ← Finset.sum_mul,
      scaledDivergenceMean_sum_zero]
  exact_mod_cast hq

end FreudenthalSVLean.QuarticVolume
