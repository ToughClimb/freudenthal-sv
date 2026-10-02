import FreudenthalSVLean.LowDegreeBubbleExpansion
import FreudenthalSVLean.GridNodalSupport
import FreudenthalSVLean.PolynomialL2Space

/-!
# Actual degree-four and degree-five element-bubble right inverses

For manuscript Lemma `bubble`, this module constructs fixed linear
operators on actual spatial pressure polynomials.  The homogeneous
representation, completeness of geometric edge conditions, structural
low-degree expansion, and genuine tetrahedron integral supply every
compatibility condition needed by the explicit inverse formulas.
The resulting fields have the stated polynomial degrees and contain the
quartic tetrahedron bubble as a factor.

These are local right inverses.  This module does not assert the global
vertex/edge correction theorem or the initial stable mean lift.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.LowDegreeBubbleIndices
open FreudenthalSVLean.LowDegreeBubbleExpansion
open FreudenthalSVLean.ElementBubbleAlgebra

noncomputable section

namespace FreudenthalSVLean.ElementBubbleLift

set_option backward.isDefEq.respectTransparency false

def cubicCoefficients (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] (Vertex → ℝ) :=
  LinearMap.pi (fun i => (lcoeff ℝ (faceExponent i)).comp
    (HomogeneousBarycentric.representationLinear σ o 3))

def quarticCoefficients (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] (Vertex → Vertex → ℝ) :=
  LinearMap.pi (fun i => LinearMap.pi (fun a =>
    (lcoeff ℝ (faceExponent i + Finsupp.single a 1)).comp
      (HomogeneousBarycentric.representationLinear σ o 4)))

def cubicLift (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] (Coordinate → MvPolynomial Coordinate ℝ) :=
  (constantLiftLinear σ o).comp (cubicCoefficients σ o)

def quarticLift (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] (Coordinate → MvPolynomial Coordinate ℝ) :=
  (affineLiftLinear σ o).comp (quarticCoefficients σ o)

theorem cubicCoefficients_apply (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (i : Vertex) :
    cubicCoefficients σ o p i = coeff (faceExponent i)
      (HomogeneousBarycentric.representation σ o 3 p) := rfl

theorem cubicLift_eq (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) : cubicLift σ o p =
      fun j => C (constantLiftVector σ o (cubicCoefficients σ o p) j) * bubble σ o := rfl

def zeroEdgeTrace (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) : Prop :=
  ∀ a b : Vertex, a ≠ b → ∀ t ∈ Icc (0 : ℝ) 1,
    eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) t) p = 0

/-- The degree-four bubble lift solves every degree-at-most-three residual
with actual zero edge traces and actual zero element integral. -/
theorem cubicLift_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (hp : p.totalDegree ≤ 3)
    (he : zeroEdgeTrace σ o p) (hm : unitSpatialIntegral σ o p = 0) :
    PolynomialCalculus.polynomialDivergence (cubicLift σ o p) = p := by
  let H := HomogeneousBarycentric.representation σ o 3 p
  have hH : IsHomogeneous H 3 := HomogeneousBarycentric.representation_homogeneous σ o 3 p
  have hcoeff : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α H = 0 :=
    fun α hα => HomogeneousSkeletonCompleteness.representation_coefficients_zero σ o 3 p hp he α hα
  have hsub : eval₂Hom C (barycentric σ o) H = p :=
    HomogeneousBarycentric.substitute_representation σ o 3 p hp
  have hmean : BernsteinMean.unitPolynomialIntegral σ o H = 0 := by
    rw [← substitution_integral, hsub]
    exact hm
  have hsum : (∑ i : Vertex, coeff (faceExponent i) H) = 0 := by
    rw [cubic_mean σ o H hH hcoeff] at hmean
    linarith
  have hexp := congrArg (eval₂Hom C (barycentric σ o)) (cubic_expansion H hH hcoeff)
  rw [hsub] at hexp
  simp only [map_sum, substitute_face_monomial] at hexp
  have hsum' : (∑ i : Vertex, cubicCoefficients σ o p i) = 0 := by
    simpa only [cubicCoefficients_apply] using hsum
  rw [cubicLift_eq, ← divergence_eq_polynomialDivergence,
    constantLift_divergence σ o _ hsum']
  simp only [cubicCoefficients_apply]
  exact hexp.symm

/-- The degree-five bubble lift solves every degree-at-most-four residual;
the mean identity determines its interior coefficient rather than assuming
it is an independent compatible datum. -/
theorem quarticLift_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (hp : p.totalDegree ≤ 4)
    (he : zeroEdgeTrace σ o p) (hm : unitSpatialIntegral σ o p = 0) :
    PolynomialCalculus.polynomialDivergence (quarticLift σ o p) = p := by
  let H := HomogeneousBarycentric.representation σ o 4 p
  let q : Vertex → Vertex → ℝ := fun i a => coeff (faceExponent i + Finsupp.single a 1) H
  have hH : IsHomogeneous H 4 := HomogeneousBarycentric.representation_homogeneous σ o 4 p
  have hcoeff : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α H = 0 :=
    fun α hα => HomogeneousSkeletonCompleteness.representation_coefficients_zero σ o 4 p hp he α hα
  have hsub : eval₂Hom C (barycentric σ o) H = p :=
    HomogeneousBarycentric.substitute_representation σ o 4 p hp
  have hsum : (∑ i : FacePair, coeff (quarticFaceExponent i) H) =
      ∑ a : Vertex, affineCoefficientSum q a := by
    exact facePair_sum q
  have hmean : BernsteinMean.unitPolynomialIntegral σ o H = 0 := by
    rw [← substitution_integral, hsub]
    exact hm
  have hmiddle : coeff bubbleExponent H = -2 * ∑ a : Vertex, affineCoefficientSum q a := by
    rw [quartic_mean σ o H hH hcoeff, hsum] at hmean
    linarith
  have hexp := congrArg (eval₂Hom C (barycentric σ o)) (quartic_expansion H hH hcoeff)
  rw [hsub] at hexp
  simp only [map_add, map_sum, substitute_bubble_monomial,
    quarticFaceExponent, substitute_quartic_face_monomial] at hexp
  rw [facePair_sum (fun i a => C (q i a) * faceCubic σ o i * barycentric σ o a)] at hexp
  change divergence (affineLift σ o q) = p
  rw [affineLift_divergence]
  rw [hexp, hmiddle]
  simp only [map_mul, map_neg, map_ofNat]
  ring

theorem bubble_degree (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ) :
    (bubble σ o).totalDegree ≤ 4 := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ a : Vertex, (barycentric σ o a).totalDegree) ≤ ∑ _a : Vertex, 1 :=
      Finset.sum_le_sum (fun a _ => GridNodalSupport.barycentric_degree_le σ o a)
    _ = 4 := by simp

theorem cubicLift_degree (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (j : Coordinate) :
    (cubicLift σ o p j).totalDegree ≤ 4 :=
  (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using bubble_degree σ o)

theorem quarticLift_degree (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (j : Coordinate) :
    (quarticLift σ o p j).totalDegree ≤ 5 := by
  apply totalDegree_finsetSum_le
  intro a _
  apply (totalDegree_mul _ _).trans
  have hb : (C (affineLiftCoefficient σ o (quarticCoefficients σ o p) a j) *
      bubble σ o).totalDegree ≤ 4 :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using bubble_degree σ o)
  exact (Nat.add_le_add hb (GridNodalSupport.barycentric_degree_le σ o a)).trans (by norm_num)

theorem bubble_eval_zero (σ : Equiv.Perm Coordinate) (o x : Coordinate → ℝ)
    (a : Vertex) (ha : eval x (barycentric σ o a) = 0) : eval x (bubble σ o) = 0 := by
  rw [bubble, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) ha

/-- The constructed degree-four velocity is zero on every tetrahedron face. -/
theorem cubicLift_face_zero (σ : Equiv.Perm Coordinate) (o x : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (a : Vertex)
    (ha : eval x (barycentric σ o a) = 0) (j : Coordinate) :
    eval x (cubicLift σ o p j) = 0 := by
  change eval x (C _ * bubble σ o) = 0
  rw [map_mul, bubble_eval_zero σ o x a ha, mul_zero]

/-- The constructed degree-five velocity is zero on every tetrahedron face. -/
theorem quarticLift_face_zero (σ : Equiv.Perm Coordinate) (o x : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (a : Vertex)
    (ha : eval x (barycentric σ o a) = 0) (j : Coordinate) :
    eval x (quarticLift σ o p j) = 0 := by
  change eval x (∑ b : Vertex,
    C (affineLiftCoefficient σ o (quarticCoefficients σ o p) b j) *
      bubble σ o * barycentric σ o b) = 0
  simp only [map_sum, map_mul, bubble_eval_zero σ o x a ha, mul_zero, zero_mul,
    Finset.sum_const_zero]

end FreudenthalSVLean.ElementBubbleLift
