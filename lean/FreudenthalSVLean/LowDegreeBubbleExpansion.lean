import FreudenthalSVLean.LowDegreeBubbleIndices
import FreudenthalSVLean.HomogeneousSkeletonCompleteness
import FreudenthalSVLean.ElementBubbleAlgebra
import Mathlib.Data.Fintype.BigOperators

/-!
# Complete low-degree expansions of edge-zero residuals

This module formalizes the Bernstein target-space description in manuscript
Lemma `bubble`.  The structural support classification gives complete
expansions with four cubic face coefficients or twelve quartic face
coefficients and one interior coefficient.  The coefficients are those of
the actual homogeneous representation of a spatial polynomial, not a
separately asserted matrix input.  The real tetrahedron integral then
determines the compatibility needed by the explicit element-bubble inverse.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.LowDegreeBubbleIndices

noncomputable section

namespace FreudenthalSVLean.LowDegreeBubbleExpansion

set_option backward.isDefEq.respectTransparency false

theorem faceExponent_injective : Function.Injective faceExponent := by
  intro i j he
  by_contra hne
  have hv := congrArg (fun α : Vertex →₀ ℕ => α i) he
  simp [faceExponent_apply, hne] at hv

abbrev FacePair := {p : Vertex × Vertex // p.1 ≠ p.2}

def quarticFaceExponent (p : FacePair) : Vertex →₀ ℕ :=
  faceExponent p.val.1 + Finsupp.single p.val.2 1

theorem quarticFaceExponent_apply (p : FacePair) (j : Vertex) :
    quarticFaceExponent p j =
      if j = p.val.1 then 0 else if j = p.val.2 then 2 else 1 := by
  simp only [quarticFaceExponent, Finsupp.add_apply, faceExponent_apply,
    Finsupp.single_apply]
  by_cases hfirst : j = p.val.1
  · subst j
    simp only [Ne.symm p.property, if_true, if_false, zero_add]
  · by_cases hsecond : j = p.val.2
    · subst j
      simp only [Ne.symm p.property, if_false, if_true]
    · simp only [hfirst, hsecond, Ne.symm hsecond, if_false, add_zero]

theorem quarticFaceExponent_injective : Function.Injective quarticFaceExponent := by
  intro p q he
  have hfirst : p.val.1 = q.val.1 := by
    have hv := congrArg (fun α : Vertex →₀ ℕ => α p.val.1) he
    simp only [quarticFaceExponent_apply, if_true] at hv
    by_contra hn
    rw [if_neg hn] at hv
    split_ifs at hv
  have hsecond : p.val.2 = q.val.2 := by
    have hv := congrArg (fun α : Vertex →₀ ℕ => α p.val.2) he
    have hpf : p.val.2 ≠ p.val.1 := Ne.symm p.property
    have hqf : p.val.2 ≠ q.val.1 := by rw [← hfirst]; exact hpf
    simp only [quarticFaceExponent_apply, hpf, hqf, if_false, if_true] at hv
    by_contra hn
    rw [if_neg hn] at hv
    omega
  exact Subtype.ext (Prod.ext hfirst hsecond)

abbrev QuarticIndex := Unit ⊕ FacePair

def quarticExponent : QuarticIndex → Vertex →₀ ℕ
  | .inl _ => bubbleExponent
  | .inr p => quarticFaceExponent p

theorem quarticExponent_injective : Function.Injective quarticExponent := by
  intro p q he
  cases p with
  | inl u =>
    cases q with
    | inl v => congr
    | inr q =>
      have hv := congrArg (fun α : Vertex →₀ ℕ => α q.val.1) he
      simp [quarticExponent, bubbleExponent_apply, quarticFaceExponent_apply] at hv
  | inr p =>
    cases q with
    | inl v =>
      have hv := congrArg (fun α : Vertex →₀ ℕ => α p.val.1) he
      simp [quarticExponent, bubbleExponent_apply, quarticFaceExponent_apply] at hv
    | inr q => exact congrArg Sum.inr (quarticFaceExponent_injective he)

/-- A finite family of distinct monomial indices gives a complete expansion
whenever it contains every nonzero coefficient of the polynomial. -/
theorem expansion_of_coefficient_coverage {σ I R : Type*} [Fintype I] [CommSemiring R]
    (e : I → σ →₀ ℕ) (hi : Function.Injective e) (p : MvPolynomial σ R)
    (hc : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → ∃ i : I, e i = α) :
    p = ∑ i : I, monomial (e i) (coeff (e i) p) := by
  classical
  ext α
  by_cases hex : ∃ i : I, e i = α
  · obtain ⟨i, rfl⟩ := hex
    simp only [coeff_sum, coeff_monomial, hi.eq_iff]
    simp
  · have hz : coeff α p = 0 := by
      by_contra hne
      exact hex (hc α hne)
    have hne (i : I) : e i ≠ α := fun he => hex ⟨i, he⟩
    simp [coeff_sum, coeff_monomial, hne, hz]

theorem cubic_expansion (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 3)
    (he : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α p = 0) :
    p = ∑ i : Vertex, monomial (faceExponent i) (coeff (faceExponent i) p) := by
  apply expansion_of_coefficient_coverage faceExponent faceExponent_injective p
  intro α hne
  have hd : α.degree = 3 := by
    simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hp hne
  have hs : 3 ≤ α.support.card := by
    by_contra hlt
    exact hne (he α (by omega))
  obtain ⟨i, hi⟩ := cubic_classification α hd hs
  exact ⟨i, hi.symm⟩

theorem quartic_expansion (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 4)
    (he : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α p = 0) :
    p = monomial bubbleExponent (coeff bubbleExponent p) +
      ∑ i : FacePair, monomial (quarticFaceExponent i) (coeff (quarticFaceExponent i) p) := by
  have hh : p = ∑ i : QuarticIndex, monomial (quarticExponent i)
      (coeff (quarticExponent i) p) := by
    apply expansion_of_coefficient_coverage quarticExponent quarticExponent_injective p
    intro α hne
    have hd : α.degree = 4 := by
      simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hp hne
    have hs : 3 ≤ α.support.card := by
      by_contra hlt
      exact hne (he α (by omega))
    rcases quartic_classification α hd hs with hi | ⟨i, a, hia, hi⟩
    · exact ⟨Sum.inl (), hi.symm⟩
    · exact ⟨Sum.inr ⟨(i, a), hia⟩, hi.symm⟩
  simpa [Fintype.sum_sum_type, quarticExponent] using hh

theorem facePair_sum {S : Type*} [AddCommMonoid S] (f : Vertex → Vertex → S) :
    (∑ p : FacePair, f p.val.1 p.val.2) =
      ∑ a : Vertex, ∑ i : Vertex, if i = a then 0 else f i a := by
  have hs : (∑ p : FacePair, f p.val.1 p.val.2) =
      ∑ p ∈ (Finset.univ : Finset (Vertex × Vertex)) with p.1 ≠ p.2, f p.1 p.2 := by
    exact (Finset.sum_subtype
      (p := fun p : Vertex × Vertex => p.1 ≠ p.2)
      ((Finset.univ : Finset (Vertex × Vertex)).filter (fun p => p.1 ≠ p.2))
      (by simp) (fun p : Vertex × Vertex => f p.1 p.2)).symm
  rw [hs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [ite_not]

theorem faceExponent_support (i : Vertex) :
    (faceExponent i).support = Finset.univ.erase i := by
  ext j
  simp only [Finsupp.mem_support_iff, faceExponent_apply, Finset.mem_erase,
    Finset.mem_univ, and_true]
  split_ifs <;> simp_all

theorem bubbleExponent_support : bubbleExponent.support = Finset.univ := by
  ext j
  simp [Finsupp.mem_support_iff, bubbleExponent_apply]

theorem substitute_face_monomial (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (i : Vertex) (c : ℝ) :
    eval₂Hom C (barycentric σ o) (monomial (faceExponent i) c) =
      C c * ElementBubbleAlgebra.faceCubic σ o i := by
  rw [eval₂Hom_monomial]
  simp only [Finsupp.prod, faceExponent_support, ElementBubbleAlgebra.faceCubic]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [faceExponent_apply, if_neg (Finset.mem_erase.mp hj).1, pow_one]

theorem substitute_bubble_monomial (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (c : ℝ) :
    eval₂Hom C (barycentric σ o) (monomial bubbleExponent c) =
      C c * ElementBubbleAlgebra.bubble σ o := by
  rw [eval₂Hom_monomial]
  simp only [Finsupp.prod, bubbleExponent_support, bubbleExponent_apply, pow_one,
    ElementBubbleAlgebra.bubble]

theorem substitute_quartic_face_monomial (σ : Equiv.Perm Coordinate)
    (o : Coordinate → ℝ) (i a : Vertex) (c : ℝ) :
    eval₂Hom C (barycentric σ o) (monomial (faceExponent i + Finsupp.single a 1) c) =
      C c * ElementBubbleAlgebra.faceCubic σ o i * barycentric σ o a := by
  rw [monomial_add_single, pow_one, map_mul, substitute_face_monomial, eval₂Hom_X']

theorem face_factorialProduct (i : Vertex) :
    BernsteinPolynomial.factorialProduct (R := ℝ) (faceExponent i) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  simp only [faceExponent_apply]
  split_ifs <;> norm_num

theorem bubble_factorialProduct :
    BernsteinPolynomial.factorialProduct (R := ℝ) bubbleExponent = 1 := by
  apply Finset.prod_eq_one
  intro j _
  simp [bubbleExponent_apply]

theorem quarticFaceExponent_degree (p : FacePair) :
    (quarticFaceExponent p).degree = 4 := by
  simp only [quarticFaceExponent, map_add, faceExponent_degree, Finsupp.degree_single]

theorem quarticFace_factorialProduct (p : FacePair) :
    BernsteinPolynomial.factorialProduct (R := ℝ) (quarticFaceExponent p) = 2 := by
  rw [quarticFaceExponent, BernsteinPolynomial.factorialProduct_raised,
    face_factorialProduct]
  norm_num [faceExponent_apply, Ne.symm p.property]

theorem face_monomial_mean (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (i : Vertex) (c : ℝ) :
    BernsteinMean.unitPolynomialIntegral σ o (monomial (faceExponent i) c) = c / 720 := by
  rw [monomial_mean, faceExponent_degree, face_factorialProduct]
  norm_num

theorem bubble_monomial_mean (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (c : ℝ) :
    BernsteinMean.unitPolynomialIntegral σ o (monomial bubbleExponent c) = c / 5040 := by
  rw [monomial_mean, bubbleExponent_degree, bubble_factorialProduct]
  norm_num

theorem quarticFace_monomial_mean (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : FacePair) (c : ℝ) :
    BernsteinMean.unitPolynomialIntegral σ o (monomial (quarticFaceExponent p) c) =
      2 * c / 5040 := by
  rw [monomial_mean, quarticFaceExponent_degree, quarticFace_factorialProduct]
  norm_num
  ring

theorem substitution_integral (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Vertex ℝ) :
    unitSpatialIntegral σ o (eval₂Hom C (barycentric σ o) p) =
      BernsteinMean.unitPolynomialIntegral σ o p := by
  change (∫ x in ChainMeasureTransport.unitChainSet σ o,
    eval x (eval₂Hom C (barycentric σ o) p)) =
      ∫ x in ChainMeasureTransport.unitChainSet σ o,
        eval (BernsteinMean.spatialBarycentric σ o x) p
  simp only [PolynomialCalculus.eval_substitution]
  rfl

theorem cubic_mean (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 3)
    (he : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α p = 0) :
    BernsteinMean.unitPolynomialIntegral σ o p =
      (∑ i : Vertex, coeff (faceExponent i) p) / 720 := by
  conv_lhs => rw [cubic_expansion p hp he]
  simp only [map_sum, face_monomial_mean, Finset.sum_div]

theorem quartic_mean (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Vertex ℝ) (hp : IsHomogeneous p 4)
    (he : ∀ α : Vertex →₀ ℕ, α.support.card ≤ 2 → coeff α p = 0) :
    BernsteinMean.unitPolynomialIntegral σ o p =
      (coeff bubbleExponent p + 2 * ∑ i : FacePair, coeff (quarticFaceExponent i) p) / 5040 := by
  conv_lhs => rw [quartic_expansion p hp he]
  simp only [map_add, map_sum, bubble_monomial_mean, quarticFace_monomial_mean,
    ← Finset.sum_div, ← Finset.mul_sum]
  ring

end FreudenthalSVLean.LowDegreeBubbleExpansion
