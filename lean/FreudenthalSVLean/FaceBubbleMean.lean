import FreudenthalSVLean.BernsteinMean
import FreudenthalSVLean.SkeletonBubble

/-!
# Actual divergence means of cubic face bubbles

For manuscript equation `vertex-face-transfer`, this module derives the
one-tetrahedron face-bubble divergence mean directly from the proved
Lebesgue Bernstein integral.  A face is encoded by its omitted vertex and
the scalar product of its other three barycentric coordinates.  This is
the normalization calculation used by mean transfers; two-tetrahedron
conformity, shared-face geometry, and support are separate obligations.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BernsteinMean
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.FaceBubbleMean

/-- Integrals of unnormalized barycentric monomials, deduced from the
actual Bernstein volume integral. -/
theorem monomial_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (α : Fin 4 →₀ ℕ) (c : ℝ) :
    unitPolynomialIntegral σ o (monomial α c) =
      c * factorialProduct α / (Nat.factorial (α.degree + 3) : ℝ) := by
  have he : monomial α c = (c / normalization α.degree α) •
      bernstein (R := ℝ) α.degree α := by
    simp only [bernstein, smul_monomial, smul_eq_mul]
    congr 1
    field_simp [normalization_ne_zero (R := ℝ)]
  rw [he, map_smul, unitPolynomialIntegral_bernstein]
  simp only [smul_eq_mul, normalization]
  have hα : (Nat.factorial α.degree : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero α.degree
  field_simp [hα, factorialProduct_ne_zero (R := ℝ) α]

def faceExponent (r : Fin 4) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if i = r then 0 else 1)

theorem faceExponent_apply (r i : Fin 4) :
    faceExponent r i = if i = r then 0 else 1 := by
  simp [faceExponent]

def faceBarycentricPolynomial (r : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  monomial (faceExponent r) 1

theorem faceExponent_degree (r : Fin 4) : (faceExponent r).degree = 3 := by
  have he : (∑ i : Fin 4, faceExponent r i) +
      (∑ i : Fin 4, if i = r then (1 : ℕ) else 0) = ∑ _i : Fin 4, (1 : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hir : i = r <;> simp [faceExponent_apply, hir]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he
  rw [Finsupp.degree_eq_sum]
  omega

theorem faceExponent_sub_degree (r i : Fin 4) (hir : i ≠ r) :
    (faceExponent r - Finsupp.single i 1).degree = 2 := by
  have hle : Finsupp.single i 1 ≤ faceExponent r :=
    Finsupp.single_le_iff.mpr (by simp [faceExponent_apply, hir])
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, faceExponent_degree] at h
  omega

theorem faceExponent_sub_factorialProduct (r i : Fin 4) :
    factorialProduct (R := ℝ) (faceExponent r - Finsupp.single i 1) = 1 := by
  apply Finset.prod_eq_one
  intro l _
  change (Nat.factorial ((faceExponent r - Finsupp.single i 1 : Fin 4 →₀ ℕ) l) : ℝ) = 1
  have hl : (faceExponent r - Finsupp.single i 1 : Fin 4 →₀ ℕ) l ≤ 1 := by
    simp only [Finsupp.tsub_apply, faceExponent_apply, Finsupp.single_apply]
    split_ifs <;> omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with h | h <;> simp [h]

theorem face_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space) (r i : Fin 4) :
    unitPolynomialIntegral σ o (pderiv i (faceBarycentricPolynomial r)) =
      if i = r then 0 else 1 / 120 := by
  by_cases hir : i = r
  · subst i
    simp [faceBarycentricPolynomial, pderiv_monomial, faceExponent_apply]
  · rw [faceBarycentricPolynomial, pderiv_monomial, monomial_mean,
      faceExponent_sub_degree r i hir, faceExponent_sub_factorialProduct]
    norm_num [faceExponent_apply, hir]

def spatialFaceBubble (σ : Equiv.Perm (Fin 3)) (o : Space) (r : Fin 4) :
    MvPolynomial (Fin 3) ℝ :=
  eval₂Hom C (ChainGeometry.barycentric σ o) (faceBarycentricPolynomial r)

/-- Every face has two distinct vertices other than any designated
tetrahedron vertex.  This finite combinatorial fact concerns the four
vertices of one arbitrary tetrahedron, not a sample-mesh coverage claim. -/
theorem face_missing_pair (r l : Fin 4) :
    ∃ a b : Fin 4, a ≠ b ∧ a ≠ r ∧ b ≠ r ∧ a ≠ l ∧ b ≠ l := by
  decide +kernel +revert

theorem faceBarycentricPolynomial_derivative_vertex (r l i : Fin 4) :
    eval (fun a : Fin 4 => if a = l then (1 : ℝ) else 0)
      (pderiv i (faceBarycentricPolynomial r)) = 0 := by
  obtain ⟨a, b, hab, har, hbr, hal, hbl⟩ := face_missing_pair r l
  apply SkeletonBubble.eval_pderiv_zero_of_two_missing (faceExponent r) 1 _ a b i hab
  · simp [faceExponent_apply, har]
  · simp [faceExponent_apply, hbr]
  · simp [hal]
  · simp [hbl]

/-- The actual spatial derivative is the barycentric chain-rule sum. -/
theorem spatialFaceBubble_derivative (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (j : Fin 3) :
    pderiv j (spatialFaceBubble σ o r) =
      eval₂Hom C (ChainGeometry.barycentric σ o)
        (∑ i : Fin 4, C (ChainGeometry.barycentricGradient σ i j) *
          pderiv i (faceBarycentricPolynomial r)) := by
  rw [spatialFaceBubble, PolynomialCalculus.pderiv_substitution]
  simp only [map_sum, map_mul, eval₂Hom_C, ChainGeometry.pderiv_barycentric]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Face transfers preserve every vertex-divergence row. -/
theorem spatialFaceBubble_derivative_vertex (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r l : Fin 4) (j : Fin 3) :
    eval (ChainGeometry.chainVertex σ o l) (pderiv j (spatialFaceBubble σ o r)) = 0 := by
  rw [spatialFaceBubble_derivative, PolynomialCalculus.eval_substitution]
  simp only [ChainGeometry.barycentric_vertex, map_sum, map_mul, eval_C,
    faceBarycentricPolynomial_derivative_vertex, mul_zero, Finset.sum_const_zero]

/-- Exact mean: the outward-gradient contribution has factor `-1/120`.
The negative sign follows from partition of unity, not a chosen normal
sign convention imported from a mesh-specific lemma. -/
theorem spatialFaceBubble_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (j : Fin 3) :
    (∫ x in unitChainSet σ o, eval x (pderiv j (spatialFaceBubble σ o r))) =
      -ChainGeometry.barycentricGradient σ r j / 120 := by
  rw [spatialFaceBubble_derivative]
  simp only [PolynomialCalculus.eval_substitution]
  change unitPolynomialIntegral σ o
    (∑ i : Fin 4, C (ChainGeometry.barycentricGradient σ i j) *
      pderiv i (faceBarycentricPolynomial r)) = _
  simp only [map_sum, unitPolynomialIntegral_C_mul, face_derivative_mean]
  have he : (∑ i : Fin 4, ChainGeometry.barycentricGradient σ i j *
      (if i = r then 0 else (1 / 120 : ℝ))) =
        (∑ i : Fin 4, ChainGeometry.barycentricGradient σ i j) / 120 -
          ChainGeometry.barycentricGradient σ r j / 120 := by
    have hd : (∑ i : Fin 4, if i = r then
        (ChainGeometry.barycentricGradient σ i j : ℝ) / 120 else 0) =
          ChainGeometry.barycentricGradient σ r j / 120 := by simp
    rw [Finset.sum_div, ← hd, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hir : i = r <;> simp [hir, div_eq_mul_inv]
  rw [he, ChainGeometry.barycentricGradient_sum]
  ring

def unitSpatialIntegral (σ : Equiv.Perm (Fin 3)) (o : Space) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in unitChainSet σ o, eval x p
  map_add' p q := by
    simp only [map_add]
    apply integral_add
    · exact (MvPolynomial.continuous_eval p).continuousOn.integrableOn_compact
        (μ := volume) (unitChainSet_isCompact σ o)
    · exact (MvPolynomial.continuous_eval q).continuousOn.integrableOn_compact
        (μ := volume) (unitChainSet_isCompact σ o)
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

theorem unitSpatialIntegral_C_mul (σ : Equiv.Perm (Fin 3)) (o : Space)
    (c : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    unitSpatialIntegral σ o (C c * p) = c * unitSpatialIntegral σ o p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem spatialFaceBubble_vector_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (v : Space) :
    (∫ x in unitChainSet σ o, eval x
      (PolynomialCalculus.polynomialDivergence
        (fun j => C (v j) * spatialFaceBubble σ o r))) =
      -(∑ j : Fin 3, v j * ChainGeometry.barycentricGradient σ r j) / 120 := by
  change unitSpatialIntegral σ o
    (∑ j : Fin 3, pderiv j (C (v j) * spatialFaceBubble σ o r)) = _
  simp only [map_sum, pderiv_C_mul, unitSpatialIntegral_C_mul]
  have hm (j : Fin 3) : unitSpatialIntegral σ o
      (pderiv j (spatialFaceBubble σ o r)) =
        -ChainGeometry.barycentricGradient σ r j / 120 :=
    spatialFaceBubble_derivative_mean σ o r j
  simp only [hm]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem face_gradient_norm_square (σ : Equiv.Perm (Fin 3)) (r : Fin 4) :
    (∑ j : Fin 3, (ChainGeometry.barycentricGradient σ r j : ℝ) ^ 2) =
      if r = 0 ∨ r = 3 then 1 else 2 := by
  rw [← Equiv.sum_comp σ, Fin.sum_univ_three]
  fin_cases r <;>
    norm_num [ChainGeometry.barycentricGradient, ChainGeometry.coordinateUnit,
      σ.injective.eq_iff] <;> norm_num [Fin.ext_iff]

theorem face_gradient_norm_square_pos (σ : Equiv.Perm (Fin 3)) (r : Fin 4) :
    0 < ∑ j : Fin 3, (ChainGeometry.barycentricGradient σ r j : ℝ) ^ 2 := by
  rw [face_gradient_norm_square]
  split_ifs <;> norm_num

/-- An explicit vector yielding unit mean on the designated tetrahedron. -/
def unitTransferVector (σ : Equiv.Perm (Fin 3)) (r : Fin 4) : Space :=
  fun j => -120 * ChainGeometry.barycentricGradient σ r j /
    (∑ l : Fin 3, (ChainGeometry.barycentricGradient σ r l : ℝ) ^ 2)

theorem unitTransferVector_mean_one (σ : Equiv.Perm (Fin 3)) (o : Space) (r : Fin 4) :
    (∫ x in unitChainSet σ o, eval x
      (PolynomialCalculus.polynomialDivergence
        (fun j => C (unitTransferVector σ r j) * spatialFaceBubble σ o r))) = 1 := by
  rw [spatialFaceBubble_vector_mean]
  simp only [unitTransferVector, div_mul_eq_mul_div, mul_assoc,
    ← pow_two, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp [(face_gradient_norm_square_pos σ r).ne']

end FreudenthalSVLean.FaceBubbleMean
