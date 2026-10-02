import FreudenthalSVLean.AffineBarycentric
import FreudenthalSVLean.ElementBubbleLift

/-!
# Analytic injectivity of constant and affine element-bubble divergence

The injectivity step of manuscript Lemma `bubble` is proved here directly
in barycentric coordinates.  On each face, three strictly positive
barycentric test points recover the three normal coefficients of an affine
vector polynomial.  Partition of unity and vertex/gradient duality then
force all four vector coefficients to vanish.  The source polynomial is
recovered from its actual vertex values by the proved affine interpolation
identity.  This is a structural argument on an arbitrary translated chain,
not a matrix-rank oracle or an assumed Piola formula.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ElementBubbleAlgebra
open FreudenthalSVLean.AffineBarycentric

noncomputable section

namespace FreudenthalSVLean.ElementBubbleInjectivity

set_option backward.isDefEq.respectTransparency false

def bubbleAffineField (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (v : Vertex → Coordinate → ℝ) : Coordinate → MvPolynomial Coordinate ℝ :=
  fun j => ∑ a : Vertex, C (v a j) * bubble σ o * barycentric σ o a

def normalCoefficient (σ : Equiv.Perm Coordinate) (v : Vertex → Coordinate → ℝ)
    (i a : Vertex) : ℝ := ∑ j : Coordinate, v a j * barycentricGradient σ i j

theorem bubbleAffineField_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (v : Vertex → Coordinate → ℝ) :
    divergence (bubbleAffineField σ o v) =
      ∑ a : Vertex, ((∑ i : Vertex, C (normalCoefficient σ v i a) *
        faceCubic σ o i * barycentric σ o a) +
        C (normalCoefficient σ v a a) * bubble σ o) := by
  simp only [divergence, bubbleAffineField, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact bubble_constant_barycentric_divergence σ o (v a) a

theorem faceCubic_eval_zero (σ : Equiv.Perm Coordinate) (o x : Coordinate → ℝ)
    (i r : Vertex) (hir : i ≠ r) (hi : eval x (barycentric σ o i) = 0) :
    eval x (faceCubic σ o r) = 0 := by
  rw [faceCubic, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hir, Finset.mem_univ i⟩) hi

/-- On a face only its omitted barycentric derivative contributes. -/
theorem bubbleAffineField_divergence_face (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → ℝ) (v : Vertex → Coordinate → ℝ) (i : Vertex)
    (hi : eval x (barycentric σ o i) = 0) :
    eval x (divergence (bubbleAffineField σ o v)) =
      eval x (faceCubic σ o i) *
        ∑ a : Vertex, eval x (barycentric σ o a) * normalCoefficient σ v i a := by
  rw [bubbleAffineField_divergence, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_add, map_sum, map_mul, eval_C,
    ElementBubbleLift.bubble_eval_zero σ o x i hi, mul_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · ring
  · intro r _ hri
    rw [faceCubic_eval_zero σ o x i r (Ne.symm hri) hi, mul_zero, zero_mul]
  · simp

def faceWeight (i r a : Vertex) : ℝ :=
  if a = i then 0 else if a = r then 1 / 2 else 1 / 4

theorem faceWeight_decomposition (i r a : Vertex) (hri : r ≠ i) :
    faceWeight i r a =
      ((1 - (if a = i then 1 else 0)) + (if a = r then 1 else 0)) / 4 := by
  by_cases hai : a = i
  · subst a
    simp [faceWeight, Ne.symm hri]
  · by_cases har : a = r
    · subst a
      norm_num [faceWeight, hri]
    · norm_num [faceWeight, hai, har]

theorem faceWeight_sum (i r : Vertex) (hri : r ≠ i) :
    (∑ a : Vertex, faceWeight i r a) = 1 := by
  simp_rw [faceWeight_decomposition i r _ hri]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  norm_num

theorem faceWeight_pos (i r a : Vertex) (hai : a ≠ i) : 0 < faceWeight i r a := by
  simp only [faceWeight, hai, if_false]
  split_ifs <;> norm_num

theorem faceWeight_dot (i r : Vertex) (hri : r ≠ i) (d : Vertex → ℝ) :
    (∑ a : Vertex, faceWeight i r a * d a) =
      ((∑ a : Vertex, if a = i then 0 else d a) + d r) / 4 := by
  have ht (a : Vertex) : faceWeight i r a * d a =
      ((if a = i then 0 else d a) + (if a = r then d r else 0)) / 4 := by
    by_cases hai : a = i
    · subst a
      simp [faceWeight, Ne.symm hri]
    · by_cases har : a = r
      · subst a
        simp only [faceWeight, hri, if_false, if_true]
        ring
      · simp only [faceWeight, hai, har, if_false, add_zero]
        ring
  simp only [ht, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The three face equations determine all three normal coefficients. -/
theorem face_rows_zero (i : Vertex) (d : Vertex → ℝ)
    (hd : ∀ r : Vertex, r ≠ i → (∑ a : Vertex, faceWeight i r a * d a) = 0) :
    ∀ r : Vertex, r ≠ i → d r = 0 := by
  let S : ℝ := ∑ a : Vertex, if a = i then 0 else d a
  have hr (r : Vertex) (hri : r ≠ i) : d r = -S := by
    have hh := hd r hri
    rw [faceWeight_dot i r hri] at hh
    change (S + d r) / 4 = 0 at hh
    linarith
  have he : S = -3 * S := by
    calc
      S = ∑ a : Vertex, if a = i then 0 else -S := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hai : a = i
        · simp [hai]
        · simp only [hai, if_false, hr a hai]
      _ = -3 * S := by
        have ht (a : Vertex) : (if a = i then 0 else -S) =
            -S - (if a = i then -S else 0) := by
          split_ifs <;> ring
        simp only [ht, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
  have hS : S = 0 := by linarith
  intro r hri
  rw [hr r hri, hS, neg_zero]

theorem normalCoefficient_sum (σ : Equiv.Perm Coordinate)
    (v : Vertex → Coordinate → ℝ) (a : Vertex) :
    (∑ i : Vertex, normalCoefficient σ v i a) = 0 := by
  simp only [normalCoefficient]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, barycentricGradient_sum, mul_zero, Finset.sum_const_zero]

theorem normal_reconstruction (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (v : Vertex → Coordinate → ℝ) (a : Vertex) (j : Coordinate) :
    (∑ i : Vertex, normalCoefficient σ v i a * chainVertex σ o i j) = v a j := by
  simp only [normalCoefficient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have ht (l : Coordinate) :
      (∑ i : Vertex, barycentricGradient σ i l * chainVertex σ o i j) =
        if j = l then 1 else 0 := by
    simpa only [mul_comm] using VertexJetAlgebra.vertex_gradient_duality σ o j l
  simp only [← Finset.mul_sum, ht]
  simp

/-- Every affine vector coefficient is forced to zero by zero bubble
divergence, uniformly in the tetrahedron's geometry. -/
theorem bubbleAffineField_eq_zero (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (v : Vertex → Coordinate → ℝ) (hd : divergence (bubbleAffineField σ o v) = 0) :
    v = 0 := by
  have hoff (i a : Vertex) (hai : a ≠ i) : normalCoefficient σ v i a = 0 := by
    apply face_rows_zero i (normalCoefficient σ v i) _ a hai
    intro r hri
    let x := affinePoint σ o (faceWeight i r)
    have hb (l : Vertex) : eval x (barycentric σ o l) = faceWeight i r l :=
      affinePoint_barycentric σ o _ (faceWeight_sum i r hri) l
    have hi : eval x (barycentric σ o i) = 0 := by rw [hb]; simp [faceWeight]
    have hf : eval x (faceCubic σ o i) ≠ 0 := by
      rw [faceCubic, map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro l hl
      rw [hb]
      exact (faceWeight_pos i r l (Finset.mem_erase.mp hl).1).ne'
    have hh := congrArg (eval x) hd
    rw [bubbleAffineField_divergence_face σ o x v i hi, map_zero] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left hf
    simpa only [hb] using hz
  have hrow (i a : Vertex) : normalCoefficient σ v i a = 0 := by
    by_cases hai : a = i
    · subst i
      have hs := normalCoefficient_sum σ v a
      have hh : (∑ i : Vertex, normalCoefficient σ v i a) = normalCoefficient σ v a a := by
        apply Finset.sum_eq_single a
        · intro i _ hia
          exact hoff i a (Ne.symm hia)
        · simp
      rw [hh] at hs
      exact hs
    · exact hoff i a hai
  funext a j
  have hh := normal_reconstruction σ o v a j
  simp only [hrow, zero_mul, Finset.sum_const_zero] at hh
  exact hh.symm

/-- Injectivity for every affine source vector, proved using actual
polynomial degree and differentiation.  Constant source vectors are
included as the degree-zero subspace. -/
theorem affine_bubble_divergence_kernel (σ : Equiv.Perm Coordinate)
    (o : Coordinate → ℝ) (p : Coordinate → MvPolynomial Coordinate ℝ)
    (hp : ∀ j : Coordinate, (p j).totalDegree ≤ 1)
    (hd : PolynomialCalculus.polynomialDivergence (fun j => bubble σ o * p j) = 0) :
    p = 0 := by
  let v : Vertex → Coordinate → ℝ := fun a j => eval (chainVertex σ o a) (p j)
  have hinterp (j : Coordinate) : p j = ∑ a : Vertex, C (v a j) * barycentric σ o a :=
    affine_interpolation σ o (p j) (hp j)
  have hfield : (fun j => bubble σ o * p j) = bubbleAffineField σ o v := by
    funext j
    rw [hinterp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfield] at hd
  have hv : v = 0 := bubbleAffineField_eq_zero σ o v hd
  funext j
  rw [hinterp, hv]
  simp

end FreudenthalSVLean.ElementBubbleInjectivity
