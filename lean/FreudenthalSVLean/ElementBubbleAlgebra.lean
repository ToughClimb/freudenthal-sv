import FreudenthalSVLean.VertexJetAlgebra
import FreudenthalSVLean.SkeletonBubble
import FreudenthalSVLean.PolynomialDegree

/-!
# Analytic low-degree element-bubble inverses

Manuscript Lemma `bubble` closes the degree-four and degree-five residuals
by multiplying constant or affine vector polynomials by the quartic
tetrahedron bubble.  This module supplies explicit algebraic inverse
formulas using the barycentric direction/gradient duality already proved
in `VertexJetAlgebra`.  Statements about all edge-zero residuals require
the separate homogeneous barycentric representation and mean condition;
those representation obligations are not assumed here.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.ElementBubbleAlgebra

variable {R : Type*} [CommRing R]

def divergence (v : Coordinate → MvPolynomial Coordinate R) : MvPolynomial Coordinate R :=
  ∑ j : Coordinate, pderiv j (v j)

theorem direction_dot_gradient (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b i : Vertex) :
    (∑ j : Coordinate, VertexJetAlgebra.direction σ o a b j *
      barycentricGradient σ i j) =
        (if i = b then 1 else 0) - (if i = a then 1 else 0) := by
  simpa only [mul_comm] using VertexJetAlgebra.gradient_dot_edge σ o i a b

def bubble (σ : Equiv.Perm Coordinate) (o : Coordinate → R) : MvPolynomial Coordinate R :=
  ∏ a : Vertex, barycentric σ o a

def faceCubic (σ : Equiv.Perm Coordinate) (o : Coordinate → R) (i : Vertex) :
    MvPolynomial Coordinate R := ∏ a ∈ Finset.univ.erase i, barycentric σ o a

theorem bubble_derivative (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (j : Coordinate) :
    pderiv j (bubble σ o) =
      ∑ i : Vertex, C (barycentricGradient σ i j) * faceCubic σ o i := by
  rw [bubble, SkeletonBubble.pderiv_prod]
  simp only [pderiv_barycentric, faceCubic]

theorem faceCubic_mul_barycentric (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) : faceCubic σ o a * barycentric σ o a = bubble σ o := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ a)

def constantLiftVector (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : Vertex → R) : Coordinate → R :=
  fun j => ∑ a : Vertex, d a * chainVertex σ o a j

/-- Face gradients applied to the explicit constant lift give exactly the
compatible four coefficients. -/
theorem constantLiftVector_gradient (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : Vertex → R) (hd : ∑ a : Vertex, d a = 0) (i : Vertex) :
    (∑ j : Coordinate, constantLiftVector σ o d j * barycentricGradient σ i j) = d i := by
  have hz : constantLiftVector σ o d =
      fun j => ∑ a : Vertex, d a * VertexJetAlgebra.direction σ o 0 a j := by
    funext j
    simp only [constantLiftVector, VertexJetAlgebra.direction, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hd, zero_mul, sub_zero]
  rw [hz]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, direction_dot_gradient,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd, zero_mul, sub_zero]
  simp

/-- Exact divergence of the quartic bubble times a constant vector. -/
theorem bubble_constant_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (v : Coordinate → R) :
    divergence (fun j => C (v j) * bubble σ o) =
      ∑ i : Vertex, C (∑ j : Coordinate, v j * barycentricGradient σ i j) *
        faceCubic σ o i := by
  simp only [divergence, pderiv_C_mul,
    bubble_derivative, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc]

/-- An explicit right inverse on all zero-sum cubic face coefficients;
no finite matrix-rank assumption occurs. -/
theorem constantLift_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : Vertex → R) (hd : ∑ a : Vertex, d a = 0) :
    divergence
      (fun j => C (constantLiftVector σ o d j) * bubble σ o) =
        ∑ i : Vertex, C (d i) * faceCubic σ o i := by
  rw [bubble_constant_divergence]
  simp only [constantLiftVector_gradient σ o d hd]

/-- The affine inverse's vector coefficient attached to barycentric index
`a`.  Only the twelve off-diagonal face coefficients are used. -/
def affineLiftCoefficient (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q : Vertex → Vertex → R) (a : Vertex) : Coordinate → R :=
  fun j => ∑ i : Vertex, if i = a then 0 else
    q i a * VertexJetAlgebra.direction σ o a i j

theorem affineLiftCoefficient_gradient (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q : Vertex → Vertex → R) (a i : Vertex) :
    (∑ j : Coordinate, affineLiftCoefficient σ o q a j * barycentricGradient σ i j) =
      (if i = a then 0 else q i a) -
        (if i = a then ∑ b : Vertex, if b = a then 0 else q b a else 0) := by
  simp only [affineLiftCoefficient, Finset.sum_mul, ite_mul, zero_mul, mul_assoc]
  rw [Finset.sum_comm]
  have ht (b : Vertex) : (∑ j : Coordinate, if b = a then 0 else
      q b a * (VertexJetAlgebra.direction σ o a b j * barycentricGradient σ i j)) =
        if b = a then 0 else q b a *
          ((if i = b then 1 else 0) - (if i = a then 1 else 0)) := by
    by_cases hba : b = a
    · simp [hba]
    · simp only [hba, if_false, ← Finset.mul_sum]
      rw [direction_dot_gradient]
  simp only [ht]
  have hs (b : Vertex) :
      (if b = a then 0 else q b a *
        ((if i = b then 1 else 0) - (if i = a then 1 else 0))) =
      (if b = a then 0 else q b a) * (if i = b then 1 else 0) -
        (if b = a then 0 else q b a) * (if i = a then 1 else 0) := by
    by_cases hba : b = a <;> simp [hba, mul_sub]
  simp only [hs, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero]
  simp [eq_comm]

def affineCoefficientSum (q : Vertex → Vertex → R) (a : Vertex) : R :=
  ∑ i : Vertex, if i = a then 0 else q i a

/-- Product rule for an actual vector-polynomial divergence. -/
theorem divergence_mul (v : Coordinate → MvPolynomial Coordinate R)
    (p : MvPolynomial Coordinate R) :
    divergence (fun j => v j * p) =
      divergence v * p + ∑ j : Coordinate, v j * pderiv j p := by
  simp only [divergence, pderiv_mul, Finset.sum_add_distrib, Finset.sum_mul]

/-- The barycentric expansion of a single affine coefficient of the
element-bubble field. -/
theorem bubble_constant_barycentric_divergence
    (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (v : Coordinate → R) (a : Vertex) :
    divergence (fun j => C (v j) * bubble σ o * barycentric σ o a) =
      (∑ i : Vertex, C (∑ j : Coordinate, v j * barycentricGradient σ i j) *
        faceCubic σ o i * barycentric σ o a) +
      C (∑ j : Coordinate, v j * barycentricGradient σ a j) * bubble σ o := by
  rw [divergence_mul, bubble_constant_divergence, Finset.sum_mul]
  congr 1
  simp only [pderiv_barycentric, map_sum, Finset.sum_mul, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The explicit degree-five field: a quartic bubble multiplied by an
affine vector polynomial with coefficients determined by the face data. -/
def affineLift (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q : Vertex → Vertex → R) : Coordinate → MvPolynomial Coordinate R :=
  fun j => ∑ a : Vertex, C (affineLiftCoefficient σ o q a j) *
    bubble σ o * barycentric σ o a

theorem affineLift_component_divergence
    (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q : Vertex → Vertex → R) (a : Vertex) :
    divergence (fun j => C (affineLiftCoefficient σ o q a j) *
      bubble σ o * barycentric σ o a) =
      (∑ i : Vertex, if i = a then 0 else
        C (q i a) * faceCubic σ o i * barycentric σ o a) -
        C (2 * affineCoefficientSum q a) * bubble σ o := by
  rw [bubble_constant_barycentric_divergence]
  have ht (i : Vertex) :
      C (∑ j : Coordinate, affineLiftCoefficient σ o q a j *
        barycentricGradient σ i j) * faceCubic σ o i * barycentric σ o a =
      (if i = a then 0 else C (q i a) * faceCubic σ o i * barycentric σ o a) -
        (if i = a then C (affineCoefficientSum q a) * bubble σ o else 0) := by
    rw [affineLiftCoefficient_gradient]
    by_cases hia : i = a
    · subst i
      simp only [if_true, zero_sub, map_neg, neg_mul, affineCoefficientSum]
      rw [mul_assoc, faceCubic_mul_barycentric]
    · simp [hia]
  simp only [ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    affineLiftCoefficient_gradient, zero_sub, map_neg]
  change _ - C (affineCoefficientSum q a) * bubble σ o +
    -C (affineCoefficientSum q a) * bubble σ o = _
  simp only [map_mul, map_ofNat]
  ring

/-- Exact analytic inverse formula for all twelve quartic face coefficients.
The bubble coefficient is precisely the one imposed by the zero-integral
condition: minus twice their sum. -/
theorem affineLift_divergence (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q : Vertex → Vertex → R) :
    divergence (affineLift σ o q) =
      (∑ a : Vertex, ∑ i : Vertex, if i = a then 0 else
        C (q i a) * faceCubic σ o i * barycentric σ o a) -
        C (2 * ∑ a : Vertex, affineCoefficientSum q a) * bubble σ o := by
  have hd : divergence (affineLift σ o q) =
      ∑ a : Vertex, divergence (fun j => C (affineLiftCoefficient σ o q a j) *
        bubble σ o * barycentric σ o a) := by
    simp only [divergence, affineLift, map_sum]
    exact Finset.sum_comm
  rw [hd]
  simp only [affineLift_component_divergence, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum]

def constantLiftLinear (σ : Equiv.Perm Coordinate) (o : Coordinate → R) :
    (Vertex → R) →ₗ[R] (Coordinate → MvPolynomial Coordinate R) where
  toFun d j := C (constantLiftVector σ o d j) * bubble σ o
  map_add' d e := by
    funext j
    simp only [constantLiftVector, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      map_add]
  map_smul' c d := by
    funext j
    simp only [constantLiftVector, Pi.smul_apply, smul_eq_mul, mul_assoc,
      ← Finset.mul_sum, map_mul, smul_eq_C_mul, RingHom.id_apply]

theorem affineLiftCoefficient_add (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (q r : Vertex → Vertex → R) :
    affineLiftCoefficient σ o (q + r) =
      affineLiftCoefficient σ o q + affineLiftCoefficient σ o r := by
  funext a j
  simp only [affineLiftCoefficient, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hia : i = a <;> simp [hia]

theorem affineLiftCoefficient_smul (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (c : R) (q : Vertex → Vertex → R) :
    affineLiftCoefficient σ o (c • q) = c • affineLiftCoefficient σ o q := by
  funext a j
  simp only [affineLiftCoefficient, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum, mul_ite, mul_zero]

def affineLiftLinear (σ : Equiv.Perm Coordinate) (o : Coordinate → R) :
    (Vertex → Vertex → R) →ₗ[R] (Coordinate → MvPolynomial Coordinate R) where
  toFun := affineLift σ o
  map_add' q r := by
    funext j
    simp only [affineLift, affineLiftCoefficient_add, Pi.add_apply, map_add,
      add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    funext j
    simp only [affineLift, affineLiftCoefficient_smul, Pi.smul_apply,
      smul_eq_mul, smul_eq_C_mul, map_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

theorem divergence_eq_polynomialDivergence
    (v : Coordinate → MvPolynomial Coordinate ℝ) :
    divergence v = PolynomialCalculus.polynomialDivergence v := rfl

end FreudenthalSVLean.ElementBubbleAlgebra
