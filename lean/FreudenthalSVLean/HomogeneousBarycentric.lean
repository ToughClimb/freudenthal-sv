import FreudenthalSVLean.VertexJetAlgebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!+# Homogeneous barycentric representation of spatial polynomials

The Bernstein-basis argument in manuscript Lemma `bubble` uses homogeneous
degree-three and degree-four polynomials in four barycentric variables to
represent spatial polynomials of degree at most three and four.  This module
constructs that representation from actual spatial polynomials: each
homogeneous spatial component is substituted into homogeneous vertex-coordinate
forms and raised to the prescribed degree by the barycentric sum.  Partition
of unity and affine coordinate reconstruction prove that the spatial
substitution recovers the original polynomial.

No claim about edge-zero coefficient completeness or element-bubble closure
is assumed in this representation theorem.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.HomogeneousBarycentric

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]

def barycentricSum : MvPolynomial Vertex R := ∑ a : Vertex, X a

def coordinateForm (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (j : Coordinate) : MvPolynomial Vertex R :=
  ∑ a : Vertex, C (chainVertex σ o a j) * X a

def representation (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : ℕ) (p : MvPolynomial Coordinate R) : MvPolynomial Vertex R :=
  ∑ m ∈ Finset.range (d + 1), barycentricSum ^ (d - m) *
    eval₂Hom C (coordinateForm σ o) (homogeneousComponent m p)

/-- The geometry and degree are fixed before the polynomial input. -/
def representationLinear (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : ℕ) : MvPolynomial Coordinate R →ₗ[R] MvPolynomial Vertex R where
  toFun := representation σ o d
  map_add' p q := by
    simp only [representation, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [representation, smul_eq_C_mul, homogeneousComponent_C_mul,
      map_mul, eval₂Hom_C, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring

theorem barycentricSum_homogeneous :
    IsHomogeneous (barycentricSum : MvPolynomial Vertex R) 1 := by
  apply IsHomogeneous.sum
  intro a _
  exact isHomogeneous_X R a

theorem coordinateForm_homogeneous (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (j : Coordinate) : IsHomogeneous (coordinateForm σ o j) 1 := by
  apply IsHomogeneous.sum
  intro a _
  exact isHomogeneous_C_mul_X _ _

/-- Homogeneous degree is proved from the actual polynomial construction. -/
theorem representation_homogeneous (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : ℕ) (p : MvPolynomial Coordinate R) :
    IsHomogeneous (representation σ o d p) d := by
  apply IsHomogeneous.sum
  intro m hm
  have hm' : m ≤ d := by simpa using (Finset.mem_range.mp hm)
  have hs : IsHomogeneous (barycentricSum ^ (d - m) : MvPolynomial Vertex R) (d - m) := by
    simpa using (barycentricSum_homogeneous (R := R)).pow (d - m)
  have hc : IsHomogeneous
      (eval₂Hom C (coordinateForm σ o) (homogeneousComponent m p)) m := by
    simpa only [one_mul, coe_eval₂Hom] using
      (homogeneousComponent_isHomogeneous m p).eval₂ C (coordinateForm σ o)
        (fun r => isHomogeneous_C Vertex r) (coordinateForm_homogeneous σ o)
  simpa only [Nat.sub_add_cancel hm'] using hs.mul hc

theorem substitute_barycentricSum (σ : Equiv.Perm Coordinate) (o : Coordinate → R) :
    eval₂Hom C (barycentric σ o) (barycentricSum : MvPolynomial Vertex R) = 1 := by
  simp only [barycentricSum, map_sum, eval₂Hom_X']
  exact barycentric_sum σ o

theorem substitute_coordinateForm (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (j : Coordinate) :
    eval₂Hom C (barycentric σ o) (coordinateForm σ o j) = X j := by
  simp only [coordinateForm, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']
  exact VertexJetAlgebra.coordinate_polynomial_reconstruction σ o j

theorem substitute_coordinateForms (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (p : MvPolynomial Coordinate R) :
    eval₂Hom C (barycentric σ o) (eval₂Hom C (coordinateForm σ o) p) = p := by
  rw [← RingHom.comp_apply]
  have hc : (eval₂Hom C (barycentric σ o)).comp (eval₂Hom C (coordinateForm σ o)) =
      RingHom.id (MvPolynomial Coordinate R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simpa only [RingHom.comp_apply, eval₂Hom_X', RingHom.id_apply] using
        substitute_coordinateForm σ o j
  rw [hc]
  rfl

/-- The usual homogeneous-component sum with any degree bound, not just
the actual total degree of the polynomial. -/
theorem sum_components_of_degree_le (d : ℕ) (p : MvPolynomial Coordinate R)
    (hp : p.totalDegree ≤ d) :
    (∑ m ∈ Finset.range (d + 1), homogeneousComponent m p) = p := by
  calc
    _ = ∑ m ∈ Finset.range (p.totalDegree + 1), homogeneousComponent m p := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp 1))
      intro m _ hm
      apply homogeneousComponent_eq_zero
      have ht : p.totalDegree + 1 ≤ m := by
        simpa only [Finset.mem_range, not_lt] using hm
      omega
    _ = p := sum_homogeneousComponent p

/-- Every degree-bounded spatial polynomial is the actual substitution of
a homogeneous polynomial in the four barycentric variables. -/
theorem substitute_representation (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (d : ℕ) (p : MvPolynomial Coordinate R) (hp : p.totalDegree ≤ d) :
    eval₂Hom C (barycentric σ o) (representation σ o d p) = p := by
  simp only [representation, map_sum, map_mul, map_pow, substitute_barycentricSum,
    one_pow, one_mul, substitute_coordinateForms]
  exact sum_components_of_degree_le d p hp

end FreudenthalSVLean.HomogeneousBarycentric
