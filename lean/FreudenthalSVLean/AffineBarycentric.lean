import FreudenthalSVLean.LowDegreeBubbleExpansion

/-!
# Affine barycentric reconstruction

The affine source space in manuscript Lemma `bubble` and the local jet
arguments is described by its four vertex values.  This module proves
that description for actual spatial polynomials of total degree at most
one, and proves that a vertex combination with weights summing to one has
exactly those barycentric coordinates.  These identities concern every
translated coordinate-chain tetrahedron.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.AffineBarycentric

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]

def affinePoint (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (w : Vertex → R) : Coordinate → R :=
  fun j => ∑ a : Vertex, w a * chainVertex σ o a j

theorem affinePoint_barycentric (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (w : Vertex → R) (hw : ∑ a : Vertex, w a = 1) (i : Vertex) :
    eval (affinePoint σ o w) (barycentric σ o i) = w i := by
  have hv (a : Vertex) :
      (∑ j : Coordinate, barycentricGradient σ i j * chainVertex σ o a j) =
        (if i = a then 1 else 0) - eval (0 : Coordinate → R) (barycentric σ o i) := by
    simpa only [Pi.zero_apply, sub_zero, barycentric_vertex] using
      VertexJetAlgebra.gradient_dot_displacement σ o 0 (chainVertex σ o a) i
  have hs : (∑ j : Coordinate, barycentricGradient σ i j * affinePoint σ o w j) =
      w i - eval (0 : Coordinate → R) (barycentric σ o i) := by
    simp only [affinePoint, Finset.mul_sum]
    rw [Finset.sum_comm]
    have ht (a : Vertex) :
        (∑ j : Coordinate, barycentricGradient σ i j * (w a * chainVertex σ o a j)) =
          w a * (∑ j : Coordinate, barycentricGradient σ i j * chainVertex σ o a j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [ht, hv, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
    simp
  have hp := VertexJetAlgebra.gradient_dot_displacement σ o 0 (affinePoint σ o w) i
  simp only [Pi.zero_apply, sub_zero] at hp
  rw [hs] at hp
  exact (sub_left_inj).mp hp.symm

/-- Every actual affine spatial polynomial is its barycentric interpolation
of the four vertex values; no independent unisolvence assumption is used. -/
theorem affine_interpolation (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (p : MvPolynomial Coordinate ℝ) (hp : p.totalDegree ≤ 1) :
    p = ∑ a : Vertex, C (eval (chainVertex σ o a) p) * barycentric σ o a := by
  let H := HomogeneousBarycentric.representation σ o 1 p
  let c : Vertex → ℝ := fun a => coeff (Finsupp.single a 1) H
  have hH : IsHomogeneous H 1 := HomogeneousBarycentric.representation_homogeneous σ o 1 p
  have hh : H = ∑ a : Vertex, monomial (Finsupp.single a 1) (c a) := by
    apply LowDegreeBubbleExpansion.expansion_of_coefficient_coverage
      (fun a : Vertex => Finsupp.single a 1)
      (Finsupp.single_left_injective (by norm_num : (1 : ℕ) ≠ 0)) H
    intro α hne
    have hd : α.degree = 1 := by
      simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hH hne
    obtain ⟨a, ha⟩ := LowDegreeBubbleIndices.degree_one_single α hd
    exact ⟨a, ha.symm⟩
  have he := congrArg (eval₂Hom C (barycentric σ o)) hh
  rw [HomogeneousBarycentric.substitute_representation σ o 1 p hp] at he
  simp only [map_sum, ← C_mul_X_eq_monomial, map_mul, eval₂Hom_C, eval₂Hom_X'] at he
  have hc (a : Vertex) : eval (chainVertex σ o a) p = c a := by
    have hv := congrArg (eval (chainVertex σ o a)) he
    simpa only [map_sum, map_mul, eval_C, barycentric_vertex, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using hv
  calc
    p = ∑ a : Vertex, C (c a) * barycentric σ o a := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hc]

end FreudenthalSVLean.AffineBarycentric
