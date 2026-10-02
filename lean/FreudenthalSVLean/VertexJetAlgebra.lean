import FreudenthalSVLean.SkeletonBubble

/-!
# Analytic edge-jet reconstruction at a tetrahedron vertex

For manuscript equation `vertex-jet-map` and the complete-compatibility
lemma `vertex-jets`, this module proves the barycentric duality underlying
the reconstruction of a derivative from the three issuing edge jets.
The identities apply to arbitrary coordinate permutations and translations,
not merely to the six enumerated vertex-star states.

This is local algebra; passage from conforming polynomial data to common
edge jets, boundary constraints, and the mean-preserving star lift are
separate formalization obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.VertexJetAlgebra

variable {R : Type*} [CommRing R]

def direction (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b : Vertex) : Coordinate → R :=
  fun j => chainVertex σ o b j - chainVertex σ o a j

theorem gradient_dot_displacement (σ : Equiv.Perm Coordinate)
    (o x y : Coordinate → R) (i : Vertex) :
    (∑ j : Coordinate, barycentricGradient σ i j * (y j - x j)) =
      eval y (barycentric σ o i) - eval x (barycentric σ o i) := by
  fin_cases i <;>
    simp [barycentricGradient, coordinateUnit, barycentric, chainCoordinate,
      sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib] <;> ring

/-- Barycentric gradients are exactly dual to the issuing edge directions. -/
theorem gradient_dot_edge (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (i a b : Vertex) :
    (∑ j : Coordinate, barycentricGradient σ i j * direction σ o a b j) =
      (if i = b then 1 else 0) - (if i = a then 1 else 0) := by
  simp only [direction]
  rw [gradient_dot_displacement, barycentric_vertex, barycentric_vertex]

/-- Affine coordinate reconstruction by the four barycentric coordinates. -/
theorem coordinate_reconstruction (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → R) (j : Coordinate) :
    (∑ b : Vertex, eval x (barycentric σ o b) * chainVertex σ o b j) = x j := by
  obtain ⟨r, rfl⟩ := σ.surjective j
  fin_cases r <;>
    simp [Fin.sum_univ_succ, barycentric, chainCoordinate, chainVertex] <;> ring

theorem coordinate_polynomial_reconstruction (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (j : Coordinate) :
    (∑ b : Vertex, C (chainVertex σ o b j) * barycentric σ o b) = X j := by
  obtain ⟨r, rfl⟩ := σ.surjective j
  fin_cases r <;>
    simp [Fin.sum_univ_succ, barycentric, chainCoordinate, chainVertex,
      map_add] <;> ring

/-- The coordinate reconstruction identity differentiated in the actual
polynomial ring gives a matrix identity, not an asserted inverse. -/
theorem vertex_gradient_duality (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (j l : Coordinate) :
    (∑ b : Vertex, chainVertex σ o b j * barycentricGradient σ b l) =
      if j = l then 1 else 0 := by
  have hp := congrArg (pderiv l) (coordinate_polynomial_reconstruction σ o j)
  simp only [map_sum, pderiv_C_mul, pderiv_barycentric, pderiv_X,
    Pi.single_apply] at hp
  apply C_injective (σ := Coordinate)
  simpa only [map_sum, map_mul, apply_ite, map_one, map_zero] using hp

theorem direction_gradient_duality (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) (j l : Coordinate) :
    (∑ b : Vertex, direction σ o a b j * barycentricGradient σ b l) =
      if j = l then 1 else 0 := by
  simp only [direction, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    barycentricGradient_sum, mul_zero, sub_zero]
  exact vertex_gradient_duality σ o j l

/-- Any linear functional is reconstructed from its values on the three
issuing edge directions (the fourth, zero direction contributes nothing). -/
theorem gradient_reconstruction (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) (g : Coordinate → R) (l : Coordinate) :
    (∑ b : Vertex,
      (∑ j : Coordinate, g j * direction σ o a b j) *
        barycentricGradient σ b l) = g l := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, direction_gradient_duality]
  simp

def edgeJet (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b : Vertex) (p : MvPolynomial Coordinate R) : R :=
  ∑ j : Coordinate, eval (chainVertex σ o a) (pderiv j p) * direction σ o a b j

theorem edgeJet_self (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) (p : MvPolynomial Coordinate R) : edgeJet σ o a a p = 0 := by
  simp [edgeJet, direction]

theorem edgeJet_eq_fderiv (σ : Equiv.Perm Coordinate) (o : Coordinate → ℝ)
    (a b : Vertex) (p : MvPolynomial Coordinate ℝ) :
    edgeJet σ o a b p =
      fderiv ℝ (fun x => eval x p) (chainVertex σ o a) (direction σ o a b) := by
  rw [PolynomialCalculus.fderiv_eval_apply]
  rfl

/-- Cubic scalar correction with independently prescribed issuing-edge jets. -/
def rawVertexLift (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) (s : Vertex → R) : MvPolynomial Coordinate R :=
  ∑ b : Vertex, if b = a then 0 else s b • SkeletonBubble.vertexBubble σ o a b

/-- The geometry is fixed before the edge-jet input; the correction is one
linear operator on the entire jet space. -/
def rawVertexLiftLinear (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a : Vertex) : (Vertex → R) →ₗ[R] MvPolynomial Coordinate R where
  toFun := rawVertexLift σ o a
  map_add' s t := by
    simp only [rawVertexLift, Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hba : b = a <;> simp [hba]
  map_smul' c s := by
    simp [rawVertexLift, Pi.smul_apply, Finset.smul_sum, smul_ite, smul_smul]

theorem rawVertexLift_derivative (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a l : Vertex) (s : Vertex → R) (i : Coordinate) :
    eval (chainVertex σ o l) (pderiv i (rawVertexLift σ o a s)) =
      ∑ b : Vertex, if b = a then 0 else
        s b * (if l = a then barycentricGradient σ b i else 0) := by
  simp only [rawVertexLift, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hba : b = a
  · simp [hba]
  · simp only [hba, if_false, smul_eq_C_mul, pderiv_C_mul, map_mul, eval_C]
    rw [SkeletonBubble.pderiv_vertexBubble_vertex σ o a b l i (Ne.symm hba)]

/-- Edge jets of an arbitrary polynomial yield a cubic correction with
exactly the same full derivative at the designated vertex. -/
theorem rawVertexLift_reproduces_gradient (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (a : Vertex) (p : MvPolynomial Coordinate R) (i : Coordinate) :
    eval (chainVertex σ o a)
      (pderiv i (rawVertexLift σ o a (fun b => edgeJet σ o a b p))) =
        eval (chainVertex σ o a) (pderiv i p) := by
  rw [rawVertexLift_derivative]
  simp only [if_true]
  have he : (∑ b : Vertex, if b = a then 0 else
      edgeJet σ o a b p * barycentricGradient σ b i) =
        ∑ b : Vertex, edgeJet σ o a b p * barycentricGradient σ b i := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hba : b = a
    · subst b
      simp [edgeJet_self]
    · simp [hba]
  rw [he]
  exact gradient_reconstruction σ o a
    (fun j => eval (chainVertex σ o a) (pderiv j p)) i

/-- The cubic correction has zero derivative at every other vertex. -/
theorem rawVertexLift_protects_other_vertices (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (a l : Vertex) (s : Vertex → R) (i : Coordinate)
    (hla : l ≠ a) :
    eval (chainVertex σ o l) (pderiv i (rawVertexLift σ o a s)) = 0 := by
  rw [rawVertexLift_derivative]
  simp [hla]

end FreudenthalSVLean.VertexJetAlgebra
