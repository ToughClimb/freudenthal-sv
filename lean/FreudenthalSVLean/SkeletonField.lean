import FreudenthalSVLean.NodalMesh
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Global barycentric skeleton-product fields

This module implements the common nodal-product structure in manuscript
Lemma `skeleton-bubble`, the vertex raw correction, face transfers, and
endpoint/middle edge bubbles.  For arbitrary fixed lattice nodes and
natural exponents, it proves the degree bound, conformity, homogeneous
boundary values, and zero polynomial on any element missing a required
node.  Thus the local product identities have actual global finite-element
realizations whenever the explicitly stated boundary-plane condition holds.
Local trace matching, exact face adjacency, and uniform patch size are
separate geometry and lifting obligations.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.NodalMesh

noncomputable section

namespace FreudenthalSVLean.SkeletonField

variable {I : Type*} [Fintype I]

def scalarField {N : ℕ} (nodes : I → Fin 3 → ℤ) (α : I → ℕ)
    (t : Tet N) : MvPolynomial (Fin 3) ℝ :=
  ∏ i : I, meshNodalPolynomial t (nodes i) ^ α i

def vectorField (N : ℕ) (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (s : Space) :
    BrokenVelocity N := fun t j => C (s j) * scalarField nodes α t

def activeSkeleton (N : ℕ) (nodes : I → Fin 3 → ℤ) (α : I → ℕ) : Prop :=
  ∀ j : Fin 3,
    (∃ i : I, 0 < α i ∧ nodes i j ≠ 0) ∧
      (∃ i : I, 0 < α i ∧ nodes i j ≠ (N : ℤ))

theorem scalarField_degree {N : ℕ} (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (t : Tet N) :
    (scalarField nodes α t).totalDegree ≤ ∑ i : I, α i := by
  apply (totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans
    (by simpa using (Nat.mul_le_mul_left (α i) (meshNodalPolynomial_degree_le t (nodes i))))

theorem vectorField_degree {N : ℕ} (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (s : Space)
    (t : Tet N) (j : Fin 3) :
    (vectorField N nodes α s t j).totalDegree ≤ ∑ i : I, α i :=
  (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C, zero_add] using scalarField_degree nodes α t)

/-- The evaluation uses one globally defined continuous function. -/
theorem scalarField_eval {N : ℕ} (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (t : Tet N)
    (x : Space) (hx : x ∈ tetrahedron t) :
    eval x (scalarField nodes α t) = ∏ i : I, meshNodal N (nodes i) x ^ α i := by
  simp only [scalarField, map_prod, map_pow, meshNodalPolynomial_eval t _ x hx]

theorem vectorField_conforming {N : ℕ} (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (s : Space)
    (t u : Tet N) (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u)
    (j : Fin 3) : eval x (vectorField N nodes α s t j) =
      eval x (vectorField N nodes α s u j) := by
  simp only [vectorField, map_mul, eval_C, scalarField_eval nodes α t x ht,
    scalarField_eval nodes α u x hu]

theorem scalarField_boundary_zero {N : ℕ} (hN : 0 < N) (nodes : I → Fin 3 → ℤ)
    (α : I → ℕ) (hn : ∀ i, nodeInBox N (nodes i)) (ha : activeSkeleton N nodes α)
    (t : Tet N) (x : Space) (ht : x ∈ tetrahedron t) (hx : x ∈ cubeBoundary) :
    eval x (scalarField nodes α t) = 0 := by
  rw [scalarField_eval nodes α t x ht]
  obtain ⟨j, hj⟩ := hx.2
  rcases hj with hj | hj
  · obtain ⟨i, hi, hin⟩ := (ha j).1
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [meshNodal_zero_lower (nodes i) (hn i) x j hj hin]
    exact zero_pow (Nat.ne_of_gt hi)
  · obtain ⟨i, hi, hin⟩ := (ha j).2
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [meshNodal_zero_upper hN (nodes i) (hn i) x j hj hin]
    exact zero_pow (Nat.ne_of_gt hi)

/-- All skeleton-product fields satisfying the fixed geometric conditions
are members of the actual defined conforming velocity space. -/
theorem vectorField_mem_velocitySpace {N k : ℕ} (hN : 0 < N)
    (nodes : I → Fin 3 → ℤ) (α : I → ℕ) (hn : ∀ i, nodeInBox N (nodes i))
    (ha : activeSkeleton N nodes α) (hk : (∑ i : I, α i) ≤ k) (s : Space) :
    vectorField N nodes α s ∈ velocitySpace N k := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    exact (vectorField_degree nodes α s t j).trans hk
  · intro t u x ht hu j
    exact vectorField_conforming nodes α s t u x ht hu j
  · intro t x ht hx j
    simp only [vectorField, map_mul, eval_C,
      scalarField_boundary_zero hN nodes α hn ha t x ht hx, mul_zero]

theorem scalarField_zero_of_missing_node {N : ℕ} (nodes : I → Fin 3 → ℤ)
    (α : I → ℕ) (t : Tet N) (i : I) (hi : 0 < α i)
    (hn : ∀ a : Fin 4, GridNodalSupport.intPoint (nodes i) ≠
      ChainGeometry.chainVertex t.2 (cellOrigin t.1) a) : scalarField nodes α t = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [meshNodalPolynomial_zero_of_not_vertex t (nodes i) hn]
  exact zero_pow (Nat.ne_of_gt hi)

end FreudenthalSVLean.SkeletonField
