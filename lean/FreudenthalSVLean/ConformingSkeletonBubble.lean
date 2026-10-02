import FreudenthalSVLean.NodalMesh
import FreudenthalSVLean.SkeletonBubble

/-!
# Conforming supported edge and vertex skeleton bubbles

For manuscript Lemma `vertex-jets` and equation `vertex-raw-bubble`, this
module proves that the nodal products `φ_n φ_m` and `φ_n² φ_m` are actual
members of `V_{h,k}` whenever their lattice endpoints do not share a
physical boundary plane.  Degree, conformity, and homogeneous boundary
values are all proved from the global nodal representation.  A node absent
from a tetrahedron makes the local polynomial identically zero.
The endpoints' being a geometric mesh edge is needed for the subsequent
jet indexing, not for this conformity and boundary result.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.NodalMesh

noncomputable section

namespace FreudenthalSVLean.ConformingSkeletonBubble

def activePair (N : ℕ) (n m : Fin 3 → ℤ) : Prop :=
  ∀ j : Fin 3, (n j ≠ 0 ∨ m j ≠ 0) ∧ (n j ≠ (N : ℤ) ∨ m j ≠ (N : ℤ))

def edgeBubbleField (N r : ℕ) (n m : Fin 3 → ℤ) (s : Space) : BrokenVelocity N :=
  fun t j => C (s j) * meshNodalPolynomial t n ^ r * meshNodalPolynomial t m

theorem edgeBubbleField_degree {N r : ℕ} (n m : Fin 3 → ℤ) (s : Space)
    (t : Tet N) (j : Fin 3) :
    (edgeBubbleField N r n m s t j).totalDegree ≤ r + 1 := by
  have hp : (meshNodalPolynomial t n ^ r).totalDegree ≤ r :=
    (totalDegree_pow _ _).trans (by simpa using
      (Nat.mul_le_mul_left r (meshNodalPolynomial_degree_le t n)))
  have hcp : (C (s j) * meshNodalPolynomial t n ^ r).totalDegree ≤ r :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hp)
  exact (totalDegree_mul _ _).trans (add_le_add hcp (meshNodalPolynomial_degree_le t m))

theorem edgeBubbleField_conforming {N r : ℕ} (n m : Fin 3 → ℤ) (s : Space)
    (t u : Tet N) (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u)
    (j : Fin 3) : eval x (edgeBubbleField N r n m s t j) =
      eval x (edgeBubbleField N r n m s u j) := by
  simp only [edgeBubbleField, map_mul, map_pow, eval_C,
    meshNodalPolynomial_eval t n x ht, meshNodalPolynomial_eval t m x ht,
    meshNodalPolynomial_eval u n x hu, meshNodalPolynomial_eval u m x hu]

theorem edgeBubbleField_boundary_zero {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (n m : Fin 3 → ℤ) (hn : nodeInBox N n) (hm : nodeInBox N m)
    (ha : activePair N n m) (s : Space) (t : Tet N) (x : Space)
    (ht : x ∈ tetrahedron t) (hx : x ∈ cubeBoundary) (j : Fin 3) :
    eval x (edgeBubbleField N r n m s t j) = 0 := by
  simp only [edgeBubbleField, map_mul, map_pow, eval_C,
    meshNodalPolynomial_eval t n x ht, meshNodalPolynomial_eval t m x ht]
  obtain ⟨l, hl⟩ := hx.2
  rcases hl with hl | hl
  · rcases (ha l).1 with hnl | hml
    · rw [meshNodal_zero_lower n hn x l hl hnl]
      simp [Nat.ne_of_gt hr]
    · rw [meshNodal_zero_lower m hm x l hl hml]
      simp
  · rcases (ha l).2 with hnl | hml
    · rw [meshNodal_zero_upper hN n hn x l hl hnl]
      simp [Nat.ne_of_gt hr]
    · rw [meshNodal_zero_upper hN m hm x l hl hml]
      simp

/-- Quadratic and cubic instances give, respectively, the complete edge-jet
realization and raw supported vertex correction in the manuscript. -/
theorem edgeBubbleField_mem_velocitySpace {N k r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hk : r + 1 ≤ k) (n m : Fin 3 → ℤ) (hn : nodeInBox N n) (hm : nodeInBox N m)
    (ha : activePair N n m) (s : Space) :
    edgeBubbleField N r n m s ∈ velocitySpace N k := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    exact (edgeBubbleField_degree n m s t j).trans hk
  · intro t u x ht hu j
    exact edgeBubbleField_conforming n m s t u x ht hu j
  · intro t x ht hx j
    exact edgeBubbleField_boundary_zero hN hr n m hn hm ha s t x ht hx j

theorem edgeBubbleField_zero_of_missing_first {N r : ℕ} (hr : 0 < r)
    (n m : Fin 3 → ℤ) (s : Space) (t : Tet N)
    (hn : ∀ a : Fin 4, GridNodalSupport.intPoint n ≠
      ChainGeometry.chainVertex t.2 (cellOrigin t.1) a) (j : Fin 3) :
    edgeBubbleField N r n m s t j = 0 := by
  rw [edgeBubbleField, meshNodalPolynomial_zero_of_not_vertex t n hn]
  simp [Nat.ne_of_gt hr]

theorem edgeBubbleField_zero_of_missing_second {N r : ℕ}
    (n m : Fin 3 → ℤ) (s : Space) (t : Tet N)
    (hm : ∀ a : Fin 4, GridNodalSupport.intPoint m ≠
      ChainGeometry.chainVertex t.2 (cellOrigin t.1) a) (j : Fin 3) :
    edgeBubbleField N r n m s t j = 0 := by
  rw [edgeBubbleField, meshNodalPolynomial_zero_of_not_vertex t m hm]
  simp

/-- On an incident tetrahedron the global field is precisely the scaled
local cubic whose jets were derived in `SkeletonBubble`. -/
theorem cubicField_on_incident_tet {N : ℕ} (n m : Fin 3 → ℤ) (s : Space)
    (t : Tet N) (a b : Fin 4)
    (hn : GridNodalSupport.intPoint n = ChainGeometry.chainVertex t.2 (cellOrigin t.1) a)
    (hm : GridNodalSupport.intPoint m = ChainGeometry.chainVertex t.2 (cellOrigin t.1) b)
    (j : Fin 3) :
    edgeBubbleField N 2 n m s t j = PolynomialScaling.rescale (meshScale N) (s j)
      (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b) := by
  rw [edgeBubbleField, meshNodalPolynomial_eq_barycentric t n a hn,
    meshNodalPolynomial_eq_barycentric t m b hm]
  simp [PolynomialScaling.rescale, SkeletonBubble.vertexBubble, barycentric,
    ScaledChainGeometry.scaledBarycentric, mul_assoc]

theorem cubicField_vertex_derivative {N : ℕ} (hN : 0 < N)
    (n m : Fin 3 → ℤ) (s : Space) (t : Tet N) (a b l : Fin 4) (hab : a ≠ b)
    (hn : GridNodalSupport.intPoint n = ChainGeometry.chainVertex t.2 (cellOrigin t.1) a)
    (hm : GridNodalSupport.intPoint m = ChainGeometry.chainVertex t.2 (cellOrigin t.1) b)
    (i j : Fin 3) :
    eval (vertex t l) (pderiv i (edgeBubbleField N 2 n m s t j)) =
      (s j * (meshScale N)⁻¹) *
        if l = a then ChainGeometry.barycentricGradient t.2 b i else 0 := by
  rw [cubicField_on_incident_tet n m s t a b hn hm j,
    PolynomialScaling.pderiv_rescale, PolynomialScaling.rescale_eval]
  have he : (meshScale N)⁻¹ • vertex t l =
      ChainGeometry.chainVertex t.2 (cellOrigin t.1) l := by
    simp only [vertex, ScaledChainGeometry.scaledVertex, smul_smul,
      inv_mul_cancel₀ (meshScale_pos N hN).ne', one_smul]
  rw [he, SkeletonBubble.pderiv_vertexBubble_vertex t.2 (cellOrigin t.1) a b l i hab]

/-- Cubic global fields protect all non-designated vertex incidences. -/
theorem cubicField_protects_other_vertices {N : ℕ} (hN : 0 < N)
    (n m : Fin 3 → ℤ) (s : Space) (t : Tet N) (a b l : Fin 4)
    (hab : a ≠ b) (hla : l ≠ a)
    (hn : GridNodalSupport.intPoint n = ChainGeometry.chainVertex t.2 (cellOrigin t.1) a)
    (hm : GridNodalSupport.intPoint m = ChainGeometry.chainVertex t.2 (cellOrigin t.1) b)
    (i j : Fin 3) :
    eval (vertex t l) (pderiv i (edgeBubbleField N 2 n m s t j)) = 0 := by
  rw [cubicField_vertex_derivative hN n m s t a b l hab hn hm i j, if_neg hla, mul_zero]

end FreudenthalSVLean.ConformingSkeletonBubble
