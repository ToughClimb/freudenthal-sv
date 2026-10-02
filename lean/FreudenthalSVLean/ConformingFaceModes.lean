import FreudenthalSVLean.ActualFaceMean
import FreudenthalSVLean.EdgeBubble

/-!
# Actual conforming face modes for the edge lift

For manuscript equations `endpoint-face-bubble` and `middle-face-bubble`,
the endpoint and middle fields are weighted global three-node face
products.  Arbitrary nonnegative nodal powers preserve conformity,
homogeneous boundary values, two-owner support, and zero vertex
derivatives.  The degree bound is `3+p+q`.  Local identification with the
actual positively scaled barycentric polynomials follows directly from
the proved global nodal representation.

Incidence spanning and borrowed-face cancellation are separate
obligations, not assumed by these global realization statements.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.FaceBubbleMean

noncomputable section

namespace FreudenthalSVLean.ConformingFaceModes

def weightedFaceField (N : ℕ) (t : Tet N) (r : Vertex) (a b : GridVertex N)
    (p q : ℕ) (z : Space) : BrokenVelocity N :=
  fun v j => C (z j) * faceScalar t r v *
    meshNodalPolynomial v (integerGrid a) ^ p * meshNodalPolynomial v (integerGrid b) ^ q

def weightedFaceLinear (N : ℕ) (t : Tet N) (r : Vertex) (a b : GridVertex N)
    (p q : ℕ) : Space →ₗ[ℝ] BrokenVelocity N where
  toFun := weightedFaceField N t r a b p q
  map_add' z w := by
    funext v j
    simp [weightedFaceField, Pi.add_apply, map_add, add_mul]
  map_smul' c z := by
    funext v j
    simp [weightedFaceField, Pi.smul_apply, smul_eq_C_mul, map_mul, mul_assoc]

theorem weightedFaceField_degree {N : ℕ} (t : Tet N) (r : Vertex) (a b : GridVertex N)
    (p q : ℕ) (z : Space) (v : Tet N) (j : Coordinate) :
    (weightedFaceField N t r a b p q z v j).totalDegree ≤ 3 + p + q := by
  have ha : (meshNodalPolynomial v (integerGrid a) ^ p).totalDegree ≤ p :=
    (totalDegree_pow _ _).trans (by simpa using
      (Nat.mul_le_mul_left p (meshNodalPolynomial_degree_le v (integerGrid a))))
  have hb : (meshNodalPolynomial v (integerGrid b) ^ q).totalDegree ≤ q :=
    (totalDegree_pow _ _).trans (by simpa using
      (Nat.mul_le_mul_left q (meshNodalPolynomial_degree_le v (integerGrid b))))
  have hf : (C (z j) * faceScalar t r v).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using faceScalar_degree t v r)
  exact (totalDegree_mul _ _).trans (add_le_add
    ((totalDegree_mul _ _).trans (add_le_add hf ha)) hb)

theorem weightedFaceField_conforming {N : ℕ} (t : Tet N) (r : Vertex) (a b : GridVertex N)
    (p q : ℕ) (z : Space) (v w : Tet N) (x : Space)
    (hv : x ∈ tetrahedron v) (hw : x ∈ tetrahedron w) (j : Coordinate) :
    eval x (weightedFaceField N t r a b p q z v j) =
      eval x (weightedFaceField N t r a b p q z w j) := by
  simp only [weightedFaceField, map_mul, map_pow, eval_C,
    faceScalar_conforming t r v w x hv hw,
    meshNodalPolynomial_eval v _ x hv, meshNodalPolynomial_eval w _ x hw]

theorem weightedFaceField_boundary_zero {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex)
    (ha : activeGridFace t r) (a b : GridVertex N) (p q : ℕ) (z : Space)
    (v : Tet N) (x : Space) (hv : x ∈ tetrahedron v) (hx : x ∈ cubeBoundary) (j : Coordinate) :
    eval x (weightedFaceField N t r a b p q z v j) = 0 := by
  simp only [weightedFaceField, map_mul, faceScalar_boundary_zero hN t r ha v x hv hx,
    mul_zero, zero_mul]

theorem weightedFaceField_mem_velocitySpace {N k : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex)
    (ha : activeGridFace t r) (a b : GridVertex N) (p q : ℕ) (hk : 3 + p + q ≤ k)
    (z : Space) : weightedFaceField N t r a b p q z ∈ velocitySpace N k := by
  refine ⟨?_, ?_, ?_⟩
  · intro v j
    exact (weightedFaceField_degree t r a b p q z v j).trans hk
  · intro v w x hv hw j
    exact weightedFaceField_conforming t r a b p q z v w x hv hw j
  · intro v x hv hx j
    exact weightedFaceField_boundary_zero hN t r ha a b p q z v x hv hx j

def weightedConformingLinear {N k : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex)
    (ha : activeGridFace t r) (a b : GridVertex N) (p q : ℕ) (hk : 3 + p + q ≤ k) :
    Space →ₗ[ℝ] velocitySpace N k :=
  (weightedFaceLinear N t r a b p q).codRestrict _
    (weightedFaceField_mem_velocitySpace hN t r ha a b p q hk)

theorem weightedFaceField_zero_off_pair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u) (a b : GridVertex N)
    (p q : ℕ) (z : Space) (v : Tet N) (hva : v ≠ ta.val.1) (hvb : v ≠ tb.val.1)
    (j : Coordinate) : weightedFaceField N ta.val.1 r a b p q z v j = 0 := by
  simp only [weightedFaceField, faceScalar_zero_off_pair ta tb r u hr hne he v hva hvb,
    mul_zero, zero_mul]

theorem faceScalar_vertex {N : ℕ} (hN : 0 < N) (t : Tet N) (r l : Vertex) :
    eval (vertex t l) (faceScalar t r t) = 0 := by
  rw [faceScalar_self, map_prod]
  obtain ⟨a, b, _, har, _, hal, _⟩ := face_missing_pair r l
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨har, Finset.mem_univ _⟩)
  rw [FreudenthalMesh.barycentric_vertex hN, if_neg hal]

theorem faceScalar_pderiv_vertex {N : ℕ} (hN : 0 < N) (t : Tet N) (r l : Vertex)
    (i : Coordinate) : eval (vertex t l) (pderiv i (faceScalar t r t)) = 0 := by
  have h := faceField_pderiv_vertex hN t r l (fun _ => 1) i 0
  simpa only [faceField, C_1, one_mul] using h

theorem faceScalar_all_vertices {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (v : Tet N) (l : Vertex) : eval (vertex v l) (faceScalar ta.val.1 r v) = 0 := by
  by_cases hva : v = ta.val.1
  · subst v
    exact faceScalar_vertex hN _ _ _
  · by_cases hvb : v = tb.val.1
    · subst v
      rw [faceScalar_shared _ _ _ _ he]
      exact faceScalar_vertex hN _ _ _
    · rw [faceScalar_zero_off_pair ta tb r u hr hne he v hva hvb, map_zero]

theorem faceScalar_all_vertex_derivatives {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (v : Tet N) (l : Vertex) (i : Coordinate) :
    eval (vertex v l) (pderiv i (faceScalar ta.val.1 r v)) = 0 := by
  by_cases hva : v = ta.val.1
  · subst v
    exact faceScalar_pderiv_vertex hN _ _ _ _
  · by_cases hvb : v = tb.val.1
    · subst v
      rw [faceScalar_shared _ _ _ _ he]
      exact faceScalar_pderiv_vertex hN _ _ _ _
    · rw [faceScalar_zero_off_pair ta tb r u hr hne he v hva hvb, map_zero, map_zero]

/-- Multiplying the face bubble by nodal factors preserves every vertex
derivative on both owners and on all other mesh tetrahedra. -/
theorem weightedFaceField_protects_vertices {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (a b : GridVertex N) (p q : ℕ) (z : Space) (v : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex v l) (pderiv i (weightedFaceField N ta.val.1 r a b p q z v j)) = 0 := by
  simp only [weightedFaceField, pderiv_mul, pderiv_C, map_add, map_mul, map_zero,
    faceScalar_all_vertices hN ta tb r u hr hne he v l,
    faceScalar_all_vertex_derivatives hN ta tb r u hr hne he v l i,
    mul_zero, zero_mul, add_zero]

theorem weightedFaceField_self_rescale {N : ℕ} (t : Tet N) (r a b : Vertex)
    (p q : ℕ) (z : Space) (j : Coordinate) :
    weightedFaceField N t r (gridVertexOfTet t a) (gridVertexOfTet t b) p q z t j =
      rescale (meshScale N) (z j) (spatialFaceBubble t.2 (cellOrigin t.1) r *
        ChainGeometry.barycentric t.2 (cellOrigin t.1) a ^ p *
          ChainGeometry.barycentric t.2 (cellOrigin t.1) b ^ q) := by
  rw [weightedFaceField, faceScalar_self_rescale,
    meshNodalPolynomial_eq_barycentric t _ a (gridVertex_intPoint t a),
    meshNodalPolynomial_eq_barycentric t _ b (gridVertex_intPoint t b)]
  simp only [rescale, C_1, one_mul, map_mul, map_pow,
    FreudenthalMesh.barycentric, ScaledChainGeometry.scaledBarycentric, mul_assoc]

end FreudenthalSVLean.ConformingFaceModes
