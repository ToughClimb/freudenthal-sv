import FreudenthalSVLean.ActualCanonicalFaces
import FreudenthalSVLean.UniversalFaceEdgeTrace

/-!
# Nodal multiplication of zero-edge-trace fields

For the endpoint and middle modes in manuscript Lemma `edge-star`,
multiplication of a quartic face pattern by a global endpoint hat produces
the quintic modes.  Every three-node face product has zero value on every
mesh edge.  The product rule therefore multiplies its divergence trace
by the endpoint hat, with no extra edge term.  This proves the quintic
endpoint factors and middle factor from the quartic construction, including
the borrowed term.  Conformity, boundary values, and protected vertex
derivatives are preserved as actual polynomial identities.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.FaceModeTraces
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.ActualCanonicalFaces

noncomputable section

namespace FreudenthalSVLean.ConformingNodalMultiplication

theorem physical_barycentric_edge {N : ℕ} (hN : 0 < N) (t : Tet N)
    (a l m : Vertex) (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x) (FreudenthalMesh.barycentric t a) =
      (1 - x) * (if a = l then 1 else 0) + x * (if a = m then 1 else 0) := by
  rw [FreudenthalMesh.barycentric, scaledBarycentric_eval, scaled_segment_inverse hN]
  exact ChainGeometry.barycentric_edge _ _ _ _ _ _

theorem nodal_physical_edge {N : ℕ} (hN : 0 < N) (t : Tet N) (n : GridVertex N)
    (l m : Vertex) (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x) (meshNodalPolynomial t (integerGrid n)) =
      (1 - x) * (if n = gridVertexOfTet t l then 1 else 0) +
        x * (if n = gridVertexOfTet t m then 1 else 0) := by
  classical
  by_cases hn : n ∈ gridVertices t
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hn
    rw [← ha, meshNodalPolynomial_eq_barycentric t _ a (gridVertex_intPoint t a),
      physical_barycentric_edge hN]
    simp only [(gridVertexOfTet_injective t).eq_iff]
  · have hl : n ≠ gridVertexOfTet t l := by
      intro he
      apply hn
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, he.symm⟩
    have hm : n ≠ gridVertexOfTet t m := by
      intro he
      apply hn
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, he.symm⟩
    simp [node_polynomial_zero_of_missing t n hn, hl, hm]

/-- A three-node face product has zero value on every local mesh edge,
even on tetrahedra which do not contain its defining face. -/
theorem faceScalar_all_edge_values {N : ℕ} (hN : 0 < N) (t v : Tet N)
    (r l m : Vertex) (x : ℝ) :
    eval (segmentPoint (vertex v l) (vertex v m) x) (faceScalar t r v) = 0 := by
  classical
  have hmissing : ¬ gridFace t r ⊆ ({gridVertexOfTet v l, gridVertexOfTet v m} : Finset (GridVertex N)) := by
    intro hs
    have hc := Finset.card_le_card hs
    have hp : ({gridVertexOfTet v l, gridVertexOfTet v m} : Finset (GridVertex N)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [gridFace_card] at hc
    omega
  obtain ⟨n, hn, he⟩ := Finset.not_subset.mp hmissing
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
  rw [faceScalar, map_prod]
  apply Finset.prod_eq_zero hn
  simp [nodal_physical_edge hN v n l m x, he.1, he.2]

theorem patternField_all_edge_values {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c)) (e : ℕ)
    (t : Tet N) (l m : Vertex) (x : ℝ) (j : Coordinate) :
    eval (segmentPoint (vertex t l) (vertex t m) x) (patternField hN a b c hd hl side p e t j) = 0 := by
  simp only [patternField, Finset.sum_apply, map_sum, termField, weightedFaceField,
    map_mul, faceScalar_all_edge_values hN _ t _ l m x, mul_zero, zero_mul, Finset.sum_const_zero]

def multiplyNode {N : ℕ} (n : GridVertex N) : BrokenVelocity N →ₗ[ℝ] BrokenVelocity N where
  toFun v t j := meshNodalPolynomial t (integerGrid n) * v t j
  map_add' v w := by
    funext t j
    simp [Pi.add_apply, mul_add]
  map_smul' s v := by
    funext t j
    simp [Pi.smul_apply, smul_eq_C_mul, mul_left_comm]

theorem multiplyNode_mem {N k : ℕ} (n : GridVertex N) (v : velocitySpace N k) :
    multiplyNode n v.val ∈ velocitySpace N (k + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    exact (totalDegree_mul _ _).trans ((add_le_add
      (meshNodalPolynomial_degree_le t (integerGrid n)) (v.property.1 t j)).trans (by omega))
  · intro t u x ht hu j
    simp only [multiplyNode, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
      meshNodalPolynomial_conforming t u _ x ht hu, v.property.2.1 t u x ht hu j]
  · intro t x ht hx j
    simp only [multiplyNode, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
      v.property.2.2 t x ht hx j, mul_zero]

def multiplyConforming {N k : ℕ} (n : GridVertex N) :
    velocitySpace N k →ₗ[ℝ] velocitySpace N (k + 1) :=
  ((multiplyNode n).comp (velocitySpace N k).subtype).codRestrict _ (multiplyNode_mem n)

/-- Zero velocity values on the edge remove the derivative-of-hat term. -/
theorem multiplyNode_edge_divergence {N : ℕ} (n : GridVertex N) (v : BrokenVelocity N)
    (t : Tet N) (l m : Vertex) (x : ℝ)
    (hz : ∀ j : Coordinate, eval (segmentPoint (vertex t l) (vertex t m) x) (v t j) = 0) :
    eval (segmentPoint (vertex t l) (vertex t m) x) (divergence N (multiplyNode n v) t) =
      eval (segmentPoint (vertex t l) (vertex t m) x) (meshNodalPolynomial t (integerGrid n)) *
        eval (segmentPoint (vertex t l) (vertex t m) x) (divergence N v t) := by
  simp only [divergence, multiplyNode, LinearMap.coe_mk, AddHom.coe_mk,
    pderiv_mul, map_sum, map_add, map_mul, hz, mul_zero, zero_add]
  rw [Finset.mul_sum]

theorem multiplyNode_vertex_derivative {N : ℕ} (n : GridVertex N) (v : BrokenVelocity N)
    (t : Tet N) (l : Vertex) (i j : Coordinate)
    (hz : eval (vertex t l) (v t j) = 0)
    (hd : eval (vertex t l) (pderiv i (v t j)) = 0) :
    eval (vertex t l) (pderiv i (multiplyNode n v t j)) = 0 := by
  simp only [multiplyNode, LinearMap.coe_mk, AddHom.coe_mk,
    pderiv_mul, map_add, map_mul, hz, hd, mul_zero, add_zero]

end FreudenthalSVLean.ConformingNodalMultiplication
