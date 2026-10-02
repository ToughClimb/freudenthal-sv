import FreudenthalSVLean.ActualFaceEdgeTraces

/-!
# Unified face-bubble trace on every local edge

For manuscript equations `endpoint-face-bubble` and `endpoint-bubble-first`,
the derivative of a three-node face product on an arbitrary tetrahedron
edge is its two remaining edge coordinates times the gradient of the
missing face coordinate.  Multiplication by a positive endpoint power
gives one orientation-aware trace formula.  This is a polynomial identity
for arbitrary coordinate order, translation, exponent, and edge parameter;
the finite four-vertex index calculations merely expand the product rule.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.PolynomialCalculus
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.FaceModeTraces

noncomputable section

namespace FreudenthalSVLean.UniversalFaceEdgeTrace

def faceEdgeGradient {R : Type*} [CommRing R]
    (σ : Equiv.Perm Coordinate) (r l m : Vertex) (j : Coordinate) : R :=
  if l ≠ r ∧ m ≠ r then
    ∑ u : Vertex, if u ≠ r ∧ u ≠ l ∧ u ≠ m then barycentricGradient σ u j else 0
  else 0

theorem face_edge_value (σ : Equiv.Perm Coordinate) (o : Space)
    (r l m : Vertex) (hlm : l ≠ m) (s : ℝ) :
    eval (segmentPoint (chainVertex σ o l) (chainVertex σ o m) s)
      (spatialFaceBubble σ o r) = 0 := by
  rw [spatialFaceBubble_eq_product]
  rw [← Finset.prod_ite_mem_eq]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  fin_cases r <;> fin_cases l <;> fin_cases m <;> simp_all [Fin.prod_univ_succ, barycentric_edge]

set_option maxHeartbeats 1000000 in
theorem face_edge_derivative (σ : Equiv.Perm Coordinate) (o : Space)
    (r l m : Vertex) (hlm : l ≠ m) (s : ℝ) (j : Coordinate) :
    eval (segmentPoint (chainVertex σ o l) (chainVertex σ o m) s)
      (pderiv j (spatialFaceBubble σ o r)) =
      ((1 - s) * s) * faceEdgeGradient σ r l m j := by
  rw [spatialFaceBubble_derivative]
  simp only [map_sum, map_mul, eval_C, PolynomialCalculus.eval_substitution]
  fin_cases r <;> fin_cases l <;> fin_cases m <;>
    simp_all [faceEdgeGradient, faceBarycentricPolynomial, faceExponent_apply,
      pderiv_monomial, eval_monomial, Finsupp.prod_fintype, Finsupp.tsub_apply,
      Finsupp.single_apply, barycentric_edge, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

def endpointFactor (p : ℕ) (a l m : Vertex) (s : ℝ) : ℝ :=
  if a = l then (1 - s) ^ (p + 1) * s
  else if a = m then (1 - s) * s ^ (p + 1) else 0

/-- A single formula includes the target edge, its possible spill edge,
and every other local edge. -/
theorem endpoint_face_edge_derivative (σ : Equiv.Perm Coordinate) (o : Space)
    (r a l m : Vertex) (p : ℕ) (hp : 0 < p) (hlm : l ≠ m) (s : ℝ) (j : Coordinate) :
    eval (segmentPoint (chainVertex σ o l) (chainVertex σ o m) s)
      (pderiv j (spatialFaceBubble σ o r * ChainGeometry.barycentric σ o a ^ p)) =
      endpointFactor p a l m s * faceEdgeGradient σ r l m j := by
  rw [pderiv_mul]
  simp only [map_add, map_mul, map_pow, face_edge_value σ o r l m hlm s,
    zero_mul, add_zero, face_edge_derivative σ o r l m hlm s j, barycentric_edge]
  by_cases hal : a = l
  · subst a
    simp only [if_true, if_neg hlm, mul_one, mul_zero, add_zero, endpointFactor]
    ring
  · by_cases ham : a = m
    · subst a
      simp only [if_neg hal, if_true, mul_one, mul_zero, zero_add, endpointFactor]
      ring
    · simp [hal, ham, endpointFactor, Nat.ne_of_gt hp]

/-- The unified formula for an actual positively scaled tetrahedron. -/
theorem weighted_all_edge_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a l m : Vertex) (p : ℕ) (hp : 0 < p) (hlm : l ≠ m) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t a) p 0 z) t) =
      (meshScale N)⁻¹ * endpointFactor p a l m s *
        (∑ j : Coordinate, z j * faceEdgeGradient t.2 r l m j) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  simp only [weightedFaceField_self_rescale, pow_zero, mul_one,
    rescaled_derivative_edge hN, endpoint_face_edge_derivative t.2 (cellOrigin t.1) r a l m p hp hlm s]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FreudenthalSVLean.UniversalFaceEdgeTrace
