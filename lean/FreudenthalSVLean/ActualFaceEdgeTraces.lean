import FreudenthalSVLean.FaceModeTraces

/-!
# Physical edge traces of conforming face modes

This module proves the target and spill formulas in manuscript equations
`endpoint-bubble-first`, `endpoint-bubble-second`, and `middle-face-bubble`
for the globally conforming fields on the actual mesh.  In particular,
orthogonality to the second face-coordinate gradient removes the entire
spill trace, not merely its nodal values.  The middle mode protects every
other edge without an orthogonality condition.  Shared-face identities
identify the same field on its two owners.

The incidence-space spanning and the exceptional borrowed-face sum are
not consequences of the trace formulas alone.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.FaceModeTraces
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.EdgeBubble

noncomputable section

namespace FreudenthalSVLean.ActualFaceEdgeTraces

theorem weightedFaceField_shared {N : ℕ} (t u : Tet N) (r s : Vertex)
    (he : gridFace t r = gridFace u s) (a b : GridVertex N) (p q : ℕ) (z : Space) :
    weightedFaceField N t r a b p q z u = weightedFaceField N u s a b p q z u := by
  funext j
  simp only [weightedFaceField, faceScalar_shared t u r s he]

theorem endpointBubble_swap (σ : Equiv.Perm Coordinate) (o : Space)
    (r : ℕ) (a b c : Vertex) :
    endpointBubble σ o r a b c = endpointBubble σ o r a c b := by
  unfold endpointBubble
  ring

theorem weighted_endpoint_edge_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (p : ℕ) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) p 0 z) t) =
      (meshScale N)⁻¹ * ((1 - s) ^ (p + 1) * s) *
        (∑ j : Coordinate, z j * barycentricGradient t.2 c j) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    weighted_endpoint_edge_derivative hN t r a b c p har hbr hcr hab hac hbc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_middle_edge_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) 1 1 z) t) =
      (meshScale N)⁻¹ * ((1 - s) ^ 2 * s ^ 2) *
        (∑ j : Coordinate, z j * barycentricGradient t.2 c j) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    weighted_middle_edge_derivative hN t r a b c har hbr hcr hab hac hbc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_endpoint_spill_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (p : ℕ) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ)
    (i j : Coordinate) :
    eval (segmentPoint (vertex t a) (vertex t c) s)
      (pderiv i (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) p 0 z t j)) =
      z j * (meshScale N)⁻¹ * ((1 - s) ^ (p + 1) * s * barycentricGradient t.2 b i) := by
  rw [weighted_endpoint_piece t r a b c p har hbr hcr hab hac hbc,
    endpointBubble_swap, rescaled_derivative_edge hN,
    pderiv_endpointBubble_edge _ _ _ _ _ _ _ _ hac hab (Ne.symm hbc)]

theorem weighted_endpoint_spill_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (p : ℕ) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t c) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) p 0 z) t) =
      (meshScale N)⁻¹ * ((1 - s) ^ (p + 1) * s) *
        (∑ j : Coordinate, z j * barycentricGradient t.2 b j) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    weighted_endpoint_spill_derivative hN t r a b c p har hbr hcr hab hac hbc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weighted_endpoint_other_edge_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c l m : Vertex) (p : ℕ) (hp : 2 ≤ p + 1)
    (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hlm : l ≠ m)
    (hb : ({a, b} : Finset Vertex) ≠ {l, m})
    (hc : ({a, c} : Finset Vertex) ≠ {l, m}) (z : Space) (s : ℝ)
    (i j : Coordinate) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
      (pderiv i (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) p 0 z t j)) = 0 := by
  rw [weighted_endpoint_piece t r a b c p har hbr hcr hab hac hbc,
    rescaled_derivative_edge hN,
    endpointBubble_other_edge _ _ _ hp a b c l m hab hac hlm hb hc, mul_zero]

theorem weighted_middle_other_edge_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c l m : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hlm : l ≠ m)
    (he : ({a, b} : Finset Vertex) ≠ {l, m}) (z : Space) (s : ℝ)
    (i j : Coordinate) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
      (pderiv i (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) 1 1 z t j)) = 0 := by
  rw [weighted_middle_piece t r a b c har hbr hcr hab hac hbc,
    rescaled_derivative_edge hN, middleBubble_other_edge _ _ a b c l m hab hlm he, mul_zero]

theorem weighted_endpoint_other_edge_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c l m : Vertex) (p : ℕ) (hp : 2 ≤ p + 1)
    (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hlm : l ≠ m)
    (hb : ({a, b} : Finset Vertex) ≠ {l, m})
    (hc : ({a, c} : Finset Vertex) ≠ {l, m}) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) p 0 z) t) = 0 := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    weighted_endpoint_other_edge_derivative hN t r a b c l m p hp
      har hbr hcr hab hac hbc hlm hb hc, Finset.sum_const_zero]

theorem weighted_middle_other_edge_divergence {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c l m : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hlm : l ≠ m)
    (he : ({a, b} : Finset Vertex) ≠ {l, m}) (z : Space) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (weightedFaceField N t r (gridVertexOfTet t a)
        (gridVertexOfTet t b) 1 1 z) t) = 0 := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    weighted_middle_other_edge_derivative hN t r a b c l m
      har hbr hcr hab hac hbc hlm he, Finset.sum_const_zero]

end FreudenthalSVLean.ActualFaceEdgeTraces
