import FreudenthalSVLean.ConformingFaceModes

/-!
# Complete endpoint and middle face-bubble edge traces

For manuscript equations `endpoint-bubble-first`, `endpoint-bubble-second`,
and `middle-face-bubble`, the product rule gives the target trace.  A
repeated missing endpoint or two missing simple factors prove zero trace
on every other edge.  The combinatorial argument uses unordered pairs
of vertices and applies to any tetrahedron, without listing edge types.
The actual conforming weighted face fields are then identified with
these spatial polynomials at positive mesh scale.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.EdgeBubble

noncomputable section

namespace FreudenthalSVLean.FaceModeTraces

theorem pair_eq_of_members {I : Type*} [DecidableEq I] (a b l m : I)
    (hab : a ≠ b) (hlm : l ≠ m) (ha : a ∈ ({l, m} : Finset I))
    (hb : b ∈ ({l, m} : Finset I)) : ({a, b} : Finset I) = {l, m} := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  · simp [hab, hlm]

theorem other_pairs_missing {I : Type*} [DecidableEq I] (a b c l m : I)
    (hab : a ≠ b) (hac : a ≠ c) (hlm : l ≠ m)
    (hb : ({a, b} : Finset I) ≠ {l, m}) (hc : ({a, c} : Finset I) ≠ {l, m}) :
    (a ≠ l ∧ a ≠ m) ∨ ((b ≠ l ∧ b ≠ m) ∧ (c ≠ l ∧ c ≠ m)) := by
  by_cases ha : a ∈ ({l, m} : Finset I)
  · right
    have hnb : b ∉ ({l, m} : Finset I) := fun h => hb (pair_eq_of_members a b l m hab hlm ha h)
    have hnc : c ∉ ({l, m} : Finset I) := fun h => hc (pair_eq_of_members a c l m hac hlm ha h)
    exact ⟨by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnb,
      by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnc⟩
  · left
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha

theorem endpointBubble_other_edge {R : Type*} [CommRing R]
    (σ : Equiv.Perm Coordinate) (o : Coordinate → R) (r : ℕ) (hr : 2 ≤ r)
    (a b c l m : Vertex) (hab : a ≠ b) (hac : a ≠ c) (hlm : l ≠ m)
    (hb : ({a, b} : Finset Vertex) ≠ {l, m}) (hc : ({a, c} : Finset Vertex) ≠ {l, m})
    (s : R) (j : Coordinate) :
    eval (segmentPoint (chainVertex σ o l) (chainVertex σ o m) s)
      (pderiv j (endpointBubble σ o r a b c)) = 0 := by
  rcases other_pairs_missing a b c l m hab hac hlm hb hc with ha | ⟨hb, hc⟩
  · apply pderiv_endpointBubble_zero_of_a_zero σ o _ r hr a b c j
    simp [barycentric_edge, ha.1, ha.2]
  · apply pderiv_endpointBubble_zero_of_b_c_zero σ o _ r a b c j
    · simp [barycentric_edge, hb.1, hb.2]
    · simp [barycentric_edge, hc.1, hc.2]

theorem middleBubble_other_edge {R : Type*} [CommRing R]
    (σ : Equiv.Perm Coordinate) (o : Coordinate → R) (a b c l m : Vertex)
    (hab : a ≠ b) (hlm : l ≠ m) (he : ({a, b} : Finset Vertex) ≠ {l, m})
    (s : R) (j : Coordinate) :
    eval (segmentPoint (chainVertex σ o l) (chainVertex σ o m) s)
      (pderiv j (middleBubble σ o a b c)) = 0 := by
  apply pderiv_middleBubble_zero_of_endpoint_zero
  by_cases ha : a ∈ ({l, m} : Finset Vertex)
  · right
    have hb : b ∉ ({l, m} : Finset Vertex) := fun h => he (pair_eq_of_members a b l m hab hlm ha h)
    have hb' : b ≠ l ∧ b ≠ m := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb
    simp [barycentric_edge, hb'.1, hb'.2]
  · left
    have ha' : a ≠ l ∧ a ≠ m := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha
    simp [barycentric_edge, ha'.1, ha'.2]

theorem complement_three (r a b c : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Finset.univ.erase r : Finset Vertex) = {a, b, c} := by
  have hs : ({a, b, c} : Finset Vertex) ⊆ Finset.univ.erase r := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp [har, hbr, hcr]
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  simp [hab, hac, hbc]

theorem spatialFaceBubble_three (σ : Equiv.Perm Coordinate) (o : Space)
    (r a b c : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    spatialFaceBubble σ o r = ChainGeometry.barycentric σ o a *
      ChainGeometry.barycentric σ o b * ChainGeometry.barycentric σ o c := by
  rw [spatialFaceBubble_eq_product, complement_three r a b c har hbr hcr hab hac hbc]
  simp [hab, hac, hbc, mul_assoc]

theorem weighted_endpoint_piece {N : ℕ} (t : Tet N) (r a b c : Vertex) (p : ℕ)
    (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (j : Coordinate) :
    weightedFaceField N t r (gridVertexOfTet t a) (gridVertexOfTet t b) p 0 z t j =
      rescale (meshScale N) (z j) (endpointBubble t.2 (cellOrigin t.1) (p + 1) a b c) := by
  rw [weightedFaceField_self_rescale]
  apply congrArg (rescale (meshScale N) (z j))
  rw [spatialFaceBubble_three t.2 (cellOrigin t.1) r a b c har hbr hcr hab hac hbc]
  simp only [pow_zero, mul_one, endpointBubble, pow_succ]
  ring

theorem weighted_middle_piece {N : ℕ} (t : Tet N) (r a b c : Vertex)
    (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (j : Coordinate) :
    weightedFaceField N t r (gridVertexOfTet t a) (gridVertexOfTet t b) 1 1 z t j =
      rescale (meshScale N) (z j) (middleBubble t.2 (cellOrigin t.1) a b c) := by
  rw [weightedFaceField_self_rescale]
  apply congrArg (rescale (meshScale N) (z j))
  rw [spatialFaceBubble_three t.2 (cellOrigin t.1) r a b c har hbr hcr hab hac hbc]
  simp only [pow_one, middleBubble]
  ring

theorem scaled_segment_inverse {N : ℕ} (hN : 0 < N) (t : Tet N) (a b : Vertex) (s : ℝ) :
    (meshScale N)⁻¹ • segmentPoint (vertex t a) (vertex t b) s =
      segmentPoint (chainVertex t.2 (cellOrigin t.1) a) (chainVertex t.2 (cellOrigin t.1) b) s := by
  funext j
  simp only [segmentPoint, vertex, scaledVertex, Pi.smul_apply, smul_eq_mul]
  field_simp [(meshScale_pos N hN).ne']

theorem rescaled_derivative_edge {N : ℕ} (hN : 0 < N) (t : Tet N) (a b : Vertex)
    (s c : ℝ) (P : MvPolynomial Coordinate ℝ) (i : Coordinate) :
    eval (segmentPoint (vertex t a) (vertex t b) s) (pderiv i (rescale (meshScale N) c P)) =
      c * (meshScale N)⁻¹ *
        eval (segmentPoint (chainVertex t.2 (cellOrigin t.1) a)
          (chainVertex t.2 (cellOrigin t.1) b) s) (pderiv i P) := by
  rw [pderiv_rescale, rescale_eval, scaled_segment_inverse hN]

theorem weighted_endpoint_edge_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (p : ℕ) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ) (i j : Coordinate) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (pderiv i (weightedFaceField N t r (gridVertexOfTet t a) (gridVertexOfTet t b) p 0 z t j)) =
        z j * (meshScale N)⁻¹ * ((1 - s) ^ (p + 1) * s * barycentricGradient t.2 c i) := by
  rw [weighted_endpoint_piece t r a b c p har hbr hcr hab hac hbc,
    rescaled_derivative_edge hN, pderiv_endpointBubble_edge _ _ _ _ _ _ _ _ hab hac hbc]

theorem weighted_middle_edge_derivative {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r a b c : Vertex) (har : a ≠ r) (hbr : b ≠ r) (hcr : c ≠ r)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (z : Space) (s : ℝ) (i j : Coordinate) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (pderiv i (weightedFaceField N t r (gridVertexOfTet t a) (gridVertexOfTet t b) 1 1 z t j)) =
        z j * (meshScale N)⁻¹ * ((1 - s) ^ 2 * s ^ 2 * barycentricGradient t.2 c i) := by
  rw [weighted_middle_piece t r a b c har hbr hcr hab hac hbc,
    rescaled_derivative_edge hN, pderiv_middleBubble_edge _ _ _ _ _ _ _ hab hac hbc]

end FreudenthalSVLean.FaceModeTraces
