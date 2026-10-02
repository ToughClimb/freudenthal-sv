import FreudenthalSVLean.ActualFaceConformity

/-!
# Actual paired means and vertex protection of conforming face transfers

For manuscript equation `vertex-face-transfer`, the global three-node
field is identified with the genuine scaled face polynomial on each owner.
Its divergence mean is computed from actual Lebesgue integration.  The
proved opposite omitted-vertex gradients give opposite means on the two
owners.  All vertex derivatives are zero, so routing these means does not
change any vertex-divergence row.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexStarGraphTransport
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity

noncomputable section

namespace FreudenthalSVLean.ActualFaceMean

theorem starCatalog_perm {N : ℕ} {n : GridVertex N} (ta : VertexStar n) :
    MeshCoverage.orderPerm (starCatalog ta).1 = ta.val.1.2 := by
  exact congrArg Prod.fst (catalogEquiv.apply_symm_apply (ta.val.1.2, ta.val.2))

theorem gradient_int_cast (σ : Equiv.Perm Coordinate) (r : Vertex) (j : Coordinate) :
    ((ChainGeometry.barycentricGradient (R := ℤ) σ r j) : ℝ) =
      ChainGeometry.barycentricGradient (R := ℝ) σ r j := by
  fin_cases r <;> simp [ChainGeometry.barycentricGradient, ChainGeometry.coordinateUnit]

theorem actual_shared_gradients_opposite {N : ℕ} {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (j : Coordinate) :
    ChainGeometry.barycentricGradient (R := ℝ) ta.val.1.2 r j =
      -ChainGeometry.barycentricGradient (R := ℝ) tb.val.1.2 u j := by
  have hcat : catalogFace (starCatalog ta) r = catalogFace (starCatalog tb) u := by
    rw [← displaced_catalogFace, ← displaced_catalogFace, he]
  have hncat : starCatalog ta ≠ starCatalog tb := by
    intro h
    exact hne (congrArg (fun x : VertexStar n => x.val.1) (starCatalog_injective n h))
  have hg := shared_face_gradients_opposite (starCatalog ta) (starCatalog tb) r u hncat
    (by simpa only [starCatalog_cut] using hr)
    (by simpa only [starCatalog_cut] using hu) hcat j
  unfold catalogGradient at hg
  rw [starCatalog_perm, starCatalog_perm] at hg
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hg
  simpa only [Int.cast_neg, gradient_int_cast] using hc

theorem spatialFaceBubble_eq_product (σ : Equiv.Perm Coordinate) (o : Space) (r : Vertex) :
    spatialFaceBubble σ o r =
      ∏ a ∈ Finset.univ.erase r, ChainGeometry.barycentric σ o a := by
  rw [spatialFaceBubble, faceBarycentricPolynomial,
    LowDegreeBubbleExpansion.substitute_face_monomial]
  simp [ElementBubbleAlgebra.faceCubic]

theorem faceScalar_self_rescale {N : ℕ} (t : Tet N) (r : Vertex) :
    faceScalar t r t = rescale (meshScale N) 1 (spatialFaceBubble t.2 (cellOrigin t.1) r) := by
  rw [faceScalar_self, spatialFaceBubble_eq_product]
  simp only [rescale, C_1, one_mul, map_prod]
  rfl

theorem faceField_self_rescale {N : ℕ} (t : Tet N) (r : Vertex) (s : Space) (j : Coordinate) :
    faceField N t r s t j =
      rescale (meshScale N) 1 (C (s j) * spatialFaceBubble t.2 (cellOrigin t.1) r) := by
  rw [faceField, faceScalar_self_rescale]
  simp [rescale, map_mul]

theorem scaled_face_mean (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ) (hh : 0 < h)
    (r : Vertex) (s : Space) :
    (∫ x in scaledChainSet σ o h, eval x
      (PolynomialCalculus.polynomialDivergence (fun j =>
        rescale h 1 (C (s j) * spatialFaceBubble σ o r)))) =
      h ^ 2 * (-(∑ j : Coordinate, s j * ChainGeometry.barycentricGradient σ r j) / 120) := by
  rw [divergence_rescale]
  simp only [one_mul, rescale_eval]
  rw [integral_const_mul, scaled_chain_integral σ o h hh
    (fun y => eval y (PolynomialCalculus.polynomialDivergence
      (fun j => C (s j) * spatialFaceBubble σ o r))), spatialFaceBubble_vector_mean]
  field_simp [hh.ne']

theorem faceField_mean {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex) (s : Space) :
    (∫ x in tetrahedron t, eval x (divergence N (faceField N t r s) t)) =
      (meshScale N) ^ 2 *
        (-(∑ j : Coordinate, s j * ChainGeometry.barycentricGradient t.2 r j) / 120) := by
  have hf : (faceField N t r s t) = fun j =>
      rescale (meshScale N) 1 (C (s j) * spatialFaceBubble t.2 (cellOrigin t.1) r) := by
    funext j
    exact faceField_self_rescale t r s j
  change (∫ x in scaledChainSet t.2 (cellOrigin t.1) (meshScale N),
    eval x (PolynomialCalculus.polynomialDivergence (faceField N t r s t))) = _
  rw [hf]
  exact scaled_face_mean t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r s

theorem faceField_pderiv_vertex {N : ℕ} (hN : 0 < N) (t : Tet N) (r l : Vertex)
    (s : Space) (i j : Coordinate) :
    eval (vertex t l) (pderiv i (faceField N t r s t j)) = 0 := by
  rw [faceField_self_rescale, pderiv_rescale, rescale_eval, pderiv_C_mul, map_mul, eval_C]
  have he : (meshScale N)⁻¹ • vertex t l = chainVertex t.2 (cellOrigin t.1) l := by
    simp only [vertex, scaledVertex, smul_smul, inv_mul_cancel₀ (meshScale_pos N hN).ne',
      one_smul]
  rw [he, spatialFaceBubble_derivative_vertex]
  ring

def transferVector (N : ℕ) (t : Tet N) (r : Vertex) : Space :=
  fun j => (meshScale N)⁻¹ ^ 2 * unitTransferVector t.2 r j

def transferField (N : ℕ) (t : Tet N) (r : Vertex) : BrokenVelocity N :=
  faceField N t r (transferVector N t r)

theorem transfer_mean_one {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex) :
    (∫ x in tetrahedron t, eval x (divergence N (transferField N t r) t)) = 1 := by
  rw [transferField, faceField_mean hN]
  have hg : (-(∑ j : Coordinate, unitTransferVector t.2 r j *
      ChainGeometry.barycentricGradient t.2 r j) / 120) = 1 := by
    rw [← spatialFaceBubble_vector_mean t.2 (cellOrigin t.1) r]
    exact unitTransferVector_mean_one t.2 (cellOrigin t.1) r
  simp only [transferVector, mul_assoc, ← Finset.mul_sum]
  rw [← mul_neg, mul_div_assoc, hg]
  field_simp [(meshScale_pos N hN).ne']

theorem faceField_eq_of_shared_face {N : ℕ} (t v : Tet N) (r u : Vertex)
    (he : gridFace t r = gridFace v u) (s : Space) :
    faceField N t r s = faceField N v u s := by
  funext w j
  simp only [faceField, faceScalar, he]

theorem transfer_mean_minus_one {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u) :
    (∫ x in tetrahedron tb.val.1,
      eval x (divergence N (transferField N ta.val.1 r) tb.val.1)) = -1 := by
  have hp := transfer_mean_one hN ta.val.1 r
  rw [transferField, faceField_mean hN] at hp
  rw [transferField, faceField_eq_of_shared_face ta.val.1 tb.val.1 r u he,
    faceField_mean hN]
  have hg (j : Coordinate) :
      ChainGeometry.barycentricGradient (R := ℝ) tb.val.1.2 u j =
        -ChainGeometry.barycentricGradient (R := ℝ) ta.val.1.2 r j := by
    have h := actual_shared_gradients_opposite ta tb r u hr hu hne he j
    linarith
  simp only [hg, mul_neg, Finset.sum_neg_distrib, neg_neg]
  linarith

theorem transfer_zero_off_pair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (t : Tet N) (hta : t ≠ ta.val.1) (htb : t ≠ tb.val.1) (j : Coordinate) :
    transferField N ta.val.1 r t j = 0 :=
  faceField_zero_off_pair ta tb r u hr hne he (transferVector N ta.val.1 r) t hta htb j

theorem transfer_mean_off_pair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (t : Tet N) (hta : t ≠ ta.val.1) (htb : t ≠ tb.val.1) :
    (∫ x in tetrahedron t, eval x (divergence N (transferField N ta.val.1 r) t)) = 0 := by
  have hz : transferField N ta.val.1 r t = 0 := by
    funext j
    exact transfer_zero_off_pair ta tb r u hr hne he t hta htb j
  change (∫ x in tetrahedron t,
    eval x (∑ j : Coordinate, pderiv j (transferField N ta.val.1 r t j))) = 0
  simp only [hz, Pi.zero_apply, map_zero, Finset.sum_const_zero, integral_zero]

/-- The normalized transfer preserves every mesh vertex incidence,
including both owners' boundary vertices and all non-owner elements. -/
theorem transfer_protects_vertices {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i (transferField N ta.val.1 r t j)) = 0 := by
  by_cases hta : t = ta.val.1
  · subst t
    exact faceField_pderiv_vertex hN ta.val.1 r l (transferVector N ta.val.1 r) i j
  · by_cases htb : t = tb.val.1
    · subst t
      rw [transferField, faceField_eq_of_shared_face ta.val.1 tb.val.1 r u he]
      exact faceField_pderiv_vertex hN tb.val.1 u l (transferVector N ta.val.1 r) i j
    · rw [transfer_zero_off_pair ta tb r u hr hne he t hta htb j, map_zero, map_zero]

theorem transfer_mem_velocitySpace {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u) :
    transferField N ta.val.1 r ∈ velocitySpace N 3 :=
  faceField_mem_velocitySpace hN ta.val.1 r
    (shared_face_active hN ta tb r u hr hu hne he) (transferVector N ta.val.1 r)

end FreudenthalSVLean.ActualFaceMean
