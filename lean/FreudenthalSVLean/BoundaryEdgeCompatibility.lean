import FreudenthalSVLean.FaceJumpCompatibility

/-!
# Boundary-face gradients and equal-pair compatibility

For the boundary cases of manuscript Lemma `edge-star`, zero physical
boundary trace forces the scalar gradient to be conormal to a boundary
face.  Coordinate-plane geometry is recovered from the actual vertex
coordinates and affine gradient duality.  Thus two tetrahedra with the
same boundary plane and a transverse shared-face conormal have equal
gradients, and hence equal divergence traces, at every common boundary
point.  This proves the analytic implication used for boundary face
diagonals; identification of their mesh incidences is separate.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshSegments
open FreudenthalSVLean.EdgeJetContinuity
open FreudenthalSVLean.ConformingEdgeJets
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.FaceJumpCompatibility

noncomputable section

namespace FreudenthalSVLean.BoundaryEdgeCompatibility

theorem boundary_face_jet_zero {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t : Tet N) (r a : Vertex) (ha : a ≠ r) (l : Coordinate) (R : ℝ)
    (hR : R = 0 ∨ R = 1) (hv : ∀ b : Vertex, b ≠ r → vertex t b l = R)
    (x : Space) (ht : x ∈ tetrahedron t) (hx : x l = R) (j : Coordinate) :
    directionalJet x (vertex t a) (v.val t j) = 0 := by
  apply directionalJet_zero_of_trace_zero
  intro s hs
  exact v.property.2.2 t _
    (tetrahedron_segment_mem t x _ ht (vertex_mem_tetrahedron hN t a) s hs)
    (boundary_plane_segment_mem x (vertex t a)
      (tetrahedron_subset_cube hN t ht)
      (tetrahedron_subset_cube hN t (vertex_mem_tetrahedron hN t a))
      l R hR hx (hv a ha) s hs) j

theorem boundary_face_gradient {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t : Tet N) (r : Vertex) (l : Coordinate) (R : ℝ)
    (hR : R = 0 ∨ R = 1) (hv : ∀ b : Vertex, b ≠ r → vertex t b l = R)
    (x : Space) (ht : x ∈ tetrahedron t) (hx : x l = R) (i j : Coordinate) :
    eval x (pderiv i (v.val t j)) =
      directionalJet x (vertex t r) (v.val t j) *
        ((meshScale N)⁻¹ * barycentricGradient t.2 r i) := by
  classical
  rw [← gradient_from_directional_jets hN t x (v.val t j) i]
  apply Finset.sum_eq_single r
  · intro a _ ha
    rw [boundary_face_jet_zero hN v t r a ha l R hR hv x ht hx j, zero_mul]
  · simp

/-- The three constant face coordinates determine the actual conormal;
no separately supplied normal formula is used. -/
theorem coordinate_face_gradient {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r : Vertex) (l : Coordinate) (R : ℝ)
    (hv : ∀ b : Vertex, b ≠ r → vertex t b l = R) :
    ∀ i : Coordinate, i ≠ l → barycentricGradient t.2 r i = (0 : ℝ) := by
  classical
  let A := (vertex t r l - R) * (meshScale N)⁻¹
  have he (i : Coordinate) : A * barycentricGradient t.2 r i = if l = i then 1 else 0 := by
    calc
      _ = ∑ a : Vertex, (vertex t a l - R) *
          ((meshScale N)⁻¹ * barycentricGradient t.2 a i) := by
        rw [Finset.sum_eq_single r]
        · dsimp [A]
          ring
        · intro a _ ha
          rw [hv a ha, sub_self, zero_mul]
        · simp
      _ = _ := shifted_vertex_gradient_duality hN t (fun _ => R) i l
  have hA : A ≠ 0 := by
    intro h
    have h1 := he l
    simp only [h, zero_mul] at h1
    exact zero_ne_one h1
  intro i hi
  have hz : A * barycentricGradient t.2 r i = 0 := by
    simpa only [if_neg (Ne.symm hi)] using he i
  exact (mul_eq_zero.mp hz).resolve_left hA

theorem boundary_face_tangential_gradient_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (r : Vertex) (l : Coordinate) (R : ℝ)
    (hR : R = 0 ∨ R = 1) (hv : ∀ b : Vertex, b ≠ r → vertex t b l = R)
    (x : Space) (ht : x ∈ tetrahedron t) (hx : x l = R)
    (i j : Coordinate) (hi : i ≠ l) : eval x (pderiv i (v.val t j)) = 0 := by
  rw [boundary_face_gradient hN v t r l R hR hv x ht hx i j,
    coordinate_face_gradient hN t r l R hv i hi, mul_zero, mul_zero]

/-- Boundary equal-pair compatibility at any common point.  The two
boundary faces lie in the same coordinate plane; one nonzero tangential
component of the shared-face conormal establishes transversality. -/
theorem equal_pair_gradient {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t u : Tet N) (r s rt ru : Vertex) (he : gridFace t r = gridFace u s)
    (l i : Coordinate) (hi : i ≠ l)
    (hn : barycentricGradient (R := ℝ) t.2 r i ≠ 0) (R : ℝ) (hR : R = 0 ∨ R = 1)
    (hvt : ∀ b : Vertex, b ≠ rt → vertex t b l = R)
    (hvu : ∀ b : Vertex, b ≠ ru → vertex u b l = R)
    (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) (hx : x l = R)
    (a j : Coordinate) : eval x (pderiv a (v.val t j)) = eval x (pderiv a (v.val u j)) := by
  have ht0 := boundary_face_tangential_gradient_zero hN v t rt l R hR hvt x ht hx i j hi
  have hu0 := boundary_face_tangential_gradient_zero hN v u ru l R hR hvu x hu hx i j hi
  have hj := scalar_gradient_jump hN v t u r s he x ht hu i j
  rw [ht0, hu0, sub_self] at hj
  have hnon : (meshScale N)⁻¹ * barycentricGradient t.2 r i ≠ 0 :=
    mul_ne_zero (inv_ne_zero (meshScale_pos N hN).ne') hn
  have hjet : directionalJet x (vertex t r) (v.val t j - v.val u j) = 0 :=
    (mul_eq_zero.mp hj.symm).resolve_right hnon
  have hjall := scalar_gradient_jump hN v t u r s he x ht hu a j
  rw [hjet, zero_mul] at hjall
  exact sub_eq_zero.mp hjall

theorem equal_pair_divergence {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t u : Tet N) (r s rt ru : Vertex) (he : gridFace t r = gridFace u s)
    (l i : Coordinate) (hi : i ≠ l)
    (hn : barycentricGradient (R := ℝ) t.2 r i ≠ 0) (R : ℝ) (hR : R = 0 ∨ R = 1)
    (hvt : ∀ b : Vertex, b ≠ rt → vertex t b l = R)
    (hvu : ∀ b : Vertex, b ≠ ru → vertex u b l = R)
    (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) (hx : x l = R) :
    eval x (divergence N v.val t) = eval x (divergence N v.val u) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact equal_pair_gradient hN v t u r s rt ru he l i hi hn R hR hvt hvu x ht hu hx j j

/-- At the intersection of two boundary faces with independent conormals,
the full velocity gradient vanishes.  This is the implication for the
one-tetrahedron box-edge source row of manuscript Lemma `edge-star`. -/
theorem two_boundary_faces_derivative_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (r s : Vertex) (l m : Coordinate)
    (R S : ℝ) (hR : R = 0 ∨ R = 1) (hS : S = 0 ∨ S = 1)
    (hvr : ∀ b : Vertex, b ≠ r → vertex t b l = R)
    (hvs : ∀ b : Vertex, b ≠ s → vertex t b m = S)
    (i j : Coordinate)
    (hminor : barycentricGradient (R := ℝ) t.2 r i * barycentricGradient t.2 s j -
      barycentricGradient t.2 r j * barycentricGradient t.2 s i ≠ 0)
    (x : Space) (ht : x ∈ tetrahedron t) (hx : x l = R) (hy : x m = S)
    (a b : Coordinate) : eval x (pderiv a (v.val t b)) = 0 := by
  have hz : (fun c : Coordinate => eval x (pderiv c (v.val t b))) = 0 := by
    apply conormal_intersection_zero _ (barycentricGradient t.2 r)
      (barycentricGradient t.2 s)
      (directionalJet x (vertex t r) (v.val t b) * (meshScale N)⁻¹)
      (directionalJet x (vertex t s) (v.val t b) * (meshScale N)⁻¹) i j
    · intro c
      rw [boundary_face_gradient hN v t r l R hR hvr x ht hx c b]
      ring
    · intro c
      rw [boundary_face_gradient hN v t s m S hS hvs x ht hy c b]
      ring
    · exact hminor
  exact congrFun hz a

theorem two_boundary_faces_divergence_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (r s : Vertex) (l m : Coordinate)
    (R S : ℝ) (hR : R = 0 ∨ R = 1) (hS : S = 0 ∨ S = 1)
    (hvr : ∀ b : Vertex, b ≠ r → vertex t b l = R)
    (hvs : ∀ b : Vertex, b ≠ s → vertex t b m = S)
    (i j : Coordinate)
    (hminor : barycentricGradient (R := ℝ) t.2 r i * barycentricGradient t.2 s j -
      barycentricGradient t.2 r j * barycentricGradient t.2 s i ≠ 0)
    (x : Space) (ht : x ∈ tetrahedron t) (hx : x l = R) (hy : x m = S) :
    eval x (divergence N v.val t) = 0 := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    two_boundary_faces_derivative_zero hN v t r s l m R S hR hS hvr hvs
      i j hminor x ht hx hy, Finset.sum_const_zero]

end FreudenthalSVLean.BoundaryEdgeCompatibility
