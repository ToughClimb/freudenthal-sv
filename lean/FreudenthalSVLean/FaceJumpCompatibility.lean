import FreudenthalSVLean.ConformingEdgeJets
import FreudenthalSVLean.ActualVertexStarGraph

/-!
# Face jumps derived from actual conformity

For manuscript equation `edge-checkerboard` and the source-incidence
relations in Lemma `edge-star`, continuity across a shared triangular face
forces each scalar gradient jump to be a multiple of the omitted
barycentric gradient.  The proof uses common polynomial traces on the
segments from an arbitrary common point to the three face vertices and
the differentiated affine coordinate reconstruction.  Thus it also
applies at an edge or vertex, without assuming two-sided differentiability
of a piecewise polynomial.

The conormal intersection lemma below gives the algebraic implication
needed by the four-sector checkerboard relation.  Identification of the
actual seven geometric edge stars is a separate obligation.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.MeshSegments
open FreudenthalSVLean.EdgeJetContinuity
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.FaceJumpCompatibility

theorem shared_face_vertex_mem {N : ℕ} (hN : 0 < N) (t u : Tet N) (r s a : Vertex)
    (he : gridFace t r = gridFace u s) (ha : a ≠ r) : vertex t a ∈ tetrahedron u := by
  have hm : gridVertexOfTet t a ∈ gridFace u s := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hm
  have hp : vertex t a = vertex u b := by
    rw [← gridVertexOfTet_point, ← gridVertexOfTet_point, hb]
  rw [hp]
  exact vertex_mem_tetrahedron hN u b

theorem shared_face_jet_common {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t u : Tet N) (r s a : Vertex) (he : gridFace t r = gridFace u s) (ha : a ≠ r)
    (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) (j : Coordinate) :
    directionalJet x (vertex t a) (v.val t j) = directionalJet x (vertex t a) (v.val u j) := by
  apply directionalJet_eq_of_trace_eq
  intro q hq
  exact v.property.2.1 t u _
    (tetrahedron_segment_mem t x _ ht (vertex_mem_tetrahedron hN t a) q hq)
    (tetrahedron_segment_mem u x _ hu (shared_face_vertex_mem hN t u r s a he ha) q hq) j

theorem scaled_vertex_gradient_duality {N : ℕ} (hN : 0 < N) (t : Tet N) (i j : Coordinate) :
    (∑ a : Vertex, vertex t a j * ((meshScale N)⁻¹ * barycentricGradient t.2 a i)) =
      if j = i then 1 else 0 := by
  calc
    _ = ∑ a : Vertex, chainVertex t.2 (cellOrigin t.1) a j * barycentricGradient t.2 a i := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [vertex, scaledVertex, Pi.smul_apply, smul_eq_mul]
      field_simp [(meshScale_pos N hN).ne']
    _ = _ := VertexJetAlgebra.vertex_gradient_duality t.2 (cellOrigin t.1) j i

theorem shifted_vertex_gradient_duality {N : ℕ} (hN : 0 < N) (t : Tet N)
    (x : Space) (i j : Coordinate) :
    (∑ a : Vertex, (vertex t a j - x j) * ((meshScale N)⁻¹ * barycentricGradient t.2 a i)) =
      if j = i then 1 else 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    barycentricGradient_sum, mul_zero, sub_zero]
  exact scaled_vertex_gradient_duality hN t i j

/-- The base point need not be a tetrahedron vertex. -/
theorem gradient_from_directional_jets {N : ℕ} (hN : 0 < N) (t : Tet N) (x : Space)
    (p : MvPolynomial Coordinate ℝ) (i : Coordinate) :
    (∑ a : Vertex, directionalJet x (vertex t a) p *
      ((meshScale N)⁻¹ * barycentricGradient t.2 a i)) = eval x (pderiv i p) := by
  simp only [directionalJet, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, shifted_vertex_gradient_duality hN]
  simp

theorem directionalJet_sub (x y : Space) (p q : MvPolynomial Coordinate ℝ) :
    directionalJet x y (p - q) = directionalJet x y p - directionalJet x y q := by
  simp only [directionalJet, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- Every component of the true physical gradient jump is conormal to
the shared face, including points on its edges. -/
theorem scalar_gradient_jump {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t u : Tet N) (r s : Vertex) (he : gridFace t r = gridFace u s)
    (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) (i j : Coordinate) :
    eval x (pderiv i (v.val t j)) - eval x (pderiv i (v.val u j)) =
      directionalJet x (vertex t r) (v.val t j - v.val u j) *
        ((meshScale N)⁻¹ * barycentricGradient t.2 r i) := by
  classical
  rw [← map_sub, ← map_sub]
  rw [← gradient_from_directional_jets hN t x (v.val t j - v.val u j) i]
  apply Finset.sum_eq_single r
  · intro a _ ha
    rw [directionalJet_sub, shared_face_jet_common hN v t u r s a he ha x ht hu j,
      sub_self, zero_mul]
  · simp

/-- Two independent conormals have zero intersection.  Independence is
expressed by one nonzero two-coordinate minor, so no matrix-rank oracle
is part of this implication. -/
theorem conormal_intersection_zero (w n m : Space) (c d : ℝ) (i j : Coordinate)
    (hn : ∀ l, w l = c * n l) (hm : ∀ l, w l = d * m l)
    (hminor : n i * m j - n j * m i ≠ 0) : w = 0 := by
  have he : c * (n i * m j - n j * m i) = 0 := by
    calc
      _ = w i * m j - w j * m i := by rw [hn i, hn j]; ring
      _ = 0 := by rw [hm i, hm j]; ring
  have hc : c = 0 := (mul_eq_zero.mp he).resolve_right hminor
  funext l
  simp only [hn l, hc, zero_mul, Pi.zero_apply]

end FreudenthalSVLean.FaceJumpCompatibility
