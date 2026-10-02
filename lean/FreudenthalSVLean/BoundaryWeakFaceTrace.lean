import FreudenthalSVLean.WeakFaceGauss
import FreudenthalSVLean.ActualFaceConformity

/-!
# Actual mesh boundary faces have zero weak H1_0 trace

For the boundary-face step in manuscript Lemma `means`, an omitted
active-face condition means exactly that all three face nodes lie in a
lower or upper cube coordinate plane.  Their actual barycentric affine
face chart stays in that plane, and thus outside the open cube.  The
proved smooth-closure trace theorem gives zero for every H1_0 function.
The implication holds on every positive mesh size and at every boundary
location without a boundary-state enumeration or an assumed trace rule.
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakFaceGauss

noncomputable section

namespace FreudenthalSVLean.BoundaryWeakFaceTrace

set_option backward.isDefEq.respectTransparency false

theorem scaledFaceChart_coordinate_flat (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) (j : Fin 3) (c : ℝ)
    (hc : ∀ a : Fin 4, a ≠ r → scaledVertex σ o h a j = c)
    (p : TriangleBernsteinIntegral.FacePoint) : scaledFaceChart σ o h r p j = c := by
  change h * (∑ a : Fin 4, faceBarycentric r p a * chainVertex σ o a j) = c
  calc
    _ = ∑ a : Fin 4, faceBarycentric r p a * scaledVertex σ o h a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change h * (faceBarycentric r p a * chainVertex σ o a j) =
        faceBarycentric r p a * (h * chainVertex σ o a j)
      ring
    _ = ∑ a : Fin 4, faceBarycentric r p a * c := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = r
      · subst a
        simp [faceBarycentric]
      · rw [hc a ha]
    _ = (∑ a : Fin 4, faceBarycentric r p a) * c := by rw [Finset.sum_mul]
    _ = c := by rw [faceBarycentric_sum, one_mul]

theorem vertex_coordinate_grid {N : ℕ} (t : Tet N) (a : Fin 4) (j : Fin 3) :
    vertex t a j = meshScale N * (integerGrid (gridVertexOfTet t a) j : ℝ) := by
  have he := congrFun (gridVertex_intPoint t a) j
  simp only [GridNodalSupport.intPoint] at he
  simp only [vertex, scaledVertex, Pi.smul_apply, smul_eq_mul, he]

theorem inactive_gridFace_outside_openCube {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : ¬ activeGridFace t r) (p : TriangleBernsteinIntegral.FacePoint) :
    scaledFaceChart t.2 (cellOrigin t.1) (meshScale N) r p ∉ openCube := by
  obtain ⟨j, hj⟩ := not_forall.mp ha
  rcases not_and_or.mp hj with hlow | hupp
  · have hv (a : Fin 4) (har : a ≠ r) : vertex t a j = 0 := by
      have hm : gridVertexOfTet t a ∈ gridFace t r :=
        Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨har, Finset.mem_univ _⟩, rfl⟩
      have he : integerGrid (gridVertexOfTet t a) j = 0 := by
        by_contra hn
        exact hlow ⟨gridVertexOfTet t a, hm, hn⟩
      rw [vertex_coordinate_grid, he, Int.cast_zero, mul_zero]
    have he := scaledFaceChart_coordinate_flat t.2 (cellOrigin t.1) (meshScale N) r j 0 hv p
    intro hp
    have hcoord := ((mem_openCube _).mp hp j).1
    rw [he] at hcoord
    exact lt_irrefl _ hcoord
  · have hv (a : Fin 4) (har : a ≠ r) : vertex t a j = 1 := by
      have hm : gridVertexOfTet t a ∈ gridFace t r :=
        Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨har, Finset.mem_univ _⟩, rfl⟩
      have he : integerGrid (gridVertexOfTet t a) j = (N : ℤ) := by
        by_contra hn
        exact hupp ⟨gridVertexOfTet t a, hm, hn⟩
      rw [vertex_coordinate_grid, he, Int.cast_natCast]
      simp [meshScale, (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')]
    have he := scaledFaceChart_coordinate_flat t.2 (cellOrigin t.1) (meshScale N) r j 1 hv p
    intro hp
    have hcoord := ((mem_openCube _).mp hp j).2
    rw [he] at hcoord
    exact lt_irrefl _ hcoord

theorem inactive_gridFace_weak_trace_zero {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : ¬ activeGridFace t r) {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) {T : FaceL2}
    (hT : HasH1FaceTrace f g t.2 (cellOrigin t.1) (meshScale N) r T) : T = 0 :=
  inH1ZeroCube_boundary_trace_zero hf t.2 (cellOrigin t.1) (meshScale N) r hT
    (fun p _ => inactive_gridFace_outside_openCube hN t r ha p)

end FreudenthalSVLean.BoundaryWeakFaceTrace
