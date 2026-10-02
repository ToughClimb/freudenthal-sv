import FreudenthalSVLean.BilinearFaceMean
import FreudenthalSVLean.MacroMeanTransfer
import FreudenthalSVLean.CubePolynomialTransport

/-!
# Total genuine divergence mean and its linear and transport identities

For manuscript Lemma `routing`, the required zero-sum compatibility is
expressed by a linear functional of actual element volume integrals.
The face-mode identities and coordinate symmetry transport proved here
allow its use for concrete edge lifts; no blanket divergence-theorem
claim for an arbitrary conforming field is assumed.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MacroMeanTransfer
open FreudenthalSVLean.CubeMeshSymmetry
open FreudenthalSVLean.CubePolynomialTransport

noncomputable section

namespace FreudenthalSVLean.DivergenceMean

def totalMean {N : ℕ} (hN : 0 < N) : BrokenVelocity N →ₗ[ℝ] ℝ :=
  ∑ t : Tet N, (tetIntegral hN t).comp ((LinearMap.proj t).comp (divergence N))

theorem totalMean_apply {N : ℕ} (hN : 0 < N) (v : BrokenVelocity N) :
    totalMean hN v = ∑ t : Tet N, tetIntegral hN t (divergence N v t) := by
  simp only [totalMean, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem elementMeans_sum {N : ℕ} (hN : 0 < N) (k : ℕ) (v : velocitySpace N k) :
    (∑ t : Tet N, elementMeans hN k v t) = totalMean hN v.val := by
  rw [totalMean_apply]
  rfl

theorem weightedFace_totalMean_zero {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (m : GridVertex N) (e : ℕ) (he : 0 < e) (z : Space) :
    totalMean hN (weightedFaceField N ta.val.1 r m m e 0 z) = 0 := by
  rw [totalMean_apply]
  exact WeightedFaceMean.weighted_face_total_mean_zero hN ta tb r u hr hu hne hf m e he z

theorem bilinearFace_totalMean_zero {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (a b : GridVertex N) (z : Space) :
    totalMean hN (weightedFaceField N ta.val.1 r a b 1 1 z) = 0 := by
  rw [totalMean_apply]
  exact BilinearFaceMean.weighted_two_face_total_mean_zero hN ta tb r u hr hu hne hf a b z

/-- True mean conservation by the actual coordinate/central-inversion
mesh symmetry.  The element labels form an equivalence on every `N`. -/
theorem totalMean_pushVelocity {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (flip : Bool) (v : BrokenVelocity N) :
    totalMean hN (pushVelocity π flip v) = totalMean hN v := by
  rw [totalMean_apply, totalMean_apply]
  change (∑ t : Tet N, ∫ x in tetrahedron t,
    MvPolynomial.eval x (divergence N (pushVelocity π flip v) t)) =
      ∑ t : Tet N, ∫ x in tetrahedron t, MvPolynomial.eval x (divergence N v t)
  simp only [pushVelocity_divergence_mean π flip v]
  exact (CubeMeshSymmetry.tetEquiv (N := N) π flip).symm.sum_comp
    (fun t : Tet N => ∫ x in tetrahedron t, MvPolynomial.eval x (divergence N v t))

end FreudenthalSVLean.DivergenceMean
