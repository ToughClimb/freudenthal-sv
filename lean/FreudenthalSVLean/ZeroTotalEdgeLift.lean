import FreudenthalSVLean.UniformEdgeLift
import FreudenthalSVLean.CanonicalLiftMean
import FreudenthalSVLean.EdgeAssemblyGeometry

/-!
# Uniform actual edge lifts with proved zero-total-mean compatibility

For manuscript Proposition `edge` and Lemma `routing`, both degree-specific
canonical lifts, transported to every actual increasing mesh edge, satisfy
the exact zero-total-mean identity needed by the local macro router.
The operator and its geometry are fixed before the pressure input.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.CanonicalEdgeOrientation
open FreudenthalSVLean.CubePolynomialTransport
open FreudenthalSVLean.UniformEdgeLift
open FreudenthalSVLean.CanonicalLiftMean
open FreudenthalSVLean.DivergenceMean
open FreudenthalSVLean.EdgeAssemblyGeometry

noncomputable section

namespace FreudenthalSVLean.ZeroTotalEdgeLift

set_option backward.isDefEq.respectTransparency false

theorem transportedQuartic_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (c : Fin 7) (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) (q : vertexZeroSpace N 4) :
    totalMean hN (transportedQuartic hN a b c π flip hd hl q).val = 0 := by
  change totalMean hN (pushVelocity π.symm flip
    (quarticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
      (CubeTraceTransport.zeroPressureMap hN π flip q)).val) = 0
  rw [totalMean_pushVelocity, quarticMap_totalMean_zero]

theorem transportedQuintic_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (c : Fin 7) (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) (q : vertexZeroSpace N 5) :
    totalMean hN (transportedQuintic hN a b c π flip hd hl q).val = 0 := by
  change totalMean hN (pushVelocity π.symm flip
    (quinticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
      (CubeTraceTransport.zeroPressureMap hN π flip q)).val) = 0
  rw [totalMean_pushVelocity, quinticMap_totalMean_zero]

/-- Both exact mean-compatibility and the full trace/support/energy
specification hold on every actual mesh edge, including boundary edges. -/
theorem uniform_zero_total_edge_lifts : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (e : MeshEdge N),
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        EdgeLiftSpec e.val.1 e.val.2 R₄ C ∧ EdgeLiftSpec e.val.1 e.val.2 R₅ C ∧
          (∀ q, totalMean hN (R₄ q).val = 0) ∧ (∀ q, totalMean hN (R₅ q).val = 0) := by
  obtain ⟨C, hC, hbound⟩ := canonical_pressure_energy
  refine ⟨C, hC, ?_⟩
  intro N hN e
  obtain ⟨π, flip, hdir, hl⟩ := actual_canonical_orientation hN e.val.1 e.val.2
    (edgeDirection e) (edgeDirection_eq e)
  let c := incidenceKind (boundaryTag e.val.1) (edgeDirection e)
  have hb := hbound N hN (firstNode π flip e.val.1 e.val.2)
    (secondNode π flip e.val.1 e.val.2) c hdir hl
  refine ⟨transportedQuartic hN e.val.1 e.val.2 c π flip hdir hl,
    transportedQuintic hN e.val.1 e.val.2 c π flip hdir hl,
    transportedQuartic_spec hN e.val.1 e.val.2 c π flip hdir hl C hb.1,
    transportedQuintic_spec hN e.val.1 e.val.2 c π flip hdir hl C hb.2, ?_, ?_⟩
  · exact transportedQuartic_totalMean_zero hN e.val.1 e.val.2 c π flip hdir hl
  · exact transportedQuintic_totalMean_zero hN e.val.1 e.val.2 c π flip hdir hl

end FreudenthalSVLean.ZeroTotalEdgeLift
