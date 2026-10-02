import FreudenthalSVLean.CubeTraceTransport

/-!
# Polynomial support of the canonical and transported edge lifts

For manuscript Lemma `edge-lift` and the bounded-overlap assembly,
canonical fields vanish identically on tetrahedra outside their first
endpoint's vertex star, including borrowed-face fields.  Multiplication
by an endpoint hat does not enlarge this support.  After physical cube
transport the support lies in one of the two original endpoint stars.
These are local polynomial identities, not just pointwise zero traces.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.ActualCanonicalEdgeLift
open FreudenthalSVLean.ConformingNodalMultiplication
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.CubeMeshSymmetry
open FreudenthalSVLean.CubePolynomialTransport
open FreudenthalSVLean.CanonicalEdgeOrientation
open FreudenthalSVLean.CubeTraceTransport

noncomputable section

namespace FreudenthalSVLean.CanonicalLiftSupport

set_option backward.isDefEq.respectTransparency false

theorem patternLinear_off_star {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    (patternLinear hN a b c hd hl side e hk w).val t = 0 := by
  rw [patternLinear_val]
  simp only [Finset.sum_apply, Pi.smul_apply,
    patternField_off_star hN a b c hd hl side _ e t ht, smul_zero, Finset.sum_const_zero]

theorem endpointLift_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    (endpointLift hN a b c hd hl side q).val t = 0 :=
  patternLinear_off_star hN a b c hd hl side 1 (by norm_num) _ t ht

theorem hatEndpointLift_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    (hatEndpointLift hN a b c hd hl side multiplier q).val t = 0 := by
  funext j
  change _ * (endpointLift hN a b c hd hl side q).val t j = 0
  rw [endpointLift_off_star hN a b c hd hl side q t ht]
  exact mul_zero _

theorem quarticMap_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 4) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    (quarticMap hN a b c hd hl q).val t = 0 := by
  change (endpointLift hN a b c hd hl false (quarticData hN a b c hd hl q).1).val t +
    (endpointLift hN a b c hd hl true (quarticData hN a b c hd hl q).2).val t = 0
  rw [endpointLift_off_star hN a b c hd hl _ _ t ht,
    endpointLift_off_star hN a b c hd hl _ _ t ht, add_zero]

theorem quinticMap_off_star {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 5) (t : Tet N)
    (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a) :
    (quinticMap hN a b c hd hl q).val t = 0 := by
  change (hatEndpointLift hN a b c hd hl false false (quinticData hN a b c hd hl q).1).val t +
    (hatEndpointLift hN a b c hd hl false true (quinticData hN a b c hd hl q).2.1).val t +
    (hatEndpointLift hN a b c hd hl true true (quinticData hN a b c hd hl q).2.2).val t = 0
  rw [hatEndpointLift_off_star hN a b c hd hl _ _ _ t ht,
    hatEndpointLift_off_star hN a b c hd hl _ _ _ t ht,
    hatEndpointLift_off_star hN a b c hd hl _ _ _ t ht, add_zero, add_zero]

theorem nodeMap_injective {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) :
    Function.Injective (nodeMap (N := N) π flip) := by
  intro a b he
  have hi := congrArg (nodeMap π.symm flip) he
  simpa only [nodeMap_inverse] using hi

theorem endpoint_star_transport {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) (v : BrokenVelocity N)
    (hv : ∀ t : Tet N, (∀ l : Vertex, gridVertexOfTet t l ≠ firstNode π flip a b) → v t = 0)
    (t : Tet N) (ht : ∀ l : Vertex, gridVertexOfTet t l ≠ a ∧ gridVertexOfTet t l ≠ b) :
    pushVelocity π.symm flip v t = 0 := by
  have hzero : v (tetMap π flip t) = 0 := by
    apply hv
    intro l he
    have hi : gridVertexOfTet t (transformVertex flip l) = (if flip then b else a) := by
      apply nodeMap_injective π flip
      rw [← tetMap_gridVertex, transformVertex_involutive]
      exact he
    cases flip
    · exact (ht (transformVertex false l)).1 hi
    · exact (ht (transformVertex true l)).2 hi
  funext j
  change C (orientationSign flip) * substitute π.symm flip
    (v ((tetEquiv π.symm flip).symm t) (π.symm.symm j)) = 0
  rw [tetEquiv_symm_apply, Equiv.symm_symm, hzero]
  simp [substitute]

end FreudenthalSVLean.CanonicalLiftSupport
