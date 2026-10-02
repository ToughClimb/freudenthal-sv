import FreudenthalSVLean.VertexCompatibility
import FreudenthalSVLean.VertexFaceGeometry
import FreudenthalSVLean.ActualFaceMean

/-!
# Cancellation of raw vertex-bubble means

For manuscript equation `vertex-raw-properties`, the integral of each
active cubic edge field is proportional to `g_a + g_b` on an incident
tetrahedron.  This module proves that these vectors sum to zero over the
entire admissible star, including every boundary word.  The finite
identity uses integer gradients derived from actual barycentric
polynomials.  It is checked by the Lean kernel and then transported to
real coefficients and arbitrary linear combinations of the edge fields.

The arbitrary-mesh incidence equivalence and the true scaled integral
formula are proved in `VertexStarCoverage` and `RawVertexMean`,
respectively.  Their composition with the global nodal field is a
separate assembly step.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualFaceMean

noncomputable section

namespace FreudenthalSVLean.VertexMeanCancellation

def integerMeanColumn (b : BoundaryWord) (d : ActiveEdge b) (j : Coordinate) : ℤ :=
  ∑ t : Incidence b, ∑ a : Vertex,
    if catalogRelative t.val a = d.val then
      catalogGradient t.val t.val.2 j + catalogGradient t.val a j
    else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- All active geometric edges, for all twenty-seven boundary words.
The quantification is over the exact finite direction set, not over a
sample of grid vertices or a selected list of matrix rows. -/
theorem integerMeanColumn_zero : ∀ (b : BoundaryWord) (d : ActiveEdge b) (j : Coordinate),
    integerMeanColumn b d j = 0 := by
  decide +kernel

def realMeanEntry (b : BoundaryWord) (t : Incidence b) (d : ActiveEdge b)
    (j : Coordinate) : ℝ :=
  ∑ a : Vertex, if catalogRelative t.val a = d.val then
    barycentricGradient (orderPerm t.val.1) t.val.2 j +
      barycentricGradient (orderPerm t.val.1) a j
  else 0

theorem realMeanColumn_zero (b : BoundaryWord) (d : ActiveEdge b) (j : Coordinate) :
    ∑ t : Incidence b, realMeanEntry b t d j = 0 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (integerMeanColumn_zero b d j)
  simpa only [integerMeanColumn, realMeanEntry, Int.cast_sum, Int.cast_ite,
    Int.cast_add, Int.cast_zero, catalogGradient, gradient_int_cast] using h

def localMeanNumerator (b : BoundaryWord) (x : JetSpace b) (t : Incidence b) : ℝ :=
  ∑ d : ActiveEdge b, ∑ j : Coordinate, x d j * realMeanEntry b t d j

def localMeanMap (b : BoundaryWord) : JetSpace b →ₗ[ℝ] VertexData b where
  toFun := localMeanNumerator b
  map_add' x y := by
    funext t
    simp [localMeanNumerator, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext t
    simp [localMeanNumerator, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem localMeanNumerator_sum_zero (b : BoundaryWord) (x : JetSpace b) :
    ∑ t : Incidence b, localMeanNumerator b x t = 0 := by
  classical
  unfold localMeanNumerator
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro d _
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, realMeanColumn_zero, mul_zero, Finset.sum_const_zero]

end FreudenthalSVLean.VertexMeanCancellation
