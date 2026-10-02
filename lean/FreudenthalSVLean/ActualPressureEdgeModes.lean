import FreudenthalSVLean.HomogeneousEdgeModes
import FreudenthalSVLean.PolynomialChainTransport

/-!
# Actual pressure coefficients and physical edge traces

For manuscript Lemma `edge-star`, the homogeneous edge-mode calculation
is applied to an actual pressure polynomial after the proved physical
element pullback.  The resulting coefficient extractor is one fixed
linear map.  Arbitrary physical edge parameters satisfy the complete
trace identity.  In degrees three and four, zero values at the two actual
endpoints give precisely the two endpoint coefficients, or the two
endpoint coefficients and the middle coefficient.

The construction works on every actual tetrahedron and every positive
mesh size.  It does not assume that coefficients written on different
tetrahedra are compatible; that follows from the separate trace identities
and coefficient-recovery theorem.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.HomogeneousBarycentric
open FreudenthalSVLean.HomogeneousEdgeModes
open FreudenthalSVLean.PolynomialChainTransport

noncomputable section

namespace FreudenthalSVLean.ActualPressureEdgeModes

theorem segmentPoint_zero (x y : Space) : segmentPoint x y 0 = x := by
  funext j
  simp [segmentPoint]

theorem segmentPoint_one (x y : Space) : segmentPoint x y 1 = y := by
  funext j
  simp [segmentPoint]

abbrev Poly := MvPolynomial Coordinate ℝ

def edgeRepresentationLinear {N : ℕ} (t : Tet N) (d : ℕ) : Poly →ₗ[ℝ] MvPolynomial Vertex ℝ :=
  (representationLinear (Equiv.refl Coordinate) (0 : Space) d).comp
    (PolynomialInverseEstimate.pullbackLinear t.2 (cellOrigin t.1) (meshScale N))

def edgeCoefficients {N : ℕ} (t : Tet N) (a b : Vertex) (d : ℕ) :
    Poly →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  LinearMap.pi (fun ν => (lcoeff ℝ (edgeExponent a b d ν)).comp (edgeRepresentationLinear t d))

theorem edgeCoefficients_apply {N : ℕ} (t : Tet N) (a b : Vertex) (d : ℕ)
    (p : Poly) (ν : Fin (d + 1)) :
    edgeCoefficients t a b d p ν = coeff (edgeExponent a b d ν) (edgeRepresentationLinear t d p) := rfl

theorem edgeRepresentation_homogeneous {N : ℕ} (t : Tet N) (d : ℕ) (p : Poly) :
    IsHomogeneous (edgeRepresentationLinear t d p) d :=
  representation_homogeneous _ _ _ _

theorem pullback_physical_edge_eval {N : ℕ} (t : Tet N) (p : Poly)
    (a b : Vertex) (s : ℝ) :
    eval (segmentPoint (chainVertex (Equiv.refl Coordinate) (0 : Space) a)
      (chainVertex (Equiv.refl Coordinate) (0 : Space) b) s)
      (PolynomialInverseEstimate.pullback t.2 (cellOrigin t.1) (meshScale N) p) =
      eval (segmentPoint (vertex t a) (vertex t b) s) p := by
  rw [PolynomialInverseEstimate.pullback_eval, normalize_symm_segment,
    normalize_symm_vertex, normalize_symm_vertex]
  apply congrArg (fun x : Space => eval x p)
  funext j
  simp only [vertex, scaledVertex, Pi.smul_apply, smul_eq_mul, segmentPoint]
  ring

/-- Exact correspondence between the coefficient input and the actual
physical pressure trace.  No mesh size is fixed in advance. -/
theorem edgeRepresentation_eval {N : ℕ} (t : Tet N) (d : ℕ) (p : Poly)
    (hp : p.totalDegree ≤ d) (a b : Vertex) (s : ℝ) :
    eval (edgeBarycentric a b s) (edgeRepresentationLinear t d p) =
      eval (segmentPoint (vertex t a) (vertex t b) s) p := by
  let x := segmentPoint (chainVertex (Equiv.refl Coordinate) (0 : Space) a)
    (chainVertex (Equiv.refl Coordinate) (0 : Space) b) s
  calc
    _ = eval x (eval₂Hom C (ChainGeometry.barycentric (Equiv.refl Coordinate) (0 : Space))
        (edgeRepresentationLinear t d p)) := by
      rw [PolynomialCalculus.eval_substitution]
      apply congrArg (fun z : Vertex → ℝ => eval z (edgeRepresentationLinear t d p))
      funext i
      simp only [x, barycentric_edge, edgeBarycentric]
    _ = eval x (PolynomialInverseEstimate.pullback t.2 (cellOrigin t.1) (meshScale N) p) := by
      apply congrArg (eval x)
      exact substitute_representation _ _ d _
        ((PolynomialInverseEstimate.pullback_degree _ _ _ p).trans hp)
    _ = _ := pullback_physical_edge_eval t p a b s

theorem physical_edge_expansion {N : ℕ} (t : Tet N) (d : ℕ) (p : Poly)
    (hp : p.totalDegree ≤ d) (a b : Vertex) (hab : a ≠ b) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s) p =
      ∑ ν : Fin (d + 1), edgeCoefficients t a b d p ν *
        (1 - s) ^ (d - ν.val) * s ^ ν.val := by
  rw [← edgeRepresentation_eval t d p hp a b s]
  exact homogeneous_edge_expansion _ d (edgeRepresentation_homogeneous t d p) a b hab s

theorem cubic_physical_zero_endpoint_trace {N : ℕ} (t : Tet N) (p : Poly)
    (hp : p.totalDegree ≤ 3) (a b : Vertex) (hab : a ≠ b)
    (ha : eval (vertex t a) p = 0) (hb : eval (vertex t b) p = 0) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s) p =
      edgeCoefficients t a b 3 p 1 * (1 - s) ^ 2 * s +
      edgeCoefficients t a b 3 p 2 * (1 - s) * s ^ 2 := by
  rw [← edgeRepresentation_eval t 3 p hp a b s]
  apply cubic_zero_endpoint_trace _ (edgeRepresentation_homogeneous t 3 p) a b hab
  · rw [edgeRepresentation_eval t 3 p hp a b]
    rw [segmentPoint_zero]
    exact ha
  · rw [edgeRepresentation_eval t 3 p hp a b]
    rw [segmentPoint_one]
    exact hb

theorem quartic_physical_zero_endpoint_trace {N : ℕ} (t : Tet N) (p : Poly)
    (hp : p.totalDegree ≤ 4) (a b : Vertex) (hab : a ≠ b)
    (ha : eval (vertex t a) p = 0) (hb : eval (vertex t b) p = 0) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s) p =
      edgeCoefficients t a b 4 p 1 * (1 - s) ^ 3 * s +
      edgeCoefficients t a b 4 p 2 * (1 - s) ^ 2 * s ^ 2 +
      edgeCoefficients t a b 4 p 3 * (1 - s) * s ^ 3 := by
  rw [← edgeRepresentation_eval t 4 p hp a b s]
  apply quartic_zero_endpoint_trace _ (edgeRepresentation_homogeneous t 4 p) a b hab
  · rw [edgeRepresentation_eval t 4 p hp a b]
    rw [segmentPoint_zero]
    exact ha
  · rw [edgeRepresentation_eval t 4 p hp a b]
    rw [segmentPoint_one]
    exact hb

end FreudenthalSVLean.ActualPressureEdgeModes
