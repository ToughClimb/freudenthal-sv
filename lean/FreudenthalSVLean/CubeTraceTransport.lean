import FreudenthalSVLean.CubePolynomialTransport
import FreudenthalSVLean.CanonicalEdgeOrientation
import FreudenthalSVLean.CanonicalPressureLift

/-!
# Full edge and vertex traces under physical cube symmetry

For manuscript Lemma `edge-lift`, this module transports actual edge-star
incidences and polynomial traces, including the endpoint exchange caused
by central inversion.  Vertex-zero divergence-image pressures remain in
that subspace.  Edge-star pressure energy is preserved by an explicit
equivalence of actual incidences and a Lebesgue change of variables.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CubeMeshSymmetry
open FreudenthalSVLean.CubePolynomialTransport
open FreudenthalSVLean.CanonicalEdgeOrientation
open FreudenthalSVLean.CanonicalPressureLift

noncomputable section

namespace FreudenthalSVLean.CubeTraceTransport

set_option backward.isDefEq.respectTransparency false

theorem transformVertex_involutive (flip : Bool) (a : Vertex) :
    transformVertex flip (transformVertex flip a) = a := by
  cases flip <;> simp [transformVertex]

theorem transformVertex_injective (flip : Bool) : Function.Injective (transformVertex flip) :=
  Function.Involutive.injective (transformVertex_involutive flip)

theorem pointEquiv_segment (π : Equiv.Perm Coordinate) (flip : Bool)
    (x y : Space) (s : ℝ) : pointEquiv π flip (segmentPoint x y s) =
      segmentPoint (pointEquiv π flip x) (pointEquiv π flip y) s := by
  funext j
  cases flip <;> simp only [pointEquiv_apply, Bool.false_eq_true, if_false, if_true, segmentPoint]
  ring

theorem pointEquiv_symm_vertex {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (t : Tet N) (a : Vertex) :
    (pointEquiv π flip).symm (vertex t a) =
      vertex ((tetEquiv π flip).symm t) (transformVertex flip a) := by
  rw [pointEquiv_symm, tetEquiv_symm_apply, tetMap_vertex hN]

theorem vertexZero_pushPressure {N k : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (q : vertexZeroSpace N k) :
    pushPressure π flip q.val ∈ vertexZeroSpace N k := by
  refine ⟨pushPressure_mem π flip q.val q.property.1, ?_⟩
  intro t a
  rw [pushPressure_eval, pointEquiv_symm_vertex hN]
  exact q.property.2 _ _

def zeroPressureMap {N k : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (flip : Bool) :
    vertexZeroSpace N k →ₗ[ℝ] vertexZeroSpace N k :=
  ((pushPressureLinear π flip).comp (vertexZeroSpace N k).subtype).codRestrict _
    (vertexZero_pushPressure hN π flip)

def rawEdgeEquiv {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) :
    ActualEdgeStar a b ≃ ActualEdgeStar (nodeMap π flip a) (nodeMap π flip b) where
  toFun x :=
    ⟨(⟨(tetMap π flip x.val.1.val.1, transformVertex flip x.val.1.val.2), by
      rw [tetMap_gridVertex, x.val.1.property]⟩, transformVertex flip x.val.2), by
      rw [tetMap_gridVertex, x.property]⟩
  invFun x :=
    ⟨(⟨(tetMap π.symm flip x.val.1.val.1, transformVertex flip x.val.1.val.2), by
      rw [tetMap_gridVertex, x.val.1.property, nodeMap_inverse]⟩,
      transformVertex flip x.val.2), by
      rw [tetMap_gridVertex, x.property, nodeMap_inverse]⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact tetMap_inverse π flip _
      · exact transformVertex_involutive flip _
    · exact transformVertex_involutive flip _
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · simpa using tetMap_inverse π.symm flip x.val.1.val.1
      · exact transformVertex_involutive flip _
    · exact transformVertex_involutive flip _

def orientedEdgeEquiv {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) :
    ActualEdgeStar a b ≃ ActualEdgeStar (firstNode π flip a b) (secondNode π flip a b) :=
  match flip with
  | false => rawEdgeEquiv π false a b
  | true => (reverseEdgeStar a b).trans (rawEdgeEquiv π true b a)

theorem orientedEdge_tet {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N)
    (x : ActualEdgeStar a b) : (orientedEdgeEquiv π flip a b x).val.1.val.1 =
      tetMap π flip x.val.1.val.1 := by
  cases flip <;> rfl

def orientedParameter (flip : Bool) (s : ℝ) : ℝ := if flip then 1 - s else s

theorem oriented_segment {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) (s : ℝ) :
    pointEquiv π flip (segmentPoint (gridPoint a) (gridPoint b) s) =
      segmentPoint (gridPoint (firstNode π flip a b))
        (gridPoint (secondNode π flip a b)) (orientedParameter flip s) := by
  rw [pointEquiv_segment]
  cases flip
  · simp only [firstNode, secondNode, orientedParameter, if_false,
      nodeMap_gridPoint hN, Bool.false_eq_true]
  · simp only [firstNode, secondNode, orientedParameter, if_true, nodeMap_gridPoint hN]
    funext j
    simp only [segmentPoint]
    ring

theorem oriented_pressure_trace {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) (q : BrokenPressure N) (x : ActualEdgeStar a b) (s : ℝ) :
    EdgePressureData.pressureTrace (firstNode π flip a b) (secondNode π flip a b)
      (orientedParameter flip s) (pushPressure π flip q) (orientedEdgeEquiv π flip a b x) =
        EdgePressureData.pressureTrace a b s q x := by
  change eval (segmentPoint (gridPoint (firstNode π flip a b))
    (gridPoint (secondNode π flip a b)) (orientedParameter flip s))
      (pushPressure π flip q (orientedEdgeEquiv π flip a b x).val.1.val.1) = _
  rw [← oriented_segment hN, orientedEdge_tet, pushPressure_eval,
    MeasurableEquiv.symm_apply_apply, ← tetEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem starPressureEnergy_transport {N : ℕ} (_hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) (q : BrokenPressure N) :
    starPressureEnergy (firstNode π flip a b) (secondNode π flip a b)
      (pushPressure π flip q) = starPressureEnergy a b q := by
  unfold starPressureEnergy
  rw [← (orientedEdgeEquiv π flip a b).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [orientedEdge_tet]
  simp only [pushPressure_eval, ← tetEquiv_apply, Equiv.symm_apply_apply]
  simpa only [tetEquiv_apply] using
    tetMap_integral π flip x.val.1.val.1 (fun y => (eval y (q x.val.1.val.1)) ^ 2)

theorem vertex_derivative_transport {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (v : BrokenVelocity N)
    (hz : ∀ t a i j, eval (vertex t a) (pderiv i (v t j)) = 0) :
    ∀ t a i j, eval (vertex t a) (pderiv i (pushVelocity π flip v t j)) = 0 := by
  intro t a i j
  rw [pushVelocity_derivative, substitute_eval, pointEquiv_symm_vertex hN]
  exact hz _ _ _ _

theorem nodeMap_pair_injective {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b c d : GridVertex N)
    (he : ({nodeMap π flip a, nodeMap π flip b} : Finset (GridVertex N)) =
      {nodeMap π flip c, nodeMap π flip d}) :
    ({a, b} : Finset (GridVertex N)) = {c, d} := by
  have hi := congrArg (Finset.image (nodeMap π.symm flip)) he
  simpa only [Finset.image_insert, Finset.image_singleton, nodeMap_inverse] using hi

theorem oriented_pair {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) :
    ({firstNode π flip a b, secondNode π flip a b} : Finset (GridVertex N)) =
      {nodeMap π flip a, nodeMap π flip b} := by
  cases flip
  · rfl
  · exact Finset.pair_comm _ _

theorem pushback_edge_divergence {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (v : BrokenVelocity N)
    (t : Tet N) (l m : Vertex) (s : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) s)
        (divergence N (pushVelocity π.symm flip v) t) =
      eval (segmentPoint (vertex (tetMap π flip t) (transformVertex flip l))
        (vertex (tetMap π flip t) (transformVertex flip m)) s)
          (divergence N v (tetMap π flip t)) := by
  rw [divergence_pushVelocity, pushPressure_eval, pointEquiv_symm, Equiv.symm_symm,
    tetEquiv_symm_apply, Equiv.symm_symm, pointEquiv_segment,
    ← tetMap_vertex hN, ← tetMap_vertex hN]

theorem pushback_pressure_trace {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N)
    (v : BrokenVelocity N) (x : ActualEdgeStar a b) (s : ℝ) :
    EdgePressureData.pressureTrace a b s (divergence N (pushVelocity π.symm flip v)) x =
      EdgePressureData.pressureTrace (firstNode π flip a b) (secondNode π flip a b)
        (orientedParameter flip s) (divergence N v) (orientedEdgeEquiv π flip a b x) := by
  change eval (segmentPoint (gridPoint a) (gridPoint b) s)
    (divergence N (pushVelocity π.symm flip v) x.val.1.val.1) = _
  rw [divergence_pushVelocity, pushPressure_eval, pointEquiv_symm, Equiv.symm_symm,
    tetEquiv_symm_apply, Equiv.symm_symm, oriented_segment hN]
  change _ = eval (segmentPoint (gridPoint (firstNode π flip a b))
    (gridPoint (secondNode π flip a b)) (orientedParameter flip s))
      (divergence N v (orientedEdgeEquiv π flip a b x).val.1.val.1)
  rw [orientedEdge_tet]

theorem other_edge_transport {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) (v : BrokenVelocity N)
    (hz : ∀ (t : Tet N) (l m : Vertex), l ≠ m →
      ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠
        {firstNode π flip a b, secondNode π flip a b} → ∀ s : ℝ,
          eval (segmentPoint (vertex t l) (vertex t m) s) (divergence N v t) = 0)
    (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (he : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (s : ℝ) : eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (pushVelocity π.symm flip v) t) = 0 := by
  rw [pushback_edge_divergence hN]
  apply hz
  · exact (transformVertex_injective flip).ne hlm
  · intro hi
    rw [tetMap_gridVertex, tetMap_gridVertex, oriented_pair] at hi
    exact he (nodeMap_pair_injective π flip _ _ _ _ hi)

end FreudenthalSVLean.CubeTraceTransport
