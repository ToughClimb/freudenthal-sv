import FreudenthalSVLean.VertexCompatibility
import FreudenthalSVLean.RawVertexMean

/-!
# Actual global raw cubic vertex fields

For manuscript equation `vertex-raw-bubble`, one fixed linear operator
uses the global nodal products `φ_n² φ_m`, indexed by distinct active
geometric edge directions.  The direction-to-endpoint correspondence is
proved for every positive mesh size.  Every summand is an actual member
of the conforming, homogeneous-boundary cubic velocity space; its support
lies in the marked vertex star.

The unit compatibility map is related to these fields through the exact
local nodal expansion, rather than through an assumed reference matrix.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.ConformingSkeletonBubble
open FreudenthalSVLean.PolynomialScaling

noncomputable section

namespace FreudenthalSVLean.RawVertexField

def endpoint {N : ℕ} (n : GridVertex N) (d : ActiveEdge (boundaryTag n)) : Coordinate → ℤ :=
  integerGrid n + d.val

theorem endpoint_realizes {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) :
    ∃ (t : Tet N) (a l : Vertex), gridVertexOfTet t a = n ∧ l ≠ a ∧
      integerGrid (gridVertexOfTet t l) = endpoint n d := by
  obtain ⟨t, a, l, hta, hla, he⟩ :=
    (geometric_direction_iff hN n d.val).mpr (Finset.mem_filter.mp d.property).1
  refine ⟨t, a, l, hta, hla, ?_⟩
  unfold endpoint
  rw [← he]
  abel

theorem endpoint_inBox {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) : nodeInBox N (endpoint n d) := by
  obtain ⟨t, a, l, _, _, he⟩ := endpoint_realizes hN n d
  rw [← he]
  exact gridNode_inBox _

theorem endpoint_active {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) : activePair N (integerGrid n) (endpoint n d) := by
  obtain ⟨t, a, l, _, _, he⟩ := endpoint_realizes hN n d
  rw [← he]
  apply (activeDirection_iff_activePair hN n (gridVertexOfTet t l)).mp
  rw [he]
  simpa only [endpoint, add_sub_cancel_left] using (Finset.mem_filter.mp d.property).2

def cubicEdgeLinear (N : ℕ) (n m : Coordinate → ℤ) :
    Space →ₗ[ℝ] BrokenVelocity N where
  toFun s := edgeBubbleField N 2 n m s
  map_add' s t := by
    funext v j
    simp [edgeBubbleField, Pi.add_apply, map_add, add_mul]
  map_smul' c s := by
    funext v j
    simp [edgeBubbleField, Pi.smul_apply, smul_eq_C_mul, map_mul, mul_assoc]

def rawField {N : ℕ} (n : GridVertex N) :
    JetSpace (boundaryTag n) →ₗ[ℝ] BrokenVelocity N :=
  ∑ d : ActiveEdge (boundaryTag n),
    (cubicEdgeLinear N (integerGrid n) (endpoint n d)).comp (LinearMap.proj d)

theorem rawField_apply {N : ℕ} (n : GridVertex N) (x : JetSpace (boundaryTag n))
    (t : Tet N) (j : Coordinate) :
    rawField n x t j = ∑ d : ActiveEdge (boundaryTag n),
      edgeBubbleField N 2 (integerGrid n) (endpoint n d) (x d) t j := by
  simp [rawField, cubicEdgeLinear, LinearMap.sum_apply, Finset.sum_apply]

theorem rawField_mem_velocitySpace {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) : rawField n x ∈ velocitySpace N 3 := by
  have he : rawField n x = ∑ d : ActiveEdge (boundaryTag n),
      edgeBubbleField N 2 (integerGrid n) (endpoint n d) (x d) := by
    funext t j
    simpa only [Finset.sum_apply] using rawField_apply n x t j
  rw [he]
  apply Submodule.sum_mem
  intro d _
  exact edgeBubbleField_mem_velocitySpace hN (by norm_num) (by norm_num)
    (integerGrid n) (endpoint n d) (gridNode_inBox n) (endpoint_inBox hN n d)
    (endpoint_active hN n d) (x d)

def rawConforming {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    JetSpace (boundaryTag n) →ₗ[ℝ] velocitySpace N 3 :=
  (rawField n).codRestrict _ (rawField_mem_velocitySpace hN n)

theorem rawField_zero_off_star {N : ℕ} (n : GridVertex N) (x : JetSpace (boundaryTag n))
    (t : Tet N) (ht : ∀ a : Vertex, gridVertexOfTet t a ≠ n) (j : Coordinate) :
    rawField n x t j = 0 := by
  have hn : n ∉ gridVertices t := by
    intro h
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp h
    exact ht a he
  rw [rawField_apply]
  apply Finset.sum_eq_zero
  intro d _
  rw [edgeBubbleField, node_polynomial_zero_of_missing t n hn]
  simp

theorem intPoint_injective : Function.Injective (GridNodalSupport.intPoint) := by
  intro n m h
  funext j
  have hj := congrFun h j
  change (n j : ℝ) = (m j : ℝ) at hj
  exact_mod_cast hj

theorem integer_vertex_displacement {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (l : Vertex) :
    integerGrid (gridVertexOfTet ta.val.1 l) =
      integerGrid n + catalogRelative (starCatalog ta) l := by
  funext j
  have h := catalog_displacement ta l j
  change ((gridVertexOfTet ta.val.1 l j).val : ℤ) =
    ((n j).val : ℤ) + catalogRelative (starCatalog ta) l j
  linarith

theorem endpoint_is_vertex_iff {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (d : ActiveEdge (boundaryTag n)) (l : Vertex) :
    GridNodalSupport.intPoint (endpoint n d) = chainVertex ta.val.1.2 (cellOrigin ta.val.1.1) l ↔
      catalogRelative (starCatalog ta) l = d.val := by
  rw [← gridVertex_intPoint, (intPoint_injective).eq_iff,
    integer_vertex_displacement, endpoint]
  exact add_left_cancel_iff.trans eq_comm

/-- This polynomial identity holds on each actual incident tetrahedron.
An absent endpoint contributes zero, and an existing endpoint contributes
its actual scaled barycentric coordinate. -/
theorem endpoint_nodal_expansion {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (d : ActiveEdge (boundaryTag n)) :
    meshNodalPolynomial ta.val.1 (endpoint n d) =
      ∑ l : Vertex, if catalogRelative (starCatalog ta) l = d.val then
        FreudenthalMesh.barycentric ta.val.1 l else 0 := by
  classical
  unfold meshNodalPolynomial GridNodalSupport.nodalPolynomial rescale
  simp only [C_1, one_mul, map_sum, intPoint_cellIntOrigin]
  apply Finset.sum_congr rfl
  intro l _
  by_cases he : catalogRelative (starCatalog ta) l = d.val
  · rw [if_pos ((endpoint_is_vertex_iff ta d l).mpr he), if_pos he]
    rfl
  · rw [if_neg (mt (endpoint_is_vertex_iff ta d l).mp he), if_neg he, map_zero]

theorem local_cubic_expansion {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (d : ActiveEdge (boundaryTag n)) (s : Space) (j : Coordinate) :
    edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1 j =
      ∑ l : Vertex, if catalogRelative (starCatalog ta) l = d.val then
        rescale (meshScale N) (s j)
          (SkeletonBubble.vertexBubble ta.val.1.2 (cellOrigin ta.val.1.1) ta.val.2 l)
      else 0 := by
  have hn : GridNodalSupport.intPoint (integerGrid n) =
      chainVertex ta.val.1.2 (cellOrigin ta.val.1.1) ta.val.2 := by
    exact (congrArg (fun m : GridVertex N => GridNodalSupport.intPoint (integerGrid m))
      ta.property).symm.trans (gridVertex_intPoint _ _)
  rw [edgeBubbleField, endpoint_nodal_expansion,
    meshNodalPolynomial_eq_barycentric ta.val.1 (integerGrid n) ta.val.2 hn,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs
  · simp only [rescale, SkeletonBubble.vertexBubble, map_mul, map_pow,
      FreudenthalMesh.barycentric, ScaledChainGeometry.scaledBarycentric, mul_assoc]
  · simp

theorem sum_active_eq {M : Type*} [AddCommMonoid M] (b : BoundaryWord)
    (r : Coordinate → ℤ) (f : ActiveEdge b → M) :
    (∑ d : ActiveEdge b, if r = d.val then f d else 0) =
      if hr : r ∈ catalogActiveEdges b then f ⟨r, hr⟩ else 0 := by
  classical
  by_cases hr : r ∈ catalogActiveEdges b
  · rw [dif_pos hr]
    have he (d : ActiveEdge b) : r = d.val ↔ d = ⟨r, hr⟩ := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact (congrArg Subtype.val h).symm
    simp only [he]
    exact Fintype.sum_ite_eq' _ _
  · rw [dif_neg hr]
    apply Finset.sum_eq_zero
    intro d _
    rw [if_neg]
    intro h
    exact hr (h.symm ▸ d.property)

def catalogIncidenceEquiv {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    VertexStar n ≃ Incidence (boundaryTag n) :=
  (actualStateEquiv hN n).trans (admissibleCatalogEquiv (boundaryTag n)).symm

theorem catalogIncidenceEquiv_val {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (ta : VertexStar n) : (catalogIncidenceEquiv hN n ta).val = starCatalog ta := by
  rfl

end FreudenthalSVLean.RawVertexField
