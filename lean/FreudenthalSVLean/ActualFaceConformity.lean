import FreudenthalSVLean.ActualFaceSupport
import FreudenthalSVLean.LowDegreeBubbleExpansion

/-!
# Conforming cubic face fields on every interior star face

For manuscript equation `vertex-face-transfer`, a face shared by two
admissible tetrahedra cannot lie in a physical boundary plane.  This
geometric fact is transferred to the exact boundary condition for the
global three-node product.  The resulting vector field belongs to the
actual defined cubic velocity space, is supported on the two owners, and
has the expected product of physical barycentric coordinates there.
Normalization and the paired means are treated separately.
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
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexStarGraphTransport
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.NodalMesh

noncomputable section

namespace FreudenthalSVLean.ActualFaceConformity

theorem starCatalog_admissible {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta : VertexStar n) : catalogAdmissible (boundaryTag n) (starCatalog ta) := by
  apply (catalog_admissible_iff _ _).mp
  simp only [starCatalog, Equiv.apply_symm_apply]
  exact (admissible_iff_boundaryTags hN n _).mp (star_state_admissible n ta)

theorem shared_catalog_face_active {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u) :
    activeFace (boundaryTag n) (starCatalog ta) r := by
  apply shared_admissible_face_active _ _ _ (starCatalog_admissible hN ta)
    (by simpa only [starCatalog_cut] using hr)
  refine ⟨starCatalog tb, u, starCatalog_admissible hN tb, ?_, ?_, ?_⟩
  · intro h
    exact hne (congrArg (fun x : VertexStar n => x.val.1) (starCatalog_injective n h))
  · simpa only [starCatalog_cut] using hu
  · rw [← displaced_catalogFace, ← displaced_catalogFace, he]

def activeGridFace {N : ℕ} (t : Tet N) (r : Vertex) : Prop :=
  ∀ j : Coordinate,
    (∃ m ∈ gridFace t r, integerGrid m j ≠ 0) ∧
    (∃ m ∈ gridFace t r, integerGrid m j ≠ (N : ℤ))

theorem shared_face_active {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 u) :
    activeGridFace ta.val.1 r := by
  have ha := shared_catalog_face_active hN ta tb r u hr hu hne he
  intro j
  constructor
  · by_cases hz : (n j).val = 0
    · have htag : boundaryTag n j ≠ 1 := by
        rw [(boundaryTag_zero_iff n j).mpr hz]
        decide
      obtain ⟨a, har, had⟩ := ha j htag
      refine ⟨gridVertexOfTet ta.val.1 a, Finset.mem_image.mpr
        ⟨a, Finset.mem_erase.mpr ⟨har, Finset.mem_univ _⟩, rfl⟩, ?_⟩
      rw [← catalog_displacement ta a j] at had
      change ((gridVertexOfTet ta.val.1 a j).val : ℤ) ≠ 0
      omega
    · refine ⟨n, central_node_in_face ta r hr, ?_⟩
      change ((n j).val : ℤ) ≠ 0
      exact_mod_cast hz
  · by_cases hupp : (n j).val = N
    · have htag : boundaryTag n j ≠ 1 := by
        rw [(boundaryTag_upper_iff hN n j).mpr hupp]
        decide
      obtain ⟨a, har, had⟩ := ha j htag
      refine ⟨gridVertexOfTet ta.val.1 a, Finset.mem_image.mpr
        ⟨a, Finset.mem_erase.mpr ⟨har, Finset.mem_univ _⟩, rfl⟩, ?_⟩
      rw [← catalog_displacement ta a j] at had
      change ((gridVertexOfTet ta.val.1 a j).val : ℤ) ≠ (N : ℤ)
      omega
    · refine ⟨n, central_node_in_face ta r hr, ?_⟩
      change ((n j).val : ℤ) ≠ (N : ℤ)
      exact_mod_cast hupp

theorem faceScalar_degree {N : ℕ} (t v : Tet N) (r : Vertex) :
    (faceScalar t r v).totalDegree ≤ 3 := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ m ∈ gridFace t r, (meshNodalPolynomial v (integerGrid m)).totalDegree) ≤
        ∑ _m ∈ gridFace t r, 1 :=
      Finset.sum_le_sum (fun m _ => meshNodalPolynomial_degree_le v (integerGrid m))
    _ = 3 := by simp [gridFace_card]

theorem faceScalar_conforming {N : ℕ} (t : Tet N) (r : Vertex) (v w : Tet N)
    (x : Space) (hv : x ∈ tetrahedron v) (hw : x ∈ tetrahedron w) :
    eval x (faceScalar t r v) = eval x (faceScalar t r w) := by
  simp only [faceScalar, map_prod, meshNodalPolynomial_eval v _ x hv,
    meshNodalPolynomial_eval w _ x hw]

theorem gridNode_inBox {N : ℕ} (m : GridVertex N) : nodeInBox N (integerGrid m) := by
  intro j
  change 0 ≤ ((m j).val : ℤ) ∧ ((m j).val : ℤ) ≤ (N : ℤ)
  have hm := (m j).isLt
  omega

theorem faceScalar_boundary_zero {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex)
    (ha : activeGridFace t r) (v : Tet N) (x : Space)
    (hv : x ∈ tetrahedron v) (hx : x ∈ cubeBoundary) : eval x (faceScalar t r v) = 0 := by
  simp only [faceScalar, map_prod, meshNodalPolynomial_eval v _ x hv]
  obtain ⟨j, hj⟩ := hx.2
  rcases hj with hj | hj
  · obtain ⟨m, hm, hnj⟩ := (ha j).1
    apply Finset.prod_eq_zero hm
    exact meshNodal_zero_lower (integerGrid m) (gridNode_inBox m) x j hj hnj
  · obtain ⟨m, hm, hnj⟩ := (ha j).2
    apply Finset.prod_eq_zero hm
    exact meshNodal_zero_upper hN (integerGrid m) (gridNode_inBox m) x j hj hnj

/-- The globally defined face product is an actual cubic velocity field,
including every boundary vertex case allowed by the interior-face geometry. -/
theorem faceField_mem_velocitySpace {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex)
    (ha : activeGridFace t r) (s : Space) : faceField N t r s ∈ velocitySpace N 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v j
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using faceScalar_degree t v r)
  · intro v w x hv hw j
    simp only [faceField, map_mul, eval_C, faceScalar_conforming t r v w x hv hw]
  · intro v x hv hx j
    simp only [faceField, map_mul, eval_C, faceScalar_boundary_zero hN t r ha v x hv hx,
      mul_zero]

theorem faceScalar_self {N : ℕ} (t : Tet N) (r : Vertex) :
    faceScalar t r t = ∏ a ∈ Finset.univ.erase r, FreudenthalMesh.barycentric t a := by
  rw [faceScalar, gridFace, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro a _
    exact meshNodalPolynomial_eq_barycentric t _ a (gridVertex_intPoint t a)
  · intro a _ b _ h
    exact gridVertexOfTet_injective t h

theorem faceScalar_shared {N : ℕ} (t v : Tet N) (r u : Vertex)
    (he : gridFace t r = gridFace v u) : faceScalar t r v = faceScalar v u v := by
  rw [faceScalar, faceScalar, he]

end FreudenthalSVLean.ActualFaceConformity
