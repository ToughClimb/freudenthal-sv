import FreudenthalSVLean.ActualVertexStarGraph
import FreudenthalSVLean.VertexFaceGeometry
import FreudenthalSVLean.SkeletonField

/-!
# Exact two-tetrahedron support of global face bubbles

For manuscript equation `vertex-face-transfer`, the global product of the
three face nodes is supported on precisely the two adjacent tetrahedra.
The proof transfers the full universal face-owner calculation to actual
grid vertices using injective integer displacement.  A third element must
miss a required node, so its local nodal product is the zero polynomial.
This establishes support as an identity of actual spatial polynomials,
not merely as a list of selected reference coefficients.
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
open FreudenthalSVLean.NodalMesh

noncomputable section

namespace FreudenthalSVLean.ActualFaceSupport

def gridVertices {N : ℕ} (t : Tet N) : Finset (GridVertex N) :=
  Finset.univ.image (gridVertexOfTet t)

def starCatalog {N : ℕ} {n : GridVertex N} (ta : VertexStar n) : CatalogState :=
  catalogEquiv.symm (ta.val.1.2, ta.val.2)

theorem starCatalog_cut {N : ℕ} {n : GridVertex N} (ta : VertexStar n) :
    (starCatalog ta).2 = ta.val.2 := by
  have h := congrArg Prod.snd (catalogEquiv.apply_symm_apply (ta.val.1.2, ta.val.2))
  exact h

theorem starCatalog_injective {N : ℕ} (n : GridVertex N) :
    Function.Injective (starCatalog (n := n)) := by
  intro ta tb h
  apply starState_injective n
  have he := congrArg catalogEquiv h
  simpa only [starCatalog, Equiv.apply_symm_apply] using he

theorem displaced_catalogFace {N : ℕ} {n : GridVertex N} (ta : VertexStar n) (r : Vertex) :
    (gridFace ta.val.1 r).image (displacement n) = catalogFace (starCatalog ta) r := by
  rw [displaced_face]
  rw [← catalog_relativeFace]
  simp only [starCatalog, Equiv.apply_symm_apply]

theorem displaced_catalogVertices {N : ℕ} {n : GridVertex N} (ta : VertexStar n) :
    (gridVertices ta.val.1).image (displacement n) = catalogVertices (starCatalog ta) := by
  unfold gridVertices catalogVertices
  rw [Finset.image_image]
  congr 1
  funext a j
  change ((gridVertexOfTet ta.val.1 a j).val : ℤ) - ((n j).val : ℤ) = _
  rw [grid_displacement n ta a j]
  have he := congrFun (relative_catalog (starCatalog ta) a) j
  simpa only [starCatalog, Equiv.apply_symm_apply] using he

theorem catalog_displacement {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (a : Vertex) (j : Coordinate) :
    ((gridVertexOfTet ta.val.1 a j).val : ℤ) - ((n j).val : ℤ) =
      catalogRelative (starCatalog ta) a j := by
  have he := congrFun (relative_catalog (starCatalog ta) a) j
  simp only [starCatalog, Equiv.apply_symm_apply] at he
  exact (grid_displacement n ta a j).trans he

theorem gridFace_subset_vertices {N : ℕ} (t : Tet N) (r : Vertex) :
    gridFace t r ⊆ gridVertices t :=
  Finset.image_subset_image (Finset.erase_subset r Finset.univ)

theorem central_node_in_face {N : ℕ} {n : GridVertex N} (ta : VertexStar n)
    (r : Vertex) (hr : r ≠ ta.val.2) : n ∈ gridFace ta.val.1 r := by
  exact Finset.mem_image.mpr ⟨ta.val.2,
    Finset.mem_erase.mpr ⟨hr.symm, Finset.mem_univ _⟩, ta.property⟩

/-- Any tetrahedron containing the three nodes of a shared star face is
one of the two incident tetrahedra, for arbitrary positive mesh size. -/
theorem containing_face_is_owner {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (t : Tet N) (ht : gridFace ta.val.1 r ⊆ gridVertices t) :
    t = ta.val.1 ∨ t = tb.val.1 := by
  have hn := ht (central_node_in_face ta r hr)
  obtain ⟨a, _, hta⟩ := Finset.mem_image.mp hn
  let tc : VertexStar n := ⟨(t, a), hta⟩
  have hsub : catalogFace (starCatalog ta) r ⊆ catalogVertices (starCatalog tc) := by
    rw [← displaced_catalogFace, ← displaced_catalogVertices]
    exact Finset.image_subset_image ht
  have hcat : catalogFace (starCatalog ta) r = catalogFace (starCatalog tb) u := by
    rw [← displaced_catalogFace, ← displaced_catalogFace, he]
  have hncat : starCatalog ta ≠ starCatalog tb := by
    intro h
    have heq := starCatalog_injective n h
    exact hne (congrArg (fun x : VertexStar n => x.val.1) heq)
  have hp := faceOwners_eq_pair (starCatalog ta) (starCatalog tb) r u
    (by simpa only [starCatalog_cut] using hr) hncat hcat
  have hm : starCatalog tc ∈ faceOwners (starCatalog ta) r :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩
  rw [hp] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · left
    exact congrArg (fun x : VertexStar n => x.val.1) (starCatalog_injective n h)
  · right
    exact congrArg (fun x : VertexStar n => x.val.1) (starCatalog_injective n h)

theorem gridVertex_intPoint {N : ℕ} (t : Tet N) (a : Vertex) :
    GridNodalSupport.intPoint (integerGrid (gridVertexOfTet t a)) =
      ChainGeometry.chainVertex t.2 (cellOrigin t.1) a := by
  funext j
  by_cases h : (t.2.symm j).val < a.val <;>
    simp [GridNodalSupport.intPoint, integerGrid, gridVertexOfTet, prefixMask,
      ChainGeometry.chainVertex, cellOrigin, h]

theorem node_polynomial_zero_of_missing {N : ℕ} (t : Tet N) (m : GridVertex N)
    (hm : m ∉ gridVertices t) : meshNodalPolynomial t (integerGrid m) = 0 := by
  apply meshNodalPolynomial_zero_of_not_vertex
  intro a h
  have hp : GridNodalSupport.intPoint (integerGrid m) =
      GridNodalSupport.intPoint (integerGrid (gridVertexOfTet t a)) :=
    h.trans (gridVertex_intPoint t a).symm
  have he : m = gridVertexOfTet t a := by
    funext j
    apply Fin.ext
    have hj := congrFun hp j
    simp only [GridNodalSupport.intPoint, integerGrid, Int.cast_natCast] at hj
    exact_mod_cast hj
  apply hm
  rw [he]
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

def faceScalar {N : ℕ} (t : Tet N) (r : Vertex) (v : Tet N) : MvPolynomial Coordinate ℝ :=
  ∏ m ∈ gridFace t r, meshNodalPolynomial v (integerGrid m)

def faceField (N : ℕ) (t : Tet N) (r : Vertex) (s : Space) : BrokenVelocity N :=
  fun v j => C (s j) * faceScalar t r v

/-- Every non-owner has identically zero local face-bubble polynomial. -/
theorem faceScalar_zero_off_pair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (t : Tet N) (hta : t ≠ ta.val.1) (htb : t ≠ tb.val.1) :
    faceScalar ta.val.1 r t = 0 := by
  have hs : ¬gridFace ta.val.1 r ⊆ gridVertices t := by
    intro h
    rcases containing_face_is_owner ta tb r u hr hne he t h with h | h
    · exact hta h
    · exact htb h
  obtain ⟨m, hm, hmt⟩ := Finset.not_subset.mp hs
  unfold faceScalar
  apply Finset.prod_eq_zero hm
  exact node_polynomial_zero_of_missing t m hmt

theorem faceField_zero_off_pair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hne : ta.val.1 ≠ tb.val.1)
    (he : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (s : Space) (t : Tet N) (hta : t ≠ ta.val.1) (htb : t ≠ tb.val.1) (j : Coordinate) :
    faceField N ta.val.1 r s t j = 0 := by
  rw [faceField, faceScalar_zero_off_pair ta tb r u hr hne he t hta htb, mul_zero]

end FreudenthalSVLean.ActualFaceSupport
