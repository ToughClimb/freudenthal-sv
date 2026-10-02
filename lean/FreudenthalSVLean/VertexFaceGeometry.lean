import FreudenthalSVLean.VertexStarConnectivity

/-!
# Exact universal geometry of faces through a star vertex

For manuscript equation `vertex-face-transfer`, a three-node face through
the central vertex belongs to exactly two tetrahedra of the full lattice
star. Its two omitted-vertex barycentric gradients are opposite. If both
owners are admissible in the grid box, the face is not contained in any
physical boundary plane through the central vertex.

All checks quantify the full twenty-four-state model and all twenty-seven
boundary words. Their applicability to arbitrary mesh size is supplied by
the explicit incidence and geometric face equivalences, not by sampling a
mesh. The identities are geometry certificates, not rank computations.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity

namespace FreudenthalSVLean.VertexFaceGeometry

def catalogVertices (s : CatalogState) : Finset (Coordinate → ℤ) :=
  Finset.univ.image (catalogRelative s)

def faceOwners (s : CatalogState) (r : Vertex) : Finset CatalogState :=
  Finset.univ.filter (fun t => catalogFace s r ⊆ catalogVertices t)

theorem own_face_subset (s : CatalogState) (r : Vertex) :
    catalogFace s r ⊆ catalogVertices s := by
  exact Finset.image_subset_image (Finset.erase_subset r Finset.univ)

/-- A face containing the central vertex has exactly two owners in the
full lattice, even if only one of them is admissible in a boundary box. -/
theorem face_owner_count : ∀ (s : CatalogState) (r : Vertex), r ≠ s.2 →
    (faceOwners s r).card = 2 := by
  decide +kernel

theorem owner_has_face : ∀ (s t : CatalogState) (r : Vertex), r ≠ s.2 →
    catalogFace s r ⊆ catalogVertices t →
      ∃ u : Vertex, u ≠ t.2 ∧ catalogFace s r = catalogFace t u := by
  decide +kernel

noncomputable def catalogGradient (s : CatalogState) (r : Vertex) (j : Coordinate) : ℤ :=
  barycentricGradient (R := ℤ) (orderPerm s.1) r j

theorem shared_face_gradients_opposite : ∀ (s t : CatalogState) (r u : Vertex),
    s ≠ t → r ≠ s.2 → u ≠ t.2 → catalogFace s r = catalogFace t u →
      ∀ j : Coordinate, catalogGradient s r j = -catalogGradient t u j := by
  decide +kernel

/-- Nonzero movement in every boundary coordinate is the local version
of the global nodal-product boundary-plane criterion. -/
def activeFace (b : Coordinate → Fin 3) (s : CatalogState) (r : Vertex) : Prop :=
  ∀ j : Coordinate, b j ≠ 1 →
    ∃ a : Vertex, a ≠ r ∧ catalogRelative s a j ≠ 0

instance (b : Coordinate → Fin 3) (s : CatalogState) (r : Vertex) :
    Decidable (activeFace b s r) :=
  inferInstanceAs (Decidable (∀ j : Coordinate, b j ≠ 1 →
    ∃ a : Vertex, a ≠ r ∧ catalogRelative s a j ≠ 0))

theorem shared_admissible_face_active : ∀ (b : Coordinate → Fin 3)
    (s : CatalogState) (r : Vertex),
    catalogAdmissible b s → r ≠ s.2 →
    (∃ (t : CatalogState) (u : Vertex), catalogAdmissible b t ∧ s ≠ t ∧
      u ≠ t.2 ∧ catalogFace s r = catalogFace t u) → activeFace b s r := by
  decide +kernel

/-- The two known owners exhaust the support; every third tetrahedron
must miss at least one of the three required nodes. -/
theorem faceOwners_eq_pair (s t : CatalogState) (r u : Vertex) (hs : r ≠ s.2)
    (hne : s ≠ t) (he : catalogFace s r = catalogFace t u) :
    faceOwners s r = {s, t} := by
  have hh : {s, t} ⊆ faceOwners s r := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · rw [hv]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, own_face_subset s r⟩
    · rw [hv]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [he]
      exact own_face_subset t u
  apply (Finset.eq_of_subset_of_card_le hh ?_).symm
  rw [face_owner_count s r hs]
  simp [hne]

end FreudenthalSVLean.VertexFaceGeometry
