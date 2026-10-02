import FreudenthalSVLean.OrderedSharedFaceChart
import FreudenthalSVLean.ActualFaceConformity

/-!
# Exact interior-face coverage on every mesh

For the face correction in manuscript Lemma `means`, a mesh face is
interior precisely when its three grid nodes are not all in a physical
boundary coordinate plane. The universal integer vertex-star statement
is checked in the kernel and transported by the proved actual-star
equivalence. Each interior face has exactly one other owner and one
omitted-vertex index on that owner. All statements quantify every N>0;
small meshes are not excluded and no sampled-mesh coverage is assumed.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity

noncomputable section

namespace FreudenthalSVLean.InteriorFaceCoverage

set_option backward.isDefEq.respectTransparency false

def faceAnchor {N : ℕ} (t : Tet N) (r : Fin 4) : GridVertex N :=
  gridVertexOfTet t (r.succAbove 0)

def anchoredOwner {N : ℕ} (t : Tet N) (r : Fin 4) : VertexStar (faceAnchor t r) :=
  ⟨(t, r.succAbove 0), rfl⟩

theorem anchoredOwner_omitted_ne {N : ℕ} (t : Tet N) (r : Fin 4) :
    r ≠ (anchoredOwner t r).val.2 := Fin.ne_succAbove r 0

theorem catalog_active_has_neighbor : ∀ (b : Fin 3 → Fin 3)
    (s : CatalogState) (r : Fin 4), catalogAdmissible b s → r ≠ s.2 → activeFace b s r →
      ∃ (t : CatalogState) (u : Fin 4), catalogAdmissible b t ∧ s ≠ t ∧
        u ≠ t.2 ∧ catalogFace s r = catalogFace t u := by
  decide +kernel

theorem activeGridFace_catalog {N : ℕ} {n : GridVertex N}
    (ta : VertexStar n) (r : Fin 4) (ha : activeGridFace ta.val.1 r) :
    activeFace (boundaryTag n) (starCatalog ta) r := by
  intro j hj
  have hb : (n j).val = 0 ∨ (n j).val = N := by
    by_contra hn
    push Not at hn
    exact hj (by simp only [boundaryTag, if_neg hn.1, if_neg hn.2])
  rcases hb with hn | hn
  · obtain ⟨m, hm, hneq⟩ := (ha j).1
    obtain ⟨a, har, he⟩ := Finset.mem_image.mp hm
    subst m
    refine ⟨a, (Finset.mem_erase.mp har).1, ?_⟩
    rw [← catalog_displacement ta a j]
    change ((gridVertexOfTet ta.val.1 a j).val : ℤ) ≠ 0 at hneq
    omega
  · obtain ⟨m, hm, hneq⟩ := (ha j).2
    obtain ⟨a, har, he⟩ := Finset.mem_image.mp hm
    subst m
    refine ⟨a, (Finset.mem_erase.mp har).1, ?_⟩
    rw [← catalog_displacement ta a j]
    change ((gridVertexOfTet ta.val.1 a j).val : ℤ) ≠ (N : ℤ) at hneq
    omega

theorem activeGridFace_has_star_neighbor {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : activeGridFace t r) :
    ∃ (tb : VertexStar (faceAnchor t r)) (s : Fin 4),
      t ≠ tb.val.1 ∧ s ≠ tb.val.2 ∧ gridFace t r = gridFace tb.val.1 s := by
  let ta := anchoredOwner t r
  have hc := catalog_active_has_neighbor (boundaryTag (faceAnchor t r)) (starCatalog ta) r
    (starCatalog_admissible hN ta)
    (by simpa only [starCatalog_cut] using anchoredOwner_omitted_ne t r)
    (activeGridFace_catalog ta r ha)
  obtain ⟨c, s, hadm, hne, hs, hface⟩ := hc
  let cs : {z : State // tagAdmissible (boundaryTag (faceAnchor t r)) z} :=
    ⟨catalogEquiv c, (catalog_admissible_iff _ _).mpr hadm⟩
  let tb := (actualStateEquiv hN (faceAnchor t r)).symm cs
  have hstate : (tb.val.1.2, tb.val.2) = catalogEquiv c := by
    exact congrArg Subtype.val ((actualStateEquiv hN (faceAnchor t r)).apply_symm_apply cs)
  have hcat : starCatalog tb = c := by
    unfold starCatalog
    rw [hstate, Equiv.symm_apply_apply]
  refine ⟨tb, s, ?_, ?_, ?_⟩
  · intro h
    apply hne
    have hstar : ta = tb := starTet_injective (faceAnchor t r) h
    rw [hstar, hcat]
  · simpa only [← hcat, starCatalog_cut] using hs
  · apply (Finset.image_injective (displacement_injective (faceAnchor t r))).eq_iff.mp
    change (gridFace ta.val.1 r).image (displacement (faceAnchor t r)) = _
    rw [displaced_catalogFace ta r, displaced_catalogFace tb s, hcat]
    exact hface

theorem activeGridFace_has_neighbor {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : activeGridFace t r) :
    ∃ (u : Tet N) (s : Fin 4), t ≠ u ∧ gridFace t r = gridFace u s := by
  obtain ⟨tb, s, hne, _, he⟩ := activeGridFace_has_star_neighbor hN t r ha
  exact ⟨tb.val.1, s, hne, he⟩

theorem gridFace_omitted_not_mem {N : ℕ} (t : Tet N) (r : Fin 4) :
    gridVertexOfTet t r ∉ gridFace t r := by
  intro hm
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
  exact (Finset.mem_erase.mp ha).1 (gridVertexOfTet_injective t he)

theorem gridFace_index_injective {N : ℕ} (t : Tet N) : Function.Injective (gridFace t) := by
  intro r s he
  by_contra hne
  have hm : gridVertexOfTet t r ∈ gridFace t s :=
    Finset.mem_image.mpr ⟨r, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, rfl⟩
  rw [← he] at hm
  exact gridFace_omitted_not_mem t r hm

theorem other_owner_unique {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : activeGridFace t r) (u v : Tet N) (s w : Fin 4)
    (htu : t ≠ u) (htv : t ≠ v)
    (hu : gridFace t r = gridFace u s) (hv : gridFace t r = gridFace v w) :
    u = v ∧ s = w := by
  obtain ⟨tb, b, hne, _, he⟩ := activeGridFace_has_star_neighbor hN t r ha
  have howner (z : Tet N) (a : Fin 4) (htz : t ≠ z) (hz : gridFace t r = gridFace z a) :
      z = tb.val.1 := by
    have hs : gridFace t r ⊆ gridVertices z := by
      rw [hz]
      exact gridFace_subset_vertices z a
    have ht := containing_face_is_owner (anchoredOwner t r) tb r b
      (anchoredOwner_omitted_ne t r) hne he z hs
    exact ht.resolve_left htz.symm
  have heq : u = v := (howner u s htu hu).trans (howner v w htv hv).symm
  refine ⟨heq, ?_⟩
  apply gridFace_index_injective v
  rw [← hv, ← heq, ← hu]

end FreudenthalSVLean.InteriorFaceCoverage
