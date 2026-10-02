import FreudenthalSVLean.VertexStarConnectivity

/-!
# Face-graph transport under vertex-star symmetries

For manuscript Lemmas `vertex-coverage` and `vertex-local`, the equality
of geometric three-vertex faces is preserved by coordinate permutation
and central inversion.  The graph isomorphisms below transport the checked
canonical rooted trees to every boundary word.  Connectivity therefore
follows from the actual relative geometry, rather than from equal graph
sizes or an unproved identification of graph labels.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.MeshCoverage
open SimpleGraph

noncomputable section

namespace FreudenthalSVLean.VertexStarGraphTransport

def relativeFace (s : State) (r : Vertex) : Finset (Coordinate → ℤ) :=
  (Finset.univ.erase r).image (relativeVertex s)

def stateAdjacent (s t : State) : Prop :=
  s ≠ t ∧ ∃ r u : Vertex, r ≠ s.2 ∧ u ≠ t.2 ∧ relativeFace s r = relativeFace t u

theorem stateAdjacent_symm {s t : State} (h : stateAdjacent s t) : stateAdjacent t s := by
  obtain ⟨hne, r, u, hr, hu, he⟩ := h
  exact ⟨hne.symm, u, r, hu, hr, he.symm⟩

def stateGraph (b : Coordinate → Fin 3) : SimpleGraph {s : State // tagAdmissible b s} where
  Adj s t := stateAdjacent s.val t.val
  symm := ⟨fun _ _ h => stateAdjacent_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem catalog_relativeFace (s : CatalogState) (r : Vertex) :
    relativeFace (catalogEquiv s) r = catalogFace s r := by
  unfold relativeFace catalogFace
  congr 1
  funext a
  exact relative_catalog s a

theorem catalog_stateAdjacent (s t : CatalogState) :
    stateAdjacent (catalogEquiv s) (catalogEquiv t) ↔ faceAdjacent s t := by
  simp only [stateAdjacent, faceAdjacent, catalog_relativeFace,
    catalogEquiv.injective.ne_iff]
  rfl

def catalogGraphIso (b : Coordinate → Fin 3) : catalogGraph b ≃g stateGraph b where
  toEquiv := admissibleCatalogEquiv b
  map_rel_iff' := by
    intro s t
    exact catalog_stateAdjacent s.val t.val

theorem transformVertex_involutive (flip : Bool) : Function.Involutive (transformVertex flip) := by
  cases flip
  · exact fun _ => rfl
  · exact Fin.rev_rev

theorem transformVertex_injective (flip : Bool) : Function.Injective (transformVertex flip) :=
  (transformVertex_involutive flip).injective

theorem transformVertex_surjective (flip : Bool) : Function.Surjective (transformVertex flip) :=
  (transformVertex_involutive flip).surjective

theorem transformVertex_univ (flip : Bool) :
    (Finset.univ : Finset Vertex).image (transformVertex flip) = Finset.univ := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact transformVertex_surjective flip a

theorem transformState_cut (π : Equiv.Perm Coordinate) (flip : Bool) (s : State) :
    (transformState π flip s).2 = transformVertex flip s.2 := by
  cases flip <;> rfl

theorem transformState_injective (π : Equiv.Perm Coordinate) (flip : Bool) :
    Function.Injective (transformState π flip) := by
  intro s t h
  apply (transformEquiv π flip).injective
  simpa only [transformEquiv_apply] using h

theorem transformDirection_injective (π : Equiv.Perm Coordinate) (flip : Bool) :
    Function.Injective (transformDirection π flip) := by
  intro d e h
  funext j
  have he := congrFun h (π j)
  cases flip <;> simpa [transformDirection] using he

theorem transform_relativeFace (π : Equiv.Perm Coordinate) (flip : Bool) (s : State)
    (r : Vertex) :
    relativeFace (transformState π flip s) (transformVertex flip r) =
      (relativeFace s r).image (transformDirection π flip) := by
  classical
  calc
    _ = ((Finset.univ.erase r).image (transformVertex flip)).image
        (relativeVertex (transformState π flip s)) := by
      rw [Finset.image_erase (transformVertex_injective flip), transformVertex_univ]
      rfl
    _ = (Finset.univ.erase r).image
        (fun a => transformDirection π flip (relativeVertex s a)) := by
      rw [Finset.image_image]
      congr 1
      funext a
      exact transform_relativeVertex π flip s a
    _ = _ := by rw [relativeFace, Finset.image_image]; rfl

theorem transform_stateAdjacent_iff (π : Equiv.Perm Coordinate) (flip : Bool) (s t : State) :
    stateAdjacent (transformState π flip s) (transformState π flip t) ↔ stateAdjacent s t := by
  constructor
  · rintro ⟨hne, r, u, hr, hu, he⟩
    obtain ⟨r, rfl⟩ := transformVertex_surjective flip r
    obtain ⟨u, rfl⟩ := transformVertex_surjective flip u
    rw [transformState_cut] at hr hu
    rw [transform_relativeFace, transform_relativeFace] at he
    exact ⟨fun h => hne (congrArg (transformState π flip) h), r, u,
      fun h => hr (congrArg (transformVertex flip) h),
      fun h => hu (congrArg (transformVertex flip) h),
      Finset.image_injective (transformDirection_injective π flip) he⟩
  · rintro ⟨hne, r, u, hr, hu, he⟩
    refine ⟨(transformState_injective π flip).ne hne,
      transformVertex flip r, transformVertex flip u, ?_, ?_, ?_⟩
    · rw [transformState_cut]
      exact (transformVertex_injective flip).ne hr
    · rw [transformState_cut]
      exact (transformVertex_injective flip).ne hu
    · rw [transform_relativeFace, transform_relativeFace, he]

def symmetryGraphIso (π : Equiv.Perm Coordinate) (flip : Bool) (b : Coordinate → Fin 3) :
    stateGraph b ≃g stateGraph (transformTags π flip b) where
  toEquiv := transformAdmissibleEquiv π flip b
  map_rel_iff' := by
    intro s t
    change stateAdjacent (transformEquiv π flip s.val) (transformEquiv π flip t.val) ↔ _
    simp only [transformEquiv_apply, transform_stateAdjacent_iff]
    rfl

/-- Every boundary word has a connected graph of geometric faces through
the marked vertex.  The finite trees enter only after a proved graph
isomorphism under the star's geometric symmetries. -/
theorem stateGraph_connected (b : Coordinate → Fin 3) : (stateGraph b).Connected := by
  obtain ⟨c, r, flip, htags, _⟩ := canonical_star_symmetry b
  have hc : (stateGraph (canonicalTags c)).Connected :=
    (catalogGraphIso (canonicalTags c)).connected_iff.mp (canonical_connected c)
  apply (symmetryGraphIso (orderPerm r).symm flip b).connected_iff.mpr
  exact htags ▸ hc

end FreudenthalSVLean.VertexStarGraphTransport
