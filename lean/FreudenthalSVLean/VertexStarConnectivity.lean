import FreudenthalSVLean.VertexEdgeCoverage
import FreudenthalSVLean.MeanRoutingAlgebra

/-!
# Certified face connectivity of the six canonical vertex stars

For manuscript Lemma `vertex-local`, a face adjacency is equality of the
three relative geometric vertices of faces containing the marked vertex.
Each of the six canonical graphs is supplied with a rooted tree.  The
kernel verifies admissibility, actual face adjacency, and strictly
decreasing integer depth for every non-root vertex.  An ordinary induction
then proves connectedness.  The table is a finite witness for geometry,
not a rank test and not an assumed connectivity oracle.

Transport to arbitrary boundary words and actual mesh stars is performed
separately; this module's canonical connectedness alone is not used as a
claim of arbitrary-mesh coverage.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open SimpleGraph

namespace FreudenthalSVLean.VertexStarConnectivity

def catalogFace (s : CatalogState) (r : Vertex) : Finset (Coordinate → ℤ) :=
  (Finset.univ.erase r).image (catalogRelative s)

def faceAdjacent (s t : CatalogState) : Prop :=
  s ≠ t ∧ ∃ r u : Vertex, r ≠ s.2 ∧ u ≠ t.2 ∧ catalogFace s r = catalogFace t u

instance (s t : CatalogState) : Decidable (faceAdjacent s t) :=
  inferInstanceAs (Decidable (s ≠ t ∧ ∃ r u : Vertex,
    r ≠ s.2 ∧ u ≠ t.2 ∧ catalogFace s r = catalogFace t u))

theorem faceAdjacent_symm {s t : CatalogState} (h : faceAdjacent s t) :
    faceAdjacent t s := by
  obtain ⟨hne, r, u, hr, hu, he⟩ := h
  exact ⟨hne.symm, u, r, hu, hr, he.symm⟩

def catalogGraph (b : Coordinate → Fin 3) :
    SimpleGraph {s : CatalogState // catalogAdmissible b s} where
  Adj s t := faceAdjacent s.val t.val
  symm := ⟨fun _ _ h => faceAdjacent_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def catalogIndex (s : CatalogState) : Fin 24 :=
  ⟨4 * s.1.val + s.2.val, by have := s.1.isLt; have := s.2.isLt; omega⟩

def catalogOfIndex (i : Fin 24) : CatalogState :=
  (⟨i.val / 4, by have := i.isLt; omega⟩,
    ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩)

theorem catalogOfIndex_index (s : CatalogState) :
    catalogOfIndex (catalogIndex s) = s := by
  apply Prod.ext <;> apply Fin.ext
  · have := s.2.isLt
    simp only [catalogOfIndex, catalogIndex]
    omega
  · have := s.2.isLt
    simp only [catalogOfIndex, catalogIndex]
    omega

def rootIndex (c : Fin 6) : Fin 24 := ![17, 14, 0, 0, 0, 0] c

def parentIndex (c : Fin 6) : Fin 24 → Fin 24 :=
  ![![17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17],
    ![14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,17,14,14],
    ![0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,4,0,0,0,16,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,4,0,0,0,16,8,0,0],
    ![0,0,0,0,0,0,0,0,0,4,0,0,8,9,17,0,4,0,0,0,16,8,9,0],
    ![0,12,13,14,0,20,21,22,0,4,2,6,8,9,17,18,4,0,1,2,16,8,9,10]] c

def treeDepth (c : Fin 6) : Fin 24 → ℕ :=
  ![![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,2,1,0],
    ![0,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,2,0,0,0,3,0,0,0],
    ![0,0,0,0,1,0,0,0,1,0,0,0,2,0,0,0,2,1,0,0,3,2,0,0],
    ![0,0,0,0,1,0,0,0,1,2,0,0,2,3,2,0,2,1,0,0,3,2,3,0],
    ![0,3,4,3,1,4,3,4,1,2,5,4,2,3,2,5,2,1,4,5,3,2,3,6]] c

def rootState (c : Fin 6) : CatalogState := catalogOfIndex (rootIndex c)

def parentState (c : Fin 6) (s : CatalogState) : CatalogState :=
  catalogOfIndex (parentIndex c (catalogIndex s))

theorem root_admissible : ∀ c : Fin 6, catalogAdmissible (canonicalTags c) (rootState c) := by
  decide +kernel

/-- Every non-root member has a face-sharing parent of smaller depth.
All rows, including inadmissible candidate states, are quantified explicitly. -/
theorem tree_verified : ∀ (c : Fin 6) (s : CatalogState),
    catalogAdmissible (canonicalTags c) s →
      s = rootState c ∨
        (catalogAdmissible (canonicalTags c) (parentState c s) ∧
          faceAdjacent s (parentState c s) ∧
          treeDepth c (catalogIndex (parentState c s)) < treeDepth c (catalogIndex s)) := by
  decide +kernel

def root (c : Fin 6) : {s : CatalogState // catalogAdmissible (canonicalTags c) s} :=
  ⟨rootState c, root_admissible c⟩

theorem reaches_root (c : Fin 6)
    (s : {s : CatalogState // catalogAdmissible (canonicalTags c) s}) :
    (catalogGraph (canonicalTags c)).Reachable s (root c) := by
  suffices h : ∀ n : ℕ, ∀ t : {s : CatalogState // catalogAdmissible (canonicalTags c) s},
      treeDepth c (catalogIndex t.val) = n →
        (catalogGraph (canonicalTags c)).Reachable t (root c) from
    h _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t ht
    obtain he | ⟨ha, hadj, hlt⟩ := tree_verified c t.val t.property
    · have heq : t = root c := Subtype.ext he
      subst t
      exact Reachable.rfl
    · let p : {s : CatalogState // catalogAdmissible (canonicalTags c) s} :=
        ⟨parentState c t.val, ha⟩
      have hp := ih (treeDepth c (catalogIndex p.val)) (ht ▸ hlt) p rfl
      exact (show (catalogGraph (canonicalTags c)).Adj t p from hadj).reachable.trans hp

theorem canonical_connected (c : Fin 6) : (catalogGraph (canonicalTags c)).Connected where
  preconnected s t := (reaches_root c s).trans (reaches_root c t).symm
  nonempty := ⟨root c⟩

end FreudenthalSVLean.VertexStarConnectivity
