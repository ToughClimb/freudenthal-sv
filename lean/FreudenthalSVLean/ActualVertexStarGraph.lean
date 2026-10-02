import FreudenthalSVLean.VertexStarGraphTransport

/-!
# Connected face-adjacency graphs of actual arbitrary-mesh vertex stars

For manuscript Lemma `vertex-local`, two distinct tetrahedra in a vertex
star are adjacent when they share a three-vertex face containing the
central vertex.  Here that condition is expressed using actual grid nodes.
Integer displacement from the central vertex is injective and sends these
faces exactly to the universal relative faces.  The resulting graph
isomorphism transfers the proved boundary-word connectivity to every mesh
size.  No geometric graph identification is left as an assumption.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexStarGraphTransport
open SimpleGraph

noncomputable section

namespace FreudenthalSVLean.ActualVertexStarGraph

def gridFace {N : ℕ} (t : Tet N) (r : Vertex) : Finset (GridVertex N) :=
  (Finset.univ.erase r).image (gridVertexOfTet t)

theorem gridFace_card {N : ℕ} (t : Tet N) (r : Vertex) : (gridFace t r).card = 3 := by
  rw [gridFace, Finset.card_image_of_injective _ (gridVertexOfTet_injective t)]
  simp

def physicalFace {N : ℕ} (t : Tet N) (r : Vertex) : Finset Space :=
  (gridFace t r).image gridPoint

theorem physicalFace_vertices {N : ℕ} (t : Tet N) (r : Vertex) :
    physicalFace t r = (Finset.univ.erase r).image (vertex t) := by
  unfold physicalFace gridFace
  rw [Finset.image_image]
  congr 1
  funext a
  exact gridVertexOfTet_point t a

theorem physicalFace_card {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex) :
    (physicalFace t r).card = 3 := by
  rw [physicalFace, Finset.card_image_of_injective _ (gridPoint_injective hN)]
  exact gridFace_card t r

theorem sharedFace_iff {N : ℕ} (hN : 0 < N) (t u : Tet N) (r s : Vertex) :
    gridFace t r = gridFace u s ↔ physicalFace t r = physicalFace u s := by
  exact (Finset.image_injective (gridPoint_injective hN)).eq_iff.symm

theorem integerGrid_injective {N : ℕ} : Function.Injective (integerGrid (N := N)) := by
  intro n m h
  funext j
  apply Fin.ext
  have he := congrFun h j
  change ((n j).val : ℤ) = ((m j).val : ℤ) at he
  exact_mod_cast he

def displacement {N : ℕ} (n m : GridVertex N) : Coordinate → ℤ :=
  integerGrid m - integerGrid n

theorem displacement_injective {N : ℕ} (n : GridVertex N) :
    Function.Injective (displacement n) := by
  intro m l h
  exact integerGrid_injective (sub_left_inj.mp h)

theorem displaced_face {N : ℕ} (n : GridVertex N) (ta : VertexStar n) (r : Vertex) :
    (gridFace ta.val.1 r).image (displacement n) =
      relativeFace (ta.val.1.2, ta.val.2) r := by
  unfold gridFace relativeFace
  rw [Finset.image_image]
  congr 1
  funext a j
  exact grid_displacement n ta a j

theorem starTet_injective {N : ℕ} (n : GridVertex N) :
    Function.Injective (fun ta : VertexStar n => ta.val.1) := by
  intro ta tb h
  change ta.val.1 = tb.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply gridVertexOfTet_injective ta.val.1
  rw [ta.property, h, tb.property]

theorem starState_injective {N : ℕ} (n : GridVertex N) :
    Function.Injective (fun ta : VertexStar n => (ta.val.1.2, ta.val.2)) := by
  intro ta tb h
  apply (starStateEquiv n).injective
  exact Subtype.ext h

def actualAdjacent {N : ℕ} (n : GridVertex N) (ta tb : VertexStar n) : Prop :=
  ta.val.1 ≠ tb.val.1 ∧ ∃ r u : Vertex,
    r ≠ ta.val.2 ∧ u ≠ tb.val.2 ∧ gridFace ta.val.1 r = gridFace tb.val.1 u

theorem actualAdjacent_symm {N : ℕ} {n : GridVertex N} {ta tb : VertexStar n}
    (h : actualAdjacent n ta tb) : actualAdjacent n tb ta := by
  obtain ⟨hne, r, u, hr, hu, he⟩ := h
  exact ⟨hne.symm, u, r, hu, hr, he.symm⟩

def actualGraph {N : ℕ} (n : GridVertex N) : SimpleGraph (VertexStar n) where
  Adj := actualAdjacent n
  symm := ⟨fun _ _ h => actualAdjacent_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def actualStateEquiv {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    VertexStar n ≃ {s : State // tagAdmissible (boundaryTag n) s} :=
  (starStateEquiv n).trans (Equiv.subtypeEquivRight (admissible_iff_boundaryTags hN n))

theorem actualAdjacent_iff_relative {N : ℕ} (n : GridVertex N) (ta tb : VertexStar n) :
    actualAdjacent n ta tb ↔
      stateAdjacent (ta.val.1.2, ta.val.2) (tb.val.1.2, tb.val.2) := by
  have hne : ta.val.1 ≠ tb.val.1 ↔
      (ta.val.1.2, ta.val.2) ≠ (tb.val.1.2, tb.val.2) :=
    (starTet_injective n).ne_iff.trans (starState_injective n).ne_iff.symm
  have hf (r u : Vertex) : gridFace ta.val.1 r = gridFace tb.val.1 u ↔
      relativeFace (ta.val.1.2, ta.val.2) r = relativeFace (tb.val.1.2, tb.val.2) u := by
    rw [← displaced_face n ta r, ← displaced_face n tb u]
    exact (Finset.image_injective (displacement_injective n)).eq_iff.symm
  simp only [actualAdjacent, stateAdjacent, hne, hf]

def actualGraphIso {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    actualGraph n ≃g stateGraph (boundaryTag n) where
  toEquiv := actualStateEquiv hN n
  map_rel_iff' := by
    intro ta tb
    exact (actualAdjacent_iff_relative n ta tb).symm

/-- Every interior and boundary vertex star has a connected geometric
face-adjacency graph on every positive `N`, including `N=1,2`. -/
theorem actualGraph_connected {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    (actualGraph n).Connected :=
  (actualGraphIso hN n).connected_iff.mpr (stateGraph_connected (boundaryTag n))

end FreudenthalSVLean.ActualVertexStarGraph
