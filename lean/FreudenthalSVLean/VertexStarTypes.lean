import FreudenthalSVLean.VertexStarCoverage
import FreudenthalSVLean.MeshCoverage

/-!
# Boundary words and the six vertex valences

For manuscript Lemma `vertex-coverage`, the arbitrary-mesh star equivalence
is followed by a small, explicit classification of the three boundary
tags.  The six permutations are listed with explicit inverse coordinate
maps, so every finite computation below is evaluated by the Lean kernel.
The classifications concern vertex incidences and boundary words; symmetry
of active-edge sets and connectedness of the face-adjacency graph are not
asserted here.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.MeshCoverage

namespace FreudenthalSVLean.VertexStarTypes

abbrev CatalogState := Fin 6 × Vertex

/-- The inverse index for each of the six coordinate orders. -/
def inverseOrder (r : Fin 6) : Fin 6 := ![0, 1, 2, 4, 3, 5] r

def catalogRank (r : Fin 6) (j : Coordinate) : Coordinate :=
  orderMap (inverseOrder r) j

theorem orderMap_rank : ∀ (r : Fin 6) (j : Coordinate),
    orderMap r (catalogRank r j) = j := by
  decide +kernel

theorem orderPerm_symm_eq_rank (r : Fin 6) (j : Coordinate) :
    (orderPerm r).symm j = catalogRank r j := by
  apply (orderPerm r).injective
  exact (orderPerm r).apply_symm_apply j |>.trans (orderMap_rank r j).symm

theorem orderMap_injective : Function.Injective orderMap := by
  decide +kernel

theorem orderPerm_injective : Function.Injective orderPerm := by
  intro r s h
  apply orderMap_injective
  exact congrArg (fun e : Equiv.Perm Coordinate => e.toFun) h

theorem orderPerm_bijective : Function.Bijective orderPerm := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨orderPerm_injective, ?_⟩
  simp [Fintype.card_perm]
  norm_num

noncomputable def catalogEquiv : CatalogState ≃ State :=
  Equiv.prodCongr (Equiv.ofBijective orderPerm orderPerm_bijective) (Equiv.refl Vertex)

def catalogPrefix (s : CatalogState) (j : Coordinate) : ℕ :=
  if (catalogRank s.1 j).val < s.2.val then 1 else 0

theorem prefix_catalog (s : CatalogState) (j : Coordinate) :
    prefixMask (catalogEquiv s) j = catalogPrefix s j := by
  change (if ((orderPerm s.1).symm j).val < s.2.val then 1 else 0) = _
  rw [orderPerm_symm_eq_rank]
  rfl

def catalogAdmissible (b : Coordinate → Fin 3) (s : CatalogState) : Prop :=
  ∀ j : Coordinate, (b j = 0 → catalogPrefix s j = 0) ∧
    (b j = 2 → catalogPrefix s j = 1)

instance (b : Coordinate → Fin 3) (s : CatalogState) :
    Decidable (catalogAdmissible b s) :=
  inferInstanceAs (Decidable (∀ j : Coordinate,
    (b j = 0 → catalogPrefix s j = 0) ∧ (b j = 2 → catalogPrefix s j = 1)))

theorem catalog_admissible_iff (b : Coordinate → Fin 3) (s : CatalogState) :
    tagAdmissible b (catalogEquiv s) ↔ catalogAdmissible b s := by
  simp only [tagAdmissible, catalogAdmissible, prefix_catalog]

noncomputable def admissibleCatalogEquiv (b : Coordinate → Fin 3) :
    {s : CatalogState // catalogAdmissible b s} ≃ {s : State // tagAdmissible b s} := by
  classical
  exact (Equiv.subtypeEquivRight (fun s : CatalogState => (catalog_admissible_iff b s).symm)).trans
    (catalogEquiv.subtypeEquiv (fun s : CatalogState => Iff.rfl))

def canonicalTags (c : Fin 6) : Coordinate → Fin 3 :=
  ![![0, 0, 2], ![0, 1, 2], ![0, 0, 0],
    ![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] c

def canonicalValence (c : Fin 6) : ℕ := ![2, 4, 6, 8, 12, 24] c

def tagTransform (b : Coordinate → Fin 3) (r : Fin 6) (flip : Bool) :
    Coordinate → Fin 3 :=
  fun j => if flip then Fin.rev (b (orderMap r j)) else b (orderMap r j)

/-- Every boundary word is a coordinate permutation, possibly followed
by central inversion, of one of the six location types. -/
theorem tag_words_covered : ∀ b : Coordinate → Fin 3,
    ∃ (c r : Fin 6) (flip : Bool), tagTransform b r flip = canonicalTags c := by
  decide +kernel

theorem canonical_valences : ∀ c : Fin 6,
    Fintype.card {s : CatalogState // catalogAdmissible (canonicalTags c) s} =
      canonicalValence c := by
  decide +kernel

/-- This finite statement concerns all twenty-seven boundary words,
not a sample of vertices on a mesh of a particular size. -/
theorem boundary_word_valences : ∀ b : Coordinate → Fin 3,
    ∃ c : Fin 6, Fintype.card {s : CatalogState // catalogAdmissible b s} =
      canonicalValence c := by
  decide +kernel

/-- Actual geometric incidences on every positive mesh size have one of
the six listed valences.  Coverage is the explicit mesh/state equivalence,
not an extrapolation of a finite sample. -/
theorem geometric_star_valences {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    ∃ c : Fin 6,
      Fintype.card {ta : Tet N × Vertex // vertex ta.1 ta.2 = gridPoint n} =
        canonicalValence c := by
  classical
  obtain ⟨c, hc⟩ := boundary_word_valences (boundaryTag n)
  refine ⟨c, ?_⟩
  calc
    _ = Fintype.card {s : State // admissible n s} :=
      Fintype.card_congr (geometricStarEquivState hN n)
    _ = Fintype.card {s : State // tagAdmissible (boundaryTag n) s} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (admissible_iff_boundaryTags hN n))
    _ = Fintype.card {s : CatalogState // catalogAdmissible (boundaryTag n) s} :=
      (Fintype.card_congr (admissibleCatalogEquiv (boundaryTag n))).symm
    _ = canonicalValence c := hc

end FreudenthalSVLean.VertexStarTypes
