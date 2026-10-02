import FreudenthalSVLean.RawVertexField

/-!
# Exact arbitrary-mesh edge-star coverage

For manuscript Lemma `edge-coverage` and the seven-row incidence table,
an oriented edge star is obtained by fixing the second vertex in the
already proved arbitrary-mesh vertex-star equivalence.  This gives an
explicit equivalence with a finite set of chain states and endpoint
indices, depending only on the first endpoint's boundary word and the
integer endpoint displacement.  It is not an extrapolation from a
particular mesh size.

An increasing nontrivial chain edge has one of the seven nonzero binary
displacements.  The boundary-word calculation gives the seven geometric
incidence valences and proves a uniform six-element star bound.  These
statements classify incidence counts; coefficient lifting and face
adjacency are proved separately.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.RawVertexField

noncomputable section

namespace FreudenthalSVLean.ActualEdgeCoverage

abbrev ActualEdgeStar {N : ℕ} (a b : GridVertex N) :=
  {ta : VertexStar a × Vertex // gridVertexOfTet ta.1.val.1 ta.2 = b}

def CatalogEdgePredicate (b : BoundaryWord) (d : Coordinate → ℤ)
    (sa : CatalogState × Vertex) : Prop :=
  catalogAdmissible b sa.1 ∧ catalogRelative sa.1 sa.2 = d

instance (b : BoundaryWord) (d : Coordinate → ℤ) (sa : CatalogState × Vertex) :
    Decidable (CatalogEdgePredicate b d sa) :=
  inferInstanceAs (Decidable (catalogAdmissible b sa.1 ∧ catalogRelative sa.1 sa.2 = d))

abbrev CatalogEdge (b : BoundaryWord) (d : Coordinate → ℤ) :=
  {sa : CatalogState × Vertex // CatalogEdgePredicate b d sa}

def catalogEdgeSet (b : BoundaryWord) (d : Coordinate → ℤ) : Finset (CatalogState × Vertex) :=
  Finset.univ.filter (CatalogEdgePredicate b d)

theorem displacement_catalogRelative {N : ℕ} {a : GridVertex N}
    (ta : VertexStar a) (l : Vertex) :
    displacement a (gridVertexOfTet ta.val.1 l) = catalogRelative (starCatalog ta) l := by
  funext j
  exact catalog_displacement ta l j

theorem endpoint_iff_relative {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (ta : VertexStar a) (l : Vertex) :
    gridVertexOfTet ta.val.1 l = b ↔
      catalogRelative (catalogIncidenceEquiv hN a ta).val l = displacement a b := by
  rw [catalogIncidenceEquiv_val, ← displacement_catalogRelative]
  exact (displacement_injective a).eq_iff.symm

/-- The forward and inverse maps reconstruct actual mesh elements;
the finite set contains neither missing nor spurious edge incidences. -/
def edgeCatalogEquiv {N : ℕ} (hN : 0 < N) (a b : GridVertex N) :
    ActualEdgeStar a b ≃ CatalogEdge (boundaryTag a) (displacement a b) where
  toFun x := ⟨((catalogIncidenceEquiv hN a x.val.1).val, x.val.2),
    (catalogIncidenceEquiv hN a x.val.1).property,
    (endpoint_iff_relative hN a b x.val.1 x.val.2).mp x.property⟩
  invFun x := ⟨((catalogIncidenceEquiv hN a).symm ⟨x.val.1, x.property.1⟩, x.val.2), by
    apply (endpoint_iff_relative hN a b _ _).mpr
    simpa only [Equiv.apply_symm_apply] using x.property.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (catalogIncidenceEquiv hN a).symm_apply_apply x.val.1
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((catalogIncidenceEquiv hN a).apply_symm_apply
        ⟨x.val.1, x.property.1⟩)
    · rfl

def positiveDirection (r : Fin 7) : Coordinate → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0],
    ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]] r

theorem positive_catalog_directions : ∀ (s : CatalogState) (l : Vertex),
    catalogRelative s l ≠ 0 → (∀ j, 0 ≤ catalogRelative s l j) →
      ∃ r : Fin 7, catalogRelative s l = positiveDirection r := by
  decide +kernel

theorem increasing_edge_direction {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (horder : ∀ j, (a j).val ≤ (b j).val) (x : ActualEdgeStar a b) :
    ∃ r : Fin 7, displacement a b = positiveDirection r := by
  have he : catalogRelative (starCatalog x.val.1) x.val.2 = displacement a b := by
    rw [← displacement_catalogRelative, x.property]
  have hn : catalogRelative (starCatalog x.val.1) x.val.2 ≠ 0 := by
    intro hz
    have hd : displacement a b = displacement a a := by simpa [displacement] using he.symm.trans hz
    exact hab ((displacement_injective a hd).symm)
  have ho : ∀ j, 0 ≤ catalogRelative (starCatalog x.val.1) x.val.2 j := by
    intro j
    rw [he]
    change (0 : ℤ) ≤ ((b j).val : ℤ) - ((a j).val : ℤ)
    exact sub_nonneg.mpr (by exact_mod_cast horder j)
  obtain ⟨r, hr⟩ := positive_catalog_directions (starCatalog x.val.1) x.val.2 hn ho
  exact ⟨r, he.symm.trans hr⟩

def validPositiveTags (b : BoundaryWord) (r : Fin 7) : Prop :=
  ∀ j, positiveDirection r j = 1 → b j ≠ 2

instance (b : BoundaryWord) (r : Fin 7) : Decidable (validPositiveTags b r) :=
  inferInstanceAs (Decidable (∀ j, positiveDirection r j = 1 → b j ≠ 2))

def directionSupport (r : Fin 7) : Finset Coordinate :=
  Finset.univ.filter (fun j => positiveDirection r j = 1)

def containingBoundaryPlanes (b : BoundaryWord) (r : Fin 7) : Finset Coordinate :=
  Finset.univ.filter (fun j => positiveDirection r j = 0 ∧ b j ≠ 1)

/-- Ordering: one-tetrahedron box edge, two-tetrahedron box edge,
boundary face diagonal, boundary-face axis edge, interior face diagonal,
body diagonal, interior axis edge. -/
def incidenceKind (b : BoundaryWord) (r : Fin 7) : Fin 7 :=
  if (directionSupport r).card = 3 then 5
  else if (directionSupport r).card = 2 then
    if (containingBoundaryPlanes b r).card = 0 then 4 else 2
  else if (containingBoundaryPlanes b r).card = 0 then 6
  else if (containingBoundaryPlanes b r).card = 1 then 3
  else if ∃ i j : Coordinate, positiveDirection r i = 0 ∧ positiveDirection r j = 0 ∧
      b i = 0 ∧ b j = 2 then 0 else 1

def incidenceValence (c : Fin 7) : ℕ := ![1, 2, 2, 3, 4, 6, 6] c

theorem incidenceValence_pos : ∀ c : Fin 7, 0 < incidenceValence c := by decide +kernel

instance (c : Fin 7) : NeZero (incidenceValence c) :=
  ⟨Nat.ne_of_gt (incidenceValence_pos c)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- All twenty-seven boundary words and all seven increasing directions
are checked.  No sample-mesh extrapolation occurs in this theorem. -/
theorem catalog_edge_valences : ∀ (b : BoundaryWord) (r : Fin 7), validPositiveTags b r →
    (catalogEdgeSet b (positiveDirection r)).card = incidenceValence (incidenceKind b r) := by
  decide +kernel

theorem incidenceValence_le_six : ∀ c : Fin 7, incidenceValence c ≤ 6 := by
  decide +kernel

theorem actual_positive_tags {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (r : Fin 7)
    (hd : displacement a b = positiveDirection r) : validPositiveTags (boundaryTag a) r := by
  intro j hj hu
  have ha := (boundaryTag_upper_iff hN a j).mp hu
  have he := congrFun hd j
  change ((b j).val : ℤ) - ((a j).val : ℤ) = positiveDirection r j at he
  rw [ha, hj] at he
  have hb : (b j).val ≤ N := Nat.le_of_lt_succ (b j).isLt
  omega

theorem geometric_edge_valence {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (r : Fin 7) (hd : displacement a b = positiveDirection r) :
    Fintype.card (ActualEdgeStar a b) = incidenceValence (incidenceKind (boundaryTag a) r) := by
  classical
  calc
    _ = Fintype.card (CatalogEdge (boundaryTag a) (displacement a b)) :=
      Fintype.card_congr (edgeCatalogEquiv hN a b)
    _ = (catalogEdgeSet (boundaryTag a) (positiveDirection r)).card := by
      rw [hd]
      simp only [CatalogEdge, catalogEdgeSet, Fintype.card_subtype]
    _ = _ := catalog_edge_valences (boundaryTag a) r (actual_positive_tags hN a b r hd)

theorem geometric_increasing_edge_bound {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (hab : a ≠ b) (horder : ∀ j, (a j).val ≤ (b j).val) (x : ActualEdgeStar a b) :
    Fintype.card (ActualEdgeStar a b) ≤ 6 := by
  obtain ⟨r, hd⟩ := increasing_edge_direction a b hab horder x
  rw [geometric_edge_valence hN a b r hd]
  exact incidenceValence_le_six _

def reverseEdgeStar {N : ℕ} (a b : GridVertex N) : ActualEdgeStar a b ≃ ActualEdgeStar b a where
  toFun x := ⟨(⟨(x.val.1.val.1, x.val.2), x.property⟩, x.val.1.val.2), x.val.1.property⟩
  invFun x := ⟨(⟨(x.val.1.val.1, x.val.2), x.property⟩, x.val.1.val.2), x.val.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gridVertexOfTet_mono {N : ℕ} (t : Tet N) (a b : Vertex) (hab : a.val ≤ b.val) :
    ∀ j, (gridVertexOfTet t a j).val ≤ (gridVertexOfTet t b j).val := by
  intro j
  simp only [gridVertexOfTet, prefixMask]
  split_ifs <;> omega

/-- A geometric chain edge can always be oriented increasingly, including
all box-boundary cases. -/
theorem edge_endpoints_comparable {N : ℕ} (a b : GridVertex N) (x : ActualEdgeStar a b) :
    (∀ j, (a j).val ≤ (b j).val) ∨ (∀ j, (b j).val ≤ (a j).val) := by
  rcases le_total x.val.1.val.2.val x.val.2.val with h | h
  · left
    have hm := gridVertexOfTet_mono x.val.1.val.1 x.val.1.val.2 x.val.2 h
    simpa only [x.val.1.property, x.property] using hm
  · right
    have hm := gridVertexOfTet_mono x.val.1.val.1 x.val.2 x.val.1.val.2 h
    simpa only [x.val.1.property, x.property] using hm

theorem geometric_edge_bound {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (hab : a ≠ b) (x : ActualEdgeStar a b) : Fintype.card (ActualEdgeStar a b) ≤ 6 := by
  rcases edge_endpoints_comparable a b x with h | h
  · exact geometric_increasing_edge_bound hN a b hab h x
  · rw [Fintype.card_congr (reverseEdgeStar a b)]
    exact geometric_increasing_edge_bound hN b a hab.symm h (reverseEdgeStar a b x)

theorem edgeTet_injective {N : ℕ} (a b : GridVertex N) :
    Function.Injective (fun x : ActualEdgeStar a b => x.val.1.val.1) := by
  intro x y h
  have he : x.val.1 = y.val.1 := starTet_injective a h
  have hl : x.val.2 = y.val.2 := by
    apply gridVertexOfTet_injective x.val.1.val.1
    rw [x.property, he, y.property]
  exact Subtype.ext (Prod.ext he hl)

def reducedEdgeTags (b : BoundaryWord) (r : Fin 7) : BoundaryWord :=
  fun j => if positiveDirection r j = 1 then 1 else b j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A coordinate that changes along the edge contributes no containing
boundary plane.  Replacing its initial lower-boundary tag by an interior
tag preserves the full incidence set, not just the count. -/
theorem edge_tags_reduction : ∀ (b : BoundaryWord) (r : Fin 7), validPositiveTags b r →
    catalogEdgeSet b (positiveDirection r) =
      catalogEdgeSet (reducedEdgeTags b r) (positiveDirection r) := by
  decide +kernel

end FreudenthalSVLean.ActualEdgeCoverage
