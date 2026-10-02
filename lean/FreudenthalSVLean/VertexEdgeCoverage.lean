import FreudenthalSVLean.VertexStarSymmetry

/-!
# Exact edge-direction coverage at every mesh vertex

For the two edge-count columns of manuscript Lemma `vertex-coverage`,
geometric edges are represented by the integer displacement of their
second endpoint from the marked vertex.  Existence of such an edge is
proved equivalent to membership in a finite set of subchains of the
twenty-four universal states.  Repeated descriptions of the same geometric
edge are removed by `Finset.image`.  The active condition is the one proved
equivalent to physical-boundary exclusion in `VertexStarSymmetry`.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry

namespace FreudenthalSVLean.VertexEdgeCoverage

def catalogRelative (s : CatalogState) (a : Vertex) (j : Coordinate) : ℤ :=
  (catalogPrefix (s.1, a) j : ℤ) - (catalogPrefix s j : ℤ)

theorem relative_catalog (s : CatalogState) (a : Vertex) :
    relativeVertex (catalogEquiv s) a = catalogRelative s a := by
  funext j
  change (prefixMask (catalogEquiv (s.1, a)) j : ℤ) -
    (prefixMask (catalogEquiv s) j : ℤ) = _
  rw [prefix_catalog, prefix_catalog]
  rfl

def catalogEdges (b : Coordinate → Fin 3) : Finset (Coordinate → ℤ) :=
  ((Finset.univ : Finset (CatalogState × Vertex)).filter
    (fun sa => catalogAdmissible b sa.1 ∧ sa.2 ≠ sa.1.2)).image
      (fun sa => catalogRelative sa.1 sa.2)

instance (b : Coordinate → Fin 3) (d : Coordinate → ℤ) :
    Decidable (activeDirection b d) :=
  inferInstanceAs (Decidable (∀ j : Coordinate, b j ≠ 1 → d j ≠ 0))

def catalogActiveEdges (b : Coordinate → Fin 3) : Finset (Coordinate → ℤ) :=
  (catalogEdges b).filter (activeDirection b)

def incidentDirection (b : Coordinate → Fin 3) (d : Coordinate → ℤ) : Prop :=
  ∃ (s : State) (a : Vertex), tagAdmissible b s ∧ a ≠ s.2 ∧ relativeVertex s a = d

theorem mem_catalogEdges (b : Coordinate → Fin 3) (d : Coordinate → ℤ) :
    d ∈ catalogEdges b ↔ incidentDirection b d := by
  classical
  constructor
  · intro hd
    obtain ⟨⟨s, a⟩, hs, he⟩ := Finset.mem_image.mp hd
    obtain ⟨_, ha, hne⟩ := Finset.mem_filter.mp hs
    exact ⟨catalogEquiv s, a, (catalog_admissible_iff b s).mpr ha, hne,
      (relative_catalog s a).trans he⟩
  · rintro ⟨s, a, hs, hne, he⟩
    obtain ⟨t, rfl⟩ := catalogEquiv.surjective s
    refine Finset.mem_image.mpr ⟨(t, a), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (catalog_admissible_iff b t).mp hs, hne⟩
    · exact (relative_catalog t a).symm.trans he

def geometricIncidentDirection {N : ℕ} (n : GridVertex N) (d : Coordinate → ℤ) : Prop :=
  ∃ (t : Tet N) (a l : Vertex), gridVertexOfTet t a = n ∧ l ≠ a ∧
    integerGrid (gridVertexOfTet t l) - integerGrid n = d

/-- This is an exact arbitrary-`N` coverage statement for geometric edges,
including boundary endpoints; it is not just a count agreement. -/
theorem geometric_direction_iff {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : Coordinate → ℤ) :
    geometricIncidentDirection n d ↔ d ∈ catalogEdges (boundaryTag n) := by
  rw [mem_catalogEdges]
  constructor
  · rintro ⟨t, a, l, hta, hla, he⟩
    let ta : VertexStar n := ⟨(t, a), hta⟩
    refine ⟨(t.2, a), l, (admissible_iff_boundaryTags hN n _).mp
      (star_state_admissible n ta), hla, ?_⟩
    have hr : integerGrid (gridVertexOfTet t l) - integerGrid n =
        relativeVertex (t.2, a) l := by
      funext j
      exact grid_displacement n ta l j
    exact hr.symm.trans he
  · rintro ⟨s, a, hs, hne, he⟩
    let ha := (admissible_iff_boundaryTags hN n s).mpr hs
    let t := stateTet n s ha
    have ht := stateTet_vertex n s ha
    let ta : VertexStar n := ⟨(t, s.2), ht⟩
    refine ⟨t, s.2, a, ht, hne, ?_⟩
    have hr : integerGrid (gridVertexOfTet t a) - integerGrid n = relativeVertex s a := by
      funext j
      exact grid_displacement n ta a j
    exact hr.trans he

theorem geometric_active_direction_iff {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : Coordinate → ℤ) :
    geometricIncidentDirection n d ∧ activeDirection (boundaryTag n) d ↔
      d ∈ catalogActiveEdges (boundaryTag n) := by
  simp only [catalogActiveEdges, Finset.mem_filter, geometric_direction_iff hN n]

def canonicalEdgeCount (c : Fin 6) : ℕ := ![4, 6, 7, 8, 10, 14] c

def canonicalActiveCount (c : Fin 6) : ℕ := ![0, 0, 1, 2, 4, 14] c

theorem canonical_edge_counts : ∀ c : Fin 6,
    (catalogEdges (canonicalTags c)).card = canonicalEdgeCount c := by
  decide +kernel

theorem canonical_active_counts : ∀ c : Fin 6,
    (catalogActiveEdges (canonicalTags c)).card = canonicalActiveCount c := by
  decide +kernel

end FreudenthalSVLean.VertexEdgeCoverage
