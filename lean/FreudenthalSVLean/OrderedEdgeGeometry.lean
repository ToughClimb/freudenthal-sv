import FreudenthalSVLean.CanonicalEdgeCoverage

/-!
# Ordered chain states of the seven canonical edge stars

The two tables in manuscript Lemma `edge-star` use a fixed tetrahedron
ordering.  This module reconstructs that ordering from coordinate-chain
states and endpoint indices.  The canonical edge displacement and full
vertex sets agree with the manuscript's ordered pairs, and the listed
states parameterize exactly the complete canonical catalog edge star.
No incidence-coordinate basis is assumed to have the correct geometry.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage

namespace FreudenthalSVLean.OrderedEdgeGeometry

def orderedState (c : Fin 7) (i : Fin 6) : CatalogState :=
  ![![(4, 1), (4, 1), (4, 1), (4, 1), (4, 1), (4, 1)],
    ![(4, 0), (5, 0), (4, 0), (4, 0), (4, 0), (4, 0)],
    ![(3, 0), (5, 0), (3, 0), (3, 0), (3, 0), (3, 0)],
    ![(5, 1), (2, 0), (3, 0), (5, 1), (5, 1), (5, 1)],
    ![(4, 1), (5, 1), (0, 0), (2, 0), (4, 1), (4, 1)],
    ![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)],
    ![(3, 2), (5, 2), (2, 1), (4, 1), (0, 0), (1, 0)]] c i

def orderedOther (c : Fin 7) (i : Fin 6) : Vertex :=
  ![![2, 2, 2, 2, 2, 2], ![1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2],
    ![2, 1, 1, 2, 2, 2], ![3, 3, 2, 2, 3, 3],
    ![3, 3, 3, 3, 3, 3], ![3, 3, 2, 2, 1, 1]] c i

def orderedIncidence (c : Fin 7) (i : Fin (incidenceValence c)) : CatalogState × Vertex :=
  (orderedState c (i.castLE (incidenceValence_le_six c)),
    orderedOther c (i.castLE (incidenceValence_le_six c)))

theorem canonical_tags_valid : ∀ c : Fin 7,
    validPositiveTags (canonicalEdgeTags c) (canonicalDirectionIndex c) := by
  decide +kernel

theorem ordered_incidence_valid : ∀ (c : Fin 7) (i : Fin (incidenceValence c)),
    CatalogEdgePredicate (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c))
      (orderedIncidence c i) := by
  decide +kernel

theorem ordered_incidence_injective : ∀ c : Fin 7, Function.Injective (orderedIncidence c) := by
  decide +kernel

theorem ordered_incidence_complete : ∀ c : Fin 7,
    catalogEdgeSet (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) =
      Finset.univ.image (orderedIncidence c) := by
  decide +kernel

noncomputable def orderedCatalogEquiv (c : Fin 7) :
    Fin (incidenceValence c) ≃
      CatalogEdge (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) := by
  classical
  let f (i : Fin (incidenceValence c)) :
      CatalogEdge (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) :=
    ⟨orderedIncidence c i, ordered_incidence_valid c i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact ordered_incidence_injective c (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ catalogEdgeSet (canonicalEdgeTags c)
        (positiveDirection (canonicalDirectionIndex c)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
    rw [ordered_incidence_complete] at hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    exact ⟨i, Subtype.ext hi⟩

def canonicalOppositePairs (c : Fin 7) (i : Fin 6) :
    (Coordinate → ℤ) × (Coordinate → ℤ) :=
  ![fun _ => (![0, 0, -1], ![1, 1, 0]),
    ![(![1, 0, 1], ![1, 1, 1]), (![0, 1, 1], ![1, 1, 1]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])],
    ![(![0, 1, 0], ![1, 1, 1]), (![0, 0, 1], ![1, 1, 1]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])],
    ![(![0, 0, -1], ![1, 1, 0]), (![1, 1, 0], ![1, 1, 1]),
      (![0, 1, 1], ![1, 1, 1]), (![0, 0, 0], ![0, 0, 0]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])],
    ![(![0, 0, -1], ![1, 0, 0]), (![0, 0, -1], ![0, 1, 0]),
      (![1, 0, 0], ![1, 1, 1]), (![0, 1, 0], ![1, 1, 1]),
      (![0, 0, 0], ![0, 0, 0]), (![0, 0, 0], ![0, 0, 0])],
    ![(![1, 0, 0], ![1, 1, 0]), (![1, 0, 0], ![1, 0, 1]),
      (![0, 1, 0], ![1, 1, 0]), (![0, 1, 0], ![0, 1, 1]),
      (![0, 0, 1], ![1, 0, 1]), (![0, 0, 1], ![0, 1, 1])],
    ![(![0, -1, -1], ![0, 0, -1]), (![0, -1, -1], ![0, -1, 0]),
      (![0, -1, 0], ![1, 0, 1]), (![0, 0, -1], ![1, 1, 0]),
      (![1, 1, 0], ![1, 1, 1]), (![1, 0, 1], ![1, 1, 1])]] c i

/-- The actual four-vertex sets reproduce the ordered opposite-pair
table in the paper, after translation by its first endpoint. -/
theorem ordered_opposite_pairs : ∀ (c : Fin 7) (i : Fin (incidenceValence c)),
    catalogVertices (orderedIncidence c i).1 =
      {0, positiveDirection (canonicalDirectionIndex c),
        (canonicalOppositePairs c (i.castLE (incidenceValence_le_six c))).1,
        (canonicalOppositePairs c (i.castLE (incidenceValence_le_six c))).2} := by
  decide +kernel

end FreudenthalSVLean.OrderedEdgeGeometry
