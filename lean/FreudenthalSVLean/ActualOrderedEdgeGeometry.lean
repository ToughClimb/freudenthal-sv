import FreudenthalSVLean.OrderedEdgeGeometry
import FreudenthalSVLean.EdgePressureData

/-!
# Ordered canonical incidences on the actual mesh

For manuscript Lemma `edge-star`, an edge in canonical coordinates is
identified with the ordered table by equality of the reduced containing-
boundary-plane tags.  The reduction ignores changing coordinates, so the
construction includes edges starting or ending on a physical plane in
their increasing direction, including the meshes `N=1,2`.

The ordered equivalence reconstructs actual tetrahedra and both endpoint
indices.  Shared faces and zero relative face coordinates transfer to
actual physical shared faces and coordinate planes.  These results are
the geometry interface for deriving the actual source relations and for
realizing the face-pattern coefficient identities.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry
open FreudenthalSVLean.EdgePressureData

noncomputable section

namespace FreudenthalSVLean.ActualOrderedEdgeGeometry

def CanonicalLocation {N : ℕ} (a : GridVertex N) (c : Fin 7) : Prop :=
  reducedEdgeTags (boundaryTag a) (canonicalDirectionIndex c) =
    reducedEdgeTags (canonicalEdgeTags c) (canonicalDirectionIndex c)

theorem edge_predicate_canonical {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (sa : CatalogState × Vertex) :
    CatalogEdgePredicate (boundaryTag a) (displacement a b) sa ↔
      CatalogEdgePredicate (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) sa := by
  have hsets : catalogEdgeSet (boundaryTag a) (displacement a b) =
      catalogEdgeSet (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) := by
    rw [hd, edge_tags_reduction (boundaryTag a) _ (actual_positive_tags hN a b _ hd),
      hl, ← edge_tags_reduction (canonicalEdgeTags c) _ (canonical_tags_valid c)]
  have hm := Finset.ext_iff.mp hsets sa
  simpa only [catalogEdgeSet, Finset.mem_filter, Finset.mem_univ, true_and] using hm

def orderedActualStar {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) : VertexStar a :=
  (catalogIncidenceEquiv hN a).symm ⟨(orderedIncidence c i).1,
    ((edge_predicate_canonical hN a b c hd hl (orderedIncidence c i)).mpr
      (ordered_incidence_valid c i)).1⟩

theorem orderedActualStar_catalog {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) :
    starCatalog (orderedActualStar hN a b c hd hl i) = (orderedIncidence c i).1 := by
  rw [← catalogIncidenceEquiv_val hN a]
  exact congrArg Subtype.val ((catalogIncidenceEquiv hN a).apply_symm_apply _)

theorem orderedActualStar_gradient {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) (r : Vertex) (j : Coordinate) :
    barycentricGradient (R := ℝ) (orderedActualStar hN a b c hd hl i).val.1.2 r j =
      (catalogGradient (orderedIncidence c i).1 r j : ℝ) := by
  rw [← starCatalog_perm, orderedActualStar_catalog]
  exact (gradient_int_cast _ r j).symm

def orderedActualEdge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) : ActualEdgeStar a b :=
  ⟨(orderedActualStar hN a b c hd hl i, (orderedIncidence c i).2), by
    apply (endpoint_iff_relative hN a b _ _).mpr
    rw [catalogIncidenceEquiv_val, orderedActualStar_catalog]
    exact ((edge_predicate_canonical hN a b c hd hl (orderedIncidence c i)).mpr
      (ordered_incidence_valid c i)).2⟩

theorem orderedActualEdge_catalog {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) :
    (edgeCatalogEquiv hN a b (orderedActualEdge hN a b c hd hl i)).val = orderedIncidence c i := by
  apply Prod.ext
  · exact (catalogIncidenceEquiv_val hN a _).trans (orderedActualStar_catalog hN a b c hd hl i)
  · rfl

/-- The fixed ordering covers all and only the actual incidences. -/
def orderedActualEquiv {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) : Fin (incidenceValence c) ≃ ActualEdgeStar a b := by
  classical
  apply Equiv.ofBijective (orderedActualEdge hN a b c hd hl)
  constructor
  · intro i j h
    apply ordered_incidence_injective c
    have he := congrArg (fun x => (edgeCatalogEquiv hN a b x).val) h
    simpa only [orderedActualEdge_catalog] using he
  · intro x
    have hx : (edgeCatalogEquiv hN a b x).val ∈
        catalogEdgeSet (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (edge_predicate_canonical hN a b c hd hl _).mp (edgeCatalogEquiv hN a b x).property⟩
    rw [ordered_incidence_complete] at hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    refine ⟨i, (edgeCatalogEquiv hN a b).injective (Subtype.ext ?_)⟩
    rw [orderedActualEdge_catalog]
    exact hi

theorem ordered_shared_face {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i j : Fin (incidenceValence c)) (r u : Vertex)
    (hf : catalogFace (orderedIncidence c i).1 r = catalogFace (orderedIncidence c j).1 u) :
    gridFace (orderedActualStar hN a b c hd hl i).val.1 r =
      gridFace (orderedActualStar hN a b c hd hl j).val.1 u := by
  apply (Finset.image_injective (displacement_injective a))
  rw [displaced_catalogFace, displaced_catalogFace, orderedActualStar_catalog,
    orderedActualStar_catalog]
  exact hf

theorem relative_zero_physical_coordinate {N : ℕ} {a : GridVertex N}
    (ta : VertexStar a) (l : Vertex) (j : Coordinate)
    (hz : catalogRelative (starCatalog ta) l j = 0) : vertex ta.val.1 l j = gridPoint a j := by
  have he := catalog_displacement ta l j
  rw [hz] at he
  have hv : (gridVertexOfTet ta.val.1 l j).val = (a j).val := by omega
  rw [← gridVertexOfTet_point]
  simp only [gridPoint, Pi.smul_apply, smul_eq_mul, hv]

theorem ordered_face_coordinate {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) (r : Vertex) (j : Coordinate)
    (hz : ∀ l : Vertex, l ≠ r → catalogRelative (orderedIncidence c i).1 l j = 0) :
    ∀ l : Vertex, l ≠ r → vertex (orderedActualStar hN a b c hd hl i).val.1 l j = gridPoint a j := by
  intro l hr
  apply relative_zero_physical_coordinate
  rw [orderedActualStar_catalog]
  exact hz l hr

theorem edge_constant_coordinate {N : ℕ} (a b : GridVertex N) (j : Coordinate)
    (hz : displacement a b j = 0) (s : ℝ) :
    segmentPoint (gridPoint a) (gridPoint b) s j = gridPoint a j := by
  have he : (b j).val = (a j).val := by
    change ((b j).val : ℤ) - ((a j).val : ℤ) = 0 at hz
    omega
  have hb : gridPoint b j = gridPoint a j := by simp [gridPoint, he]
  simp only [segmentPoint, hb]
  ring

theorem ordered_edge_point_mem {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (i : Fin (incidenceValence c)) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    segmentPoint (gridPoint a) (gridPoint b) s ∈
      tetrahedron (orderedActualStar hN a b c hd hl i).val.1 := by
  have h := MeshSegments.edge_segment_mem hN (orderedActualStar hN a b c hd hl i).val.1
    (orderedActualStar hN a b c hd hl i).val.2 (orderedIncidence c i).2 s hs
  change segmentPoint
    (vertex (orderedActualStar hN a b c hd hl i).val.1 (orderedActualStar hN a b c hd hl i).val.2)
    (vertex (orderedActualStar hN a b c hd hl i).val.1 (orderedIncidence c i).2) s ∈
      tetrahedron (orderedActualStar hN a b c hd hl i).val.1 at h
  have ha := first_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  have hb := second_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  change vertex (orderedActualStar hN a b c hd hl i).val.1
    (orderedActualStar hN a b c hd hl i).val.2 = gridPoint a at ha
  change vertex (orderedActualStar hN a b c hd hl i).val.1
    (orderedIncidence c i).2 = gridPoint b at hb
  rw [ha, hb] at h
  exact h

end FreudenthalSVLean.ActualOrderedEdgeGeometry
