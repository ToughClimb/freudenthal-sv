import FreudenthalSVLean.ActualEdgeCoverage

/-!
# Complete geometric coverage by the seven edge-star types

For manuscript Lemma `edge-coverage` and its ordered geometric incidence
table, the finite object is the full set of tetrahedron vertex sets in
integer coordinates relative to the first edge endpoint.  All boundary
words and all seven increasing directions are checked under coordinate
permutations and central inversion with endpoint exchange.  The latter
uses `x ↦ d-x`, so both oriented endpoints are recentered correctly.

The actual mesh-to-catalog equivalence identifies the complete geometric
star with this object for every positive mesh size.  Thus equality with
a canonical star is a theorem about all physical incidences, not merely
an equality of counts or a finite sample-mesh assertion.  Supported-patch
face neighbors and lifting coefficient identities are separate claims.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.ActualEdgeCoverage

noncomputable section

namespace FreudenthalSVLean.CanonicalEdgeCoverage

def catalogGeometry (b : BoundaryWord) (d : Coordinate → ℤ) :
    Finset (Finset (Coordinate → ℤ)) :=
  (catalogEdgeSet b d).image (fun sa => catalogVertices sa.1)

def canonicalEdgeTags (c : Fin 7) : BoundaryWord :=
  ![![1, 0, 2], ![0, 0, 1], ![0, 0, 0], ![0, 0, 1],
    ![0, 0, 1], ![0, 0, 0], ![0, 1, 1]] c

def canonicalDirectionIndex (c : Fin 7) : Fin 7 := ![0, 2, 5, 1, 3, 6, 0] c

def canonicalGeometry (c : Fin 7) : Finset (Finset (Coordinate → ℤ)) :=
  catalogGeometry (canonicalEdgeTags c) (positiveDirection (canonicalDirectionIndex c))

def edgePointTransform (d : Coordinate → ℤ) (r : Fin 6) (flip : Bool)
    (x : Coordinate → ℤ) : Coordinate → ℤ :=
  fun j => if flip then d (orderMap r j) - x (orderMap r j) else x (orderMap r j)

def transformGeometry (d : Coordinate → ℤ) (r : Fin 6) (flip : Bool)
    (S : Finset (Finset (Coordinate → ℤ))) : Finset (Finset (Coordinate → ℤ)) :=
  S.image (fun T => T.image (edgePointTransform d r flip))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The exact finite statement covers every admissible boundary word and
direction, and compares full tetrahedron vertex sets. -/
theorem seven_geometries_covered : ∀ (b : BoundaryWord) (e : Fin 7), validPositiveTags b e →
    ∃ (r : Fin 6) (flip : Bool),
      (fun j => positiveDirection e (orderMap r j)) =
        positiveDirection (canonicalDirectionIndex (incidenceKind b e)) ∧
      transformGeometry (positiveDirection e) r flip (catalogGeometry b (positiveDirection e)) =
        canonicalGeometry (incidenceKind b e) := by
  decide +kernel

def actualRelativeGeometry {N : ℕ} (a b : GridVertex N) : Finset (Finset (Coordinate → ℤ)) :=
  Finset.univ.image (fun x : ActualEdgeStar a b =>
    (gridVertices x.val.1.val.1).image (displacement a))

/-- Every actual edge-star tetrahedron is represented, with exactly its
four actual relative grid vertices. -/
theorem actual_relative_geometry {N : ℕ} (hN : 0 < N) (a b : GridVertex N) :
    actualRelativeGeometry a b = catalogGeometry (boundaryTag a) (displacement a b) := by
  classical
  ext T
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    let y := edgeCatalogEquiv hN a b x
    apply Finset.mem_image.mpr
    refine ⟨y.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.property⟩, ?_⟩
    have hy : y.val.1 = starCatalog x.val.1 := catalogIncidenceEquiv_val hN a x.val.1
    rw [hy, ← displaced_catalogVertices]
    exact hx
  · intro h
    obtain ⟨sa, hsa, hT⟩ := Finset.mem_image.mp h
    have hp : CatalogEdgePredicate (boundaryTag a) (displacement a b) sa :=
      (Finset.mem_filter.mp hsa).2
    let y : CatalogEdge (boundaryTag a) (displacement a b) := ⟨sa, hp⟩
    let x := (edgeCatalogEquiv hN a b).symm y
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    rw [displaced_catalogVertices]
    have hy : (edgeCatalogEquiv hN a b x).val = sa :=
      congrArg Subtype.val ((edgeCatalogEquiv hN a b).apply_symm_apply y)
    have hs : starCatalog x.val.1 = sa.1 := by
      rw [← catalogIncidenceEquiv_val hN a x.val.1]
      exact congrArg Prod.fst hy
    rw [hs]
    exact hT

/-- Full seven-type coverage for every positive `N`, including physical
boundary edges and `N=1,2`. -/
theorem geometric_seven_type_coverage {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (e : Fin 7) (hd : displacement a b = positiveDirection e) :
    ∃ (r : Fin 6) (flip : Bool),
      (fun j => displacement a b (orderMap r j)) =
        positiveDirection (canonicalDirectionIndex (incidenceKind (boundaryTag a) e)) ∧
      transformGeometry (displacement a b) r flip (actualRelativeGeometry a b) =
        canonicalGeometry (incidenceKind (boundaryTag a) e) := by
  rw [actual_relative_geometry hN a b, hd]
  exact seven_geometries_covered (boundaryTag a) e (actual_positive_tags hN a b e hd)

end FreudenthalSVLean.CanonicalEdgeCoverage
