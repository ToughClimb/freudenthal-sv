import FreudenthalSVLean.OrderedEdgeGeometry

/-!
# Face witnesses for the three canonical source relations

For the zero, equal-pair, and checkerboard rows of manuscript Lemma
`edge-star`, this module records the exact face indices, boundary-plane
coordinates, conormal directions, and nonzero minors in the ordered
coordinate-chain table.  These finite geometric identities are checked
from the actual relative vertices and barycentric gradients.  The
gradient-jump and boundary-trace implications are separate analytic
theorems, not assumptions encoded in these geometry records.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry

namespace FreudenthalSVLean.CanonicalSourceGeometry

theorem one_location_planes : ∀ b : BoundaryWord,
    reducedEdgeTags b (canonicalDirectionIndex 0) =
      reducedEdgeTags (canonicalEdgeTags 0) (canonicalDirectionIndex 0) →
      b 1 = 0 ∧ b 2 = 2 := by
  decide +kernel

theorem equal_pair_location_plane : ∀ b : BoundaryWord,
    reducedEdgeTags b (canonicalDirectionIndex 2) =
      reducedEdgeTags (canonicalEdgeTags 2) (canonicalDirectionIndex 2) → b 0 = 0 := by
  decide +kernel

theorem one_face_planes :
    (∀ l : Vertex, l ≠ 3 → catalogRelative (orderedIncidence 0 0).1 l 1 = 0) ∧
    (∀ l : Vertex, l ≠ 0 → catalogRelative (orderedIncidence 0 0).1 l 2 = 0) := by
  decide +kernel

theorem one_face_minor :
    catalogGradient (orderedIncidence 0 0).1 3 1 * catalogGradient (orderedIncidence 0 0).1 0 2 -
      catalogGradient (orderedIncidence 0 0).1 3 2 * catalogGradient (orderedIncidence 0 0).1 0 1 = -1 := by
  decide +kernel

theorem equal_pair_faces :
    catalogFace (orderedIncidence 2 0).1 1 = catalogFace (orderedIncidence 2 1).1 1 ∧
    (∀ l : Vertex, l ≠ 3 → catalogRelative (orderedIncidence 2 0).1 l 0 = 0) ∧
    (∀ l : Vertex, l ≠ 3 → catalogRelative (orderedIncidence 2 1).1 l 0 = 0) ∧
    catalogGradient (orderedIncidence 2 0).1 1 1 = 1 := by
  decide +kernel

theorem checkerboard_faces :
    catalogFace (orderedIncidence 4 0).1 2 = catalogFace (orderedIncidence 4 1).1 2 ∧
    catalogFace (orderedIncidence 4 2).1 1 = catalogFace (orderedIncidence 4 3).1 1 ∧
    catalogFace (orderedIncidence 4 0).1 0 = catalogFace (orderedIncidence 4 2).1 3 ∧
    catalogFace (orderedIncidence 4 1).1 0 = catalogFace (orderedIncidence 4 3).1 3 := by
  decide +kernel

def checkerNormal₁ : Coordinate → ℤ := ![1, -1, 0]
def checkerNormal₂ : Coordinate → ℤ := ![0, 0, 1]

theorem checkerboard_normals : ∀ j : Coordinate,
    catalogGradient (orderedIncidence 4 0).1 2 j = checkerNormal₁ j ∧
    catalogGradient (orderedIncidence 4 2).1 1 j = checkerNormal₁ j ∧
    catalogGradient (orderedIncidence 4 0).1 0 j = -checkerNormal₂ j ∧
    catalogGradient (orderedIncidence 4 1).1 0 j = -checkerNormal₂ j := by
  decide +kernel

theorem checkerboard_minor :
    checkerNormal₁ 0 * checkerNormal₂ 2 - checkerNormal₁ 2 * checkerNormal₂ 0 = 1 := by
  decide +kernel

end FreudenthalSVLean.CanonicalSourceGeometry
