import FreudenthalSVLean.CubeMeshSymmetry
import FreudenthalSVLean.ActualOrderedEdgeGeometry

/-!
# Actual edge orientation and canonical boundary locations

For the manuscript's seven-row edge lifting table, a permutation and,
when necessary, central inversion followed by endpoint exchange put every
increasing actual edge in a canonical direction and canonical reduced
boundary word.  Changing coordinates have no containing boundary plane;
only constant-coordinate tags are used.  The finite boundary-word identity
is transported to actual grid nodes for every positive mesh size.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CubeMeshSymmetry

noncomputable section

namespace FreudenthalSVLean.CanonicalEdgeOrientation

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem canonical_reduced_words : ∀ (word : BoundaryWord) (d : Fin 7),
    validPositiveTags word d → ∃ (r : Fin 6) (flip : Bool),
      (fun j => positiveDirection d (orderMap r j)) =
        positiveDirection (canonicalDirectionIndex (incidenceKind word d)) ∧
      reducedEdgeTags (tagTransform word r flip)
          (canonicalDirectionIndex (incidenceKind word d)) =
        reducedEdgeTags (canonicalEdgeTags (incidenceKind word d))
          (canonicalDirectionIndex (incidenceKind word d)) := by
  decide +kernel

def firstNode {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) : GridVertex N := nodeMap π flip (if flip then b else a)

def secondNode {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) : GridVertex N := nodeMap π flip (if flip then a else b)

theorem perm_displacement {N : ℕ} (π : Equiv.Perm Coordinate) (a b : GridVertex N)
    (j : Coordinate) : displacement (permNode π a) (permNode π b) j =
      displacement a b (π.symm j) := rfl

theorem reverse_displacement {N : ℕ} (a b : GridVertex N) (j : Coordinate) :
    displacement (reverseNode b) (reverseNode a) j = displacement a b j := by
  have ha : (Fin.rev (a j)).val + (a j).val = N := by
    simp only [Fin.val_rev]
    omega
  have hb : (Fin.rev (b j)).val + (b j).val = N := by
    simp only [Fin.val_rev]
    omega
  unfold displacement VertexStarSymmetry.integerGrid reverseNode
  dsimp
  omega

theorem oriented_displacement {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (a b : GridVertex N) (j : Coordinate) :
    displacement (firstNode π flip a b) (secondNode π flip a b) j =
      displacement a b (π.symm j) := by
  cases flip
  · exact perm_displacement π a b j
  · change displacement (reverseNode (permNode π b)) (reverseNode (permNode π a)) j = _
    rw [reverse_displacement, perm_displacement]

theorem constant_coordinate_tags {N : ℕ} (a b : GridVertex N) (j : Coordinate)
    (hd : displacement a b j = 0) : boundaryTag a j = boundaryTag b j := by
  have he : a j = b j := by
    apply Fin.ext
    change ((b j).val : ℤ) - ((a j).val : ℤ) = 0 at hd
    omega
  simp only [boundaryTag, he]

theorem firstNode_constant_tag {N : ℕ} (hN : 0 < N)
    (π : Equiv.Perm Coordinate) (flip : Bool) (a b : GridVertex N) (j : Coordinate)
    (hd : displacement a b (π.symm j) = 0) :
    boundaryTag (firstNode π flip a b) j = transformTags π flip (boundaryTag a) j := by
  cases flip
  · exact congrFun (nodeMap_boundaryTag hN π false a) j
  · change boundaryTag (nodeMap π true b) j = _
    rw [nodeMap_boundaryTag hN]
    simp only [transformTags, if_true, reverseTags, relabelTags]
    rw [← constant_coordinate_tags a b (π.symm j) hd]

theorem positive_direction_binary : ∀ (d : Fin 7) (j : Coordinate),
    positiveDirection d j = 0 ∨ positiveDirection d j = 1 := by
  decide +kernel

theorem actual_canonical_orientation {N : ℕ} (hN : 0 < N) (a b : GridVertex N)
    (d : Fin 7) (hd : displacement a b = positiveDirection d) :
    ∃ (π : Equiv.Perm Coordinate) (flip : Bool),
      displacement (firstNode π flip a b) (secondNode π flip a b) =
        positiveDirection (canonicalDirectionIndex (incidenceKind (boundaryTag a) d)) ∧
      CanonicalLocation (firstNode π flip a b) (incidenceKind (boundaryTag a) d) := by
  obtain ⟨r, flip, hdir, hword⟩ := canonical_reduced_words (boundaryTag a) d
    (actual_positive_tags hN a b d hd)
  let π := (orderPerm r).symm
  refine ⟨π, flip, ?_, ?_⟩
  · funext j
    rw [oriented_displacement, hd]
    exact congrFun hdir j
  · unfold CanonicalLocation
    rw [← hword]
    funext j
    unfold reducedEdgeTags
    by_cases hj : positiveDirection (canonicalDirectionIndex
      (incidenceKind (boundaryTag a) d)) j = 1
    · simp only [hj, if_true]
    · simp only [hj, if_false]
      have hzero : displacement a b (π.symm j) = 0 := by
        rw [hd]
        have he := congrFun hdir j
        rcases positive_direction_binary d (π.symm j) with hz | ho
        · exact hz
        · exact False.elim (hj (he.symm.trans ho))
      rw [firstNode_constant_tag hN π flip a b j hzero]
      exact (congrFun (tagTransform_eq_transformTags (boundaryTag a) r flip) j).symm

end FreudenthalSVLean.CanonicalEdgeOrientation
