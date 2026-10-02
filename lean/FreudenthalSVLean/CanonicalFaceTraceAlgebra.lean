import FreudenthalSVLean.CanonicalFacePatterns
import FreudenthalSVLean.UniversalFaceEdgeTrace

/-!
# Universal coefficient interface for physical canonical patterns

For the pattern table in manuscript Lemma `edge-star`, the integer face
coefficient is identified with the universal product-rule edge gradient.
All twenty-four lattice states are included, whether or not they belong
to the canonical boundary word: every extra state's terms vanish because
it contains none of the supported faces.  Thus the coefficient identity
also applies when actual increasing endpoint tags differ from the
canonical representative.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.UniversalFaceEdgeTrace
open FreudenthalSVLean.MeshCoverage

noncomputable section

namespace FreudenthalSVLean.CanonicalFaceTraceAlgebra

theorem catalog_relative_injective : ∀ s : CatalogState, Function.Injective (catalogRelative s) := by
  decide +kernel

theorem catalog_mem_face : ∀ (s : CatalogState) (r a : Vertex),
    catalogRelative s a ∈ catalogFace s r ↔ a ≠ r := by
  decide +kernel

theorem face_edge_gradient_cast (s : CatalogState) (r l m : Vertex) (j : Coordinate) :
    (faceEdgeGradient (R := ℤ) (orderPerm s.1) r l m j : ℝ) =
      faceEdgeGradient (R := ℝ) (orderPerm s.1) r l m j := by
  unfold faceEdgeGradient
  split_ifs <;> simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero,
    ActualFaceMean.gradient_int_cast]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem term_coefficient_reconstruction : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (r : Fin 2) (s : CatalogState) (u l m : Vertex),
    let F := patternTerm c side (p.castLE (patternCount_le_six c)) r
    F.nodes = catalogFace s u → l ≠ m →
      termEdgeCoefficient F (modeEndpoint c side) s l m =
        if modeEndpoint c side ∈ ({catalogRelative s l, catalogRelative s m} : Finset IntPoint) then
          ∑ j : Coordinate, F.vector j * faceEdgeGradient (R := ℤ) (orderPerm s.1) u l m j
        else 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Target and zero off-target coefficients in the complete lattice star,
not just the admissible states of one canonical boundary word. -/
theorem full_pattern_coefficients : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (s : CatalogState) (l m : Vertex), l ≠ m →
    patternEdgeCoefficient c side (p.castLE (patternCount_le_six c)) s l m =
      if ({catalogRelative s l, catalogRelative s m} : Finset IntPoint) =
          {0, positiveDirection (canonicalDirectionIndex c)} then
        expectedStatePattern c side (p.castLE (patternCount_le_six c)) s
      else 0 := by
  decide +kernel

theorem ordered_relative_endpoints : ∀ (c : Fin 7) (i : Fin (incidenceValence c)),
    catalogRelative (orderedIncidence c i).1 (orderedIncidence c i).1.2 = 0 ∧
      catalogRelative (orderedIncidence c i).1 (orderedIncidence c i).2 =
        positiveDirection (canonicalDirectionIndex c) ∧
      (orderedIncidence c i).1.2 ≠ (orderedIncidence c i).2 := by
  decide +kernel

theorem ordered_expected_state : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (i : Fin (incidenceValence c)),
    expectedStatePattern c side (p.castLE (patternCount_le_six c)) (orderedIncidence c i).1 =
      expectedPattern c side (p.castLE (patternCount_le_six c))
        (i.castLE (incidenceValence_le_six c)) := by
  decide +kernel

theorem direction_nonzero : ∀ c : Fin 7, positiveDirection (canonicalDirectionIndex c) ≠ 0 := by
  decide +kernel

end FreudenthalSVLean.CanonicalFaceTraceAlgebra
