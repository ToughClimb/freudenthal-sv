import FreudenthalSVLean.ActualCanonicalFaces
import FreudenthalSVLean.CanonicalFaceTraceAlgebra

/-!
# Actual polynomial traces of complete canonical endpoint patterns

For manuscript Lemma `edge-star`, the geometry-derived integer
coefficients are transported to the actual spatial-polynomial face
fields.  The universal product rule proves the trace for an arbitrary
local edge; integer displacement identifies the face owners and repeated
endpoint.  Summing all nonzero terms includes the borrowed face and
proves cancellation on entire off-target edges, not merely at sample
points.  All mesh sizes and boundary endpoint tags are quantified.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.VertexFaceGeometry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ActualFaceEdgeTraces
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.OrderedEdgeGeometry
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.CanonicalFaceTraceAlgebra
open FreudenthalSVLean.UniversalFaceEdgeTrace
open FreudenthalSVLean.NodalMesh

noncomputable section

namespace FreudenthalSVLean.ActualCanonicalPatternTrace

def relativeEndpointFactor (e : ℕ) (endpoint : IntPoint) (s : CatalogState)
    (l m : Vertex) (x : ℝ) : ℝ :=
  if endpoint = catalogRelative s l then (1 - x) ^ (e + 1) * x
  else if endpoint = catalogRelative s m then (1 - x) * x ^ (e + 1) else 0

theorem relative_factor_at_vertex (e : ℕ) (s : CatalogState) (a l m : Vertex) (x : ℝ) :
    relativeEndpointFactor e (catalogRelative s a) s l m x = endpointFactor e a l m x := by
  simp only [relativeEndpointFactor, (catalog_relative_injective s).eq_iff, endpointFactor]

theorem relative_factor_zero (e : ℕ) (endpoint : IntPoint) (s : CatalogState)
    (l m : Vertex) (x : ℝ)
    (h : endpoint ∉ ({catalogRelative s l, catalogRelative s m} : Finset IntPoint)) :
    relativeEndpointFactor e endpoint s l m x = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  simp [relativeEndpointFactor, h.1, h.2]

theorem first_face_displacement {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) :
    (gridFace (firstOwner hN a b c hd hl side p r).val.1
      (termPair c side p r).firstOmitted).image (displacement a) =
        (patternTerm c side (p.castLE (patternCount_le_six c)) r.val).nodes := by
  rw [displaced_catalogFace]
  have hc : starCatalog (firstOwner hN a b c hd hl side p r) = (termPair c side p r).first :=
    actualOwner_catalog hN a b c hd hl side p r _ _
  rw [hc, ← (termPair c side p r).firstFace]

private theorem faceScalar_missing {N : ℕ} (t v : Tet N) (r : Vertex)
    (h : ¬ gridFace t r ⊆ gridVertices v) : faceScalar t r v = 0 := by
  obtain ⟨m, hm, hmissing⟩ := Finset.not_subset.mp h
  exact Finset.prod_eq_zero hm (node_polynomial_zero_of_missing v m hmissing)

/-- Exact trace of each physical term on every local edge of the full
actual first-endpoint star. -/
theorem term_edge_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) (he : 0 < e) (ta : VertexStar a)
    (l m : Vertex) (hlm : l ≠ m) (x : ℝ) :
    eval (segmentPoint (vertex ta.val.1 l) (vertex ta.val.1 m) x)
      (divergence N (termField hN a b c hd hl side p r e) ta.val.1) =
      relativeEndpointFactor e (modeEndpoint c side) (starCatalog ta) l m x *
        (termEdgeCoefficient (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)
          (modeEndpoint c side) (starCatalog ta) l m : ℝ) := by
  classical
  let F := patternTerm c side (p.castLE (patternCount_le_six c)) r.val
  let w := termPair c side p r
  let t₀ := firstOwner hN a b c hd hl side p r
  have hdisp := first_face_displacement hN a b c hd hl side p r
  have hs₀ : starCatalog t₀ = w.first := actualOwner_catalog hN a b c hd hl side p r _ _
  by_cases hs : F.nodes ⊆ catalogVertices (starCatalog ta)
  · obtain ⟨u, _, hfu⟩ := owner_has_face w.first (starCatalog ta) w.firstOmitted w.firstThrough
      (by simpa only [← w.firstFace] using hs)
    have hF : F.nodes = catalogFace (starCatalog ta) u := w.firstFace.trans hfu
    have hf : gridFace t₀.val.1 w.firstOmitted = gridFace ta.val.1 u := by
      apply Finset.image_injective (displacement_injective a)
      rw [hdisp, displaced_catalogFace, ← hF]
    have hm := (canonical_term_geometry c side p r.val r.property).2.2.1
    rw [hF, catalogFace] at hm
    obtain ⟨α, _, hα⟩ := Finset.mem_image.mp hm
    have ha : gridVertexOfTet ta.val.1 α = physicalEndpoint a b side := by
      apply displacement_injective a
      have ha₀ : displacement a (gridVertexOfTet ta.val.1 α) = catalogRelative (starCatalog ta) α := by
        funext j
        exact catalog_displacement ta α j
      rw [ha₀, hα]
      cases side
      · simp [modeEndpoint, physicalEndpoint, displacement]
      · exact hd.symm
    let z : Space := fun j => meshScale N * (F.vector j : ℝ)
    have hp : termField hN a b c hd hl side p r e ta.val.1 =
        weightedFaceField N ta.val.1 u (gridVertexOfTet ta.val.1 α)
          (gridVertexOfTet ta.val.1 α) e 0 z ta.val.1 := by
      funext j
      change weightedFaceField N t₀.val.1 w.firstOmitted (physicalEndpoint a b side)
        (physicalEndpoint a b side) e 0 z ta.val.1 j = _
      rw [← ha]
      exact congrFun (weightedFaceField_shared t₀.val.1 ta.val.1 w.firstOmitted u hf
        (gridVertexOfTet ta.val.1 α) (gridVertexOfTet ta.val.1 α) e 0 z) j
    have ht := weighted_all_edge_divergence hN ta.val.1 u α l m e he hlm z x
    have hgrad :
        (∑ j : Coordinate, (F.vector j : ℝ) * faceEdgeGradient ta.val.1.2 u l m j) =
          (∑ j : Coordinate, F.vector j *
            faceEdgeGradient (R := ℤ) (MeshCoverage.orderPerm (starCatalog ta).1) u l m j : ℤ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Int.cast_mul, face_edge_gradient_cast, starCatalog_perm]
    have hz : ∑ j : Coordinate, z j * faceEdgeGradient ta.val.1.2 u l m j =
        meshScale N * ∑ j : Coordinate, (F.vector j : ℝ) * faceEdgeGradient ta.val.1.2 u l m j := by
      simp only [z, Finset.mul_sum, mul_assoc]
    have htr :
        eval (segmentPoint (vertex ta.val.1 l) (vertex ta.val.1 m) x)
          (divergence N (termField hN a b c hd hl side p r e) ta.val.1) =
          relativeEndpointFactor e (modeEndpoint c side) (starCatalog ta) l m x *
            (∑ j : Coordinate, F.vector j *
              faceEdgeGradient (R := ℤ) (MeshCoverage.orderPerm (starCatalog ta).1) u l m j : ℤ) := by
      change eval _ (∑ j : Coordinate, pderiv j (termField hN a b c hd hl side p r e ta.val.1 j)) = _
      rw [hp]
      change eval _ (divergence N (weightedFaceField N ta.val.1 u
        (gridVertexOfTet ta.val.1 α) (gridVertexOfTet ta.val.1 α) e 0 z) ta.val.1) = _
      rw [ht, hz, hgrad, ← hα, relative_factor_at_vertex]
      field_simp [(meshScale_pos N hN).ne']
    rw [htr, term_coefficient_reconstruction c side p r.val (starCatalog ta) u l m hF hlm]
    by_cases hm : modeEndpoint c side ∈
        ({catalogRelative (starCatalog ta) l, catalogRelative (starCatalog ta) m} : Finset IntPoint)
    · rw [if_pos hm]
    · rw [if_neg hm, Int.cast_zero, relative_factor_zero e _ _ l m x hm, zero_mul]
      simp
  · have hmissing : ¬ gridFace t₀.val.1 w.firstOmitted ⊆ gridVertices ta.val.1 := by
      intro h
      apply hs
      have hi := Finset.image_subset_image h (f := displacement a)
      rw [hdisp, displaced_catalogVertices] at hi
      exact hi
    have hzero : termField hN a b c hd hl side p r e ta.val.1 = 0 := by
      funext j
      change C _ * faceScalar t₀.val.1 w.firstOmitted ta.val.1 * _ * _ = 0
      rw [faceScalar_missing _ _ _ hmissing]
      simp
    change eval _ (∑ j : Coordinate, pderiv j (termField hN a b c hd hl side p r e ta.val.1 j)) = _
    rw [hzero]
    simp [termEdgeCoefficient, hs, F]

theorem active_coefficients_sum (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (s : CatalogState) (l m : Vertex) :
    (∑ r : ActiveTerm c side p,
      (termEdgeCoefficient (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)
        (modeEndpoint c side) s l m : ℝ)) =
      (patternEdgeCoefficient c side (p.castLE (patternCount_le_six c)) s l m : ℝ) := by
  classical
  have he :
      (∑ r : ActiveTerm c side p,
        (termEdgeCoefficient (patternTerm c side (p.castLE (patternCount_le_six c)) r.val)
          (modeEndpoint c side) s l m : ℝ)) =
      ∑ r ∈ (Finset.univ : Finset (Fin 2)) with
          (patternTerm c side (p.castLE (patternCount_le_six c)) r).vector ≠ 0,
        (termEdgeCoefficient (patternTerm c side (p.castLE (patternCount_le_six c)) r)
          (modeEndpoint c side) s l m : ℝ) := by
    exact (Finset.sum_subtype
      (p := fun r : Fin 2 => (patternTerm c side (p.castLE (patternCount_le_six c)) r).vector ≠ 0)
      ((Finset.univ : Finset (Fin 2)).filter
        (fun r => (patternTerm c side (p.castLE (patternCount_le_six c)) r).vector ≠ 0))
      (by simp) (fun r : Fin 2 =>
        (termEdgeCoefficient (patternTerm c side (p.castLE (patternCount_le_six c)) r)
          (modeEndpoint c side) s l m : ℝ))).symm
  rw [he, Finset.sum_filter, patternEdgeCoefficient, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hv : (patternTerm c side (p.castLE (patternCount_le_six c)) r).vector = 0
  · simp [hv, termEdgeCoefficient]
  · simp [hv]

/-- The actual endpoint pattern has precisely its target-edge trace and
zero trace on every other local edge, for every real edge parameter. -/
theorem pattern_edge_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (he : 0 < e) (ta : VertexStar a) (l m : Vertex) (hlm : l ≠ m) (x : ℝ) :
    eval (segmentPoint (vertex ta.val.1 l) (vertex ta.val.1 m) x)
      (divergence N (patternField hN a b c hd hl side p e) ta.val.1) =
      relativeEndpointFactor e (modeEndpoint c side) (starCatalog ta) l m x *
        (if ({catalogRelative (starCatalog ta) l, catalogRelative (starCatalog ta) m} : Finset IntPoint) =
              {0, positiveDirection (canonicalDirectionIndex c)} then
          (expectedStatePattern c side (p.castLE (patternCount_le_six c)) (starCatalog ta) : ℝ)
        else 0) := by
  have hp : divergence N (patternField hN a b c hd hl side p e) =
      ∑ r : ActiveTerm c side p, divergence N (termField hN a b c hd hl side p r e) := by
    exact map_sum (divergence N) _ _
  rw [hp, Finset.sum_apply, map_sum]
  simp only [term_edge_trace hN a b c hd hl side p _ e he ta l m hlm x]
  rw [← Finset.mul_sum, active_coefficients_sum,
    full_pattern_coefficients c side p (starCatalog ta) l m hlm, Int.cast_ite, Int.cast_zero]

end FreudenthalSVLean.ActualCanonicalPatternTrace
