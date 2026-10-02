import FreudenthalSVLean.ActualCanonicalEdgeLift

/-!
# Global protected traces of canonical edge lift maps

For manuscript Lemma `edge-star`, each actual canonical lift protects
every mesh vertex and every off-target mesh edge.  The proof uses injective
integer displacement to identify geometric edge pairs, exact polynomial
support off the first-endpoint star, and the full lattice coefficient
identity inside it.  Nodal multiplication preserves these protections.
There is no assumption that an off-target edge belongs to a sampled
reference configuration.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.ActualCanonicalPatternTrace
open FreudenthalSVLean.ActualCanonicalEdgeLift
open FreudenthalSVLean.ConformingNodalMultiplication

noncomputable section

namespace FreudenthalSVLean.CanonicalEdgeProtection

theorem pattern_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (he : 0 < e) (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (patternField hN a b c hd hl side p e) t) = 0 := by
  classical
  by_cases ht : ∃ u : Vertex, gridVertexOfTet t u = a
  · obtain ⟨u, hu⟩ := ht
    let ta : VertexStar a := ⟨(t, u), hu⟩
    have hpair : ({catalogRelative (starCatalog ta) l, catalogRelative (starCatalog ta) m} :
        Finset IntPoint) ≠ {0, positiveDirection (canonicalDirectionIndex c)} := by
      intro hp
      apply hother
      apply Finset.image_injective (displacement_injective a)
      have hdl : displacement a (gridVertexOfTet t l) = catalogRelative (starCatalog ta) l := by
        funext j
        exact catalog_displacement ta l j
      have hdm : displacement a (gridVertexOfTet t m) = catalogRelative (starCatalog ta) m := by
        funext j
        exact catalog_displacement ta m j
      have hda : displacement a a = 0 := sub_self _
      simp only [Finset.image_insert, Finset.image_singleton, hdl, hdm, hda, hd]
      exact hp
    have h := pattern_edge_trace hN a b c hd hl side p e he ta l m hlm x
    rw [if_neg hpair, mul_zero] at h
    exact h
  · have hz := patternField_off_star hN a b c hd hl side p e t (by
      intro u hu
      exact ht ⟨u, hu⟩)
    change eval _ (∑ j : Coordinate, pderiv j (patternField hN a b c hd hl side p e t j)) = 0
    rw [hz]
    simp

theorem patternLinear_other_edge {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (he : 0 < e) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (patternLinear hN a b c hd hl side e hk w).val t) = 0 := by
  simp only [patternLinear_val, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_C_mul, map_mul,
    pattern_other_edge hN a b c hd hl side _ e he t l m hlm hother x,
    mul_zero, Finset.sum_const_zero]

theorem patternLinear_vertex_derivative {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((patternLinear hN a b c hd hl side e hk w).val t j)) = 0 := by
  simp only [patternLinear_val, Finset.sum_apply, Pi.smul_apply,
    map_sum, smul_eq_C_mul, pderiv_C_mul, map_mul,
    patternField_vertex_derivative hN a b c hd hl side, mul_zero, Finset.sum_const_zero]

theorem endpointLift_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c)
    (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((endpointLift hN a b c hd hl side q).val t j)) = 0 :=
  patternLinear_vertex_derivative hN a b c hd hl side 1 (by norm_num)
    (inverseMap c side q.val) t l i j

theorem endpointLift_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c)
    (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (endpointLift hN a b c hd hl side q).val t) = 0 :=
  patternLinear_other_edge hN a b c hd hl side 1 (by norm_num) (by norm_num)
    (inverseMap c side q.val) t l m hlm hother x

theorem hatEndpointLift_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c)
    (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((hatEndpointLift hN a b c hd hl side multiplier q).val t j)) = 0 := by
  apply multiplyNode_vertex_derivative
  · have hz := patternLinear_edge_values (k := 4) hN a b c hd hl side 1 (by norm_num)
      (inverseMap c side q.val) t l l 0 j
    have he : segmentPoint (vertex t l) (vertex t l) (0 : ℝ) = vertex t l := by
      funext a
      simp [ChainGeometry.segmentPoint]
    rw [he] at hz
    exact hz
  · exact endpointLift_vertex_derivative hN a b c hd hl side q t l i j

theorem hatEndpointLift_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c)
    (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (hatEndpointLift hN a b c hd hl side multiplier q).val t) = 0 := by
  change eval _ (divergence N (multiplyNode (physicalEndpoint a b multiplier)
    (endpointLift hN a b c hd hl side q).val) t) = 0
  rw [multiplyNode_edge_divergence _ _ t l m x (by
    intro j
    exact patternLinear_edge_values hN a b c hd hl side 1 (by norm_num)
      (inverseMap c side q.val) t l m x j),
    endpointLift_other_edge hN a b c hd hl side q t l m hlm hother x, mul_zero]

theorem quarticLift_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c)
    (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((quarticLift hN a b c hd hl q).val t j)) = 0 := by
  change eval _ (pderiv i
    ((endpointLift hN a b c hd hl false q.1).val t j +
      (endpointLift hN a b c hd hl true q.2).val t j)) = 0
  rw [map_add, map_add, endpointLift_vertex_derivative, endpointLift_vertex_derivative, add_zero]

theorem quinticLift_vertex_derivative {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c × sourceSpace c)
    (t : Tet N) (l : Vertex) (i j : Coordinate) :
    eval (vertex t l) (pderiv i ((quinticLift hN a b c hd hl q).val t j)) = 0 := by
  change eval _ (pderiv i
    ((hatEndpointLift hN a b c hd hl false false q.1).val t j +
      (hatEndpointLift hN a b c hd hl false true q.2.1).val t j +
      (hatEndpointLift hN a b c hd hl true true q.2.2).val t j)) = 0
  simp only [map_add, hatEndpointLift_vertex_derivative hN a b c hd hl, add_zero]

theorem quarticLift_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c)
    (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (quarticLift hN a b c hd hl q).val t) = 0 := by
  have he : (quarticLift hN a b c hd hl q).val =
      (endpointLift hN a b c hd hl false q.1).val +
        (endpointLift hN a b c hd hl true q.2).val := rfl
  rw [he, map_add]
  simp only [Pi.add_apply, map_add, endpointLift_other_edge hN a b c hd hl _ _ t l m hlm hother x,
    add_zero]

theorem quinticLift_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c × sourceSpace c)
    (t : Tet N) (l m : Vertex) (hlm : l ≠ m)
    (hother : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (x : ℝ) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      (divergence N (quinticLift hN a b c hd hl q).val t) = 0 := by
  have he : (quinticLift hN a b c hd hl q).val =
      (hatEndpointLift hN a b c hd hl false false q.1).val +
        (hatEndpointLift hN a b c hd hl false true q.2.1).val +
        (hatEndpointLift hN a b c hd hl true true q.2.2).val := rfl
  rw [he, map_add, map_add]
  simp only [Pi.add_apply, map_add, hatEndpointLift_other_edge hN a b c hd hl _ _ _ t l m hlm hother x,
    add_zero]

end FreudenthalSVLean.CanonicalEdgeProtection
