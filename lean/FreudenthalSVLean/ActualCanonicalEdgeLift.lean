import FreudenthalSVLean.ActualCanonicalPatternTrace
import FreudenthalSVLean.ActualCanonicalData
import FreudenthalSVLean.ConformingNodalMultiplication

/-!
# Fixed actual canonical quartic and quintic edge lift maps

For manuscript Lemma `edge-star`, the explicit incidence inverse is
composed with actual conforming face-pattern fields.  The maps are linear
on the entire fixed compatibility subspace.  The quartic endpoint maps
are multiplied by the global endpoint hats to give both quintic endpoint
modes and the middle mode.  Their divergence trace matches the full
actual pressure trace on the edge, not just a coefficient matrix.

Transport of these maps to arbitrary edge orientations, their energy
bound, their mean correction, and global edge assembly remain distinct
obligations.
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
open FreudenthalSVLean.OrderedEdgeGeometry
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.CanonicalFaceTraceAlgebra
open FreudenthalSVLean.ActualCanonicalPatternTrace
open FreudenthalSVLean.ActualCanonicalSource
open FreudenthalSVLean.ActualCanonicalData
open FreudenthalSVLean.EdgePressureData
open FreudenthalSVLean.EdgeModeUnisolvence
open FreudenthalSVLean.ConformingNodalMultiplication
open FreudenthalSVLean.UniversalFaceEdgeTrace

noncomputable section

namespace FreudenthalSVLean.ActualCanonicalEdgeLift

def modeFactor (side : Bool) (e : ℕ) (x : ℝ) : ℝ :=
  if side then (1 - x) * x ^ (e + 1) else (1 - x) ^ (e + 1) * x

theorem pattern_target_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (he : 0 < e) (i : Fin (incidenceValence c)) (x : ℝ) :
    eval (segmentPoint (gridPoint a) (gridPoint b) x)
      (divergence N (patternField hN a b c hd hl side p e)
        (orderedActualStar hN a b c hd hl i).val.1) =
      modeFactor side e x * (expectedPattern c side (p.castLE (patternCount_le_six c))
        (i.castLE (incidenceValence_le_six c)) : ℝ) := by
  let ta := orderedActualStar hN a b c hd hl i
  have hc : ta.val.2 = (orderedIncidence c i).1.2 := by
    rw [← starCatalog_cut, orderedActualStar_catalog]
  have hneq : ta.val.2 ≠ (orderedIncidence c i).2 := by
    rw [hc]
    exact (ordered_relative_endpoints c i).2.2
  have ht := pattern_edge_trace hN a b c hd hl side p e he ta ta.val.2
    (orderedIncidence c i).2 hneq x
  have ha := first_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  have hb := second_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  change vertex ta.val.1 ta.val.2 = gridPoint a at ha
  change vertex ta.val.1 (orderedIncidence c i).2 = gridPoint b at hb
  rw [ha, hb, orderedActualStar_catalog, hc,
    (ordered_relative_endpoints c i).1, (ordered_relative_endpoints c i).2.1,
    if_pos rfl, ordered_expected_state] at ht
  have hf : relativeEndpointFactor e (modeEndpoint c side) (orderedIncidence c i).1
      (orderedIncidence c i).1.2 (orderedIncidence c i).2 x = modeFactor side e x := by
    unfold relativeEndpointFactor modeEndpoint modeFactor
    rw [(ordered_relative_endpoints c i).1, (ordered_relative_endpoints c i).2.1]
    cases side <;> simp [direction_nonzero c]
  rw [hf] at ht
  exact ht

def patternLinear {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (hk : 3 + e ≤ k) :
    (Fin (patternCount c) → ℝ) →ₗ[ℝ] velocitySpace N k :=
  ∑ p : Fin (patternCount c),
    (LinearMap.toSpanSingleton ℝ (velocitySpace N k)
      ⟨patternField hN a b c hd hl side p e, patternField_mem hN a b c hd hl side p e hk⟩).comp
      (LinearMap.proj p)

theorem patternLinear_val {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) :
    (patternLinear hN a b c hd hl side e hk w).val =
      ∑ p : Fin (patternCount c), w p • patternField hN a b c hd hl side p e := by
  simp only [patternLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply, Submodule.coe_sum, Submodule.coe_smul]

theorem patternLinear_target {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (he : 0 < e) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl
      (divergence N (patternLinear hN a b c hd hl side e hk w).val) x =
      modeFactor side e x • patternMap c side w := by
  funext i
  simp only [orderedPressureTrace, patternLinear_val, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, smul_eq_C_mul, map_mul, eval_C]
  simp only [pattern_target_trace hN a b c hd hl side _ e he i x]
  change (∑ p : Fin (patternCount c), w p * (modeFactor side e x *
    (expectedPattern c side (p.castLE (patternCount_le_six c))
      (i.castLE (incidenceValence_le_six c)) : ℝ))) =
    modeFactor side e x * ∑ p : Fin (patternCount c),
      (expectedPattern c side (p.castLE (patternCount_le_six c))
        (i.castLE (incidenceValence_le_six c)) : ℝ) * w p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change _ = modeFactor side e x *
    ((expectedPattern c side (p.castLE (patternCount_le_six c))
      (i.castLE (incidenceValence_le_six c)) : ℝ) * w p)
  ring

theorem patternLinear_edge_values {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) (t : Tet N) (l m : Vertex) (x : ℝ) (j : Coordinate) :
    eval (segmentPoint (vertex t l) (vertex t m) x)
      ((patternLinear hN a b c hd hl side e hk w).val t j) = 0 := by
  simp only [patternLinear_val, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul,
    map_sum, map_mul, patternField_all_edge_values hN a b c hd hl, mul_zero, Finset.sum_const_zero]

def endpointLift {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) :
    sourceSpace c →ₗ[ℝ] velocitySpace N 4 :=
  (patternLinear hN a b c hd hl side 1 (by norm_num)).comp
    ((inverseMap c side).comp (sourceSpace c).subtype)

theorem endpointLift_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl (divergence N (endpointLift hN a b c hd hl side q).val) x =
      modeFactor side 1 x • q.val := by
  change orderedPressureTrace hN a b c hd hl
    (divergence N (patternLinear hN a b c hd hl side 1 (by norm_num)
      (inverseMap c side q.val)).val) x = _
  rw [patternLinear_target hN a b c hd hl side 1 (by norm_num), inverse_on_source]

def quarticLift {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) :
    sourceSpace c × sourceSpace c →ₗ[ℝ] velocitySpace N 4 :=
  (endpointLift hN a b c hd hl false).comp (LinearMap.fst ℝ _ _) +
    (endpointLift hN a b c hd hl true).comp (LinearMap.snd ℝ _ _)

theorem ordered_trace_add {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (p q : BrokenPressure N) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl (p + q) x =
      orderedPressureTrace hN a b c hd hl p x + orderedPressureTrace hN a b c hd hl q x := by
  funext i
  simp only [orderedPressureTrace, Pi.add_apply, map_add]

theorem quarticLift_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl (divergence N (quarticLift hN a b c hd hl q).val) x =
      cubicTrace q.1.val q.2.val x := by
  have he : (quarticLift hN a b c hd hl q).val =
      (endpointLift hN a b c hd hl false q.1).val +
        (endpointLift hN a b c hd hl true q.2).val := rfl
  rw [he, map_add]
  rw [ordered_trace_add, endpointLift_trace, endpointLift_trace]
  rfl

/-- Matching the whole actual cubic pressure trace with one fixed quartic
linear map on its compatible coefficient data. -/
theorem quartic_pressure_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : pressureSpace N 4)
    (hz : ∀ t l, eval (vertex t l) (q.val t) = 0) (x : ℝ) :
    let hc := quartic_pressure_data hN a b hab c hd hl q hz
    let α : sourceSpace c := ⟨orderedCoefficients hN a b c hd hl 3 1 q.val, hc.1⟩
    let β : sourceSpace c := ⟨orderedCoefficients hN a b c hd hl 3 2 q.val, hc.2⟩
    orderedPressureTrace hN a b c hd hl (divergence N (quarticLift hN a b c hd hl (α, β)).val) x =
      orderedPressureTrace hN a b c hd hl q.val x := by
  dsimp only
  rw [quarticLift_trace, ordered_cubic_trace hN a b hab c hd hl q.val
    (PressureVertexBound.pressure_degree_bound q) hz x]

def hatFactor (side : Bool) (x : ℝ) : ℝ := if side then x else 1 - x

theorem canonical_endpoints_distinct {N : ℕ} (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c)) : a ≠ b := by
  intro hab
  apply direction_nonzero c
  rw [← hd, hab, displacement, sub_self]

/-- Actual endpoint hats multiply the entire ordered divergence trace of
a zero-edge-value velocity field. -/
theorem ordered_hat_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (v : BrokenVelocity N)
    (hz : ∀ (t : Tet N) (l m : Vertex) (x : ℝ) (j : Coordinate),
      eval (segmentPoint (vertex t l) (vertex t m) x) (v t j) = 0) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl
      (divergence N (multiplyNode (physicalEndpoint a b side) v)) x =
      hatFactor side x • orderedPressureTrace hN a b c hd hl (divergence N v) x := by
  funext i
  let ta := orderedActualStar hN a b c hd hl i
  have ha := first_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  have hb := second_physical_endpoint a b (orderedActualEdge hN a b c hd hl i)
  change vertex ta.val.1 ta.val.2 = gridPoint a at ha
  change vertex ta.val.1 (orderedIncidence c i).2 = gridPoint b at hb
  have hga : gridVertexOfTet ta.val.1 ta.val.2 = a := ta.property
  have hgb : gridVertexOfTet ta.val.1 (orderedIncidence c i).2 = b :=
    (orderedActualEdge hN a b c hd hl i).property
  have hdiv := multiplyNode_edge_divergence (physicalEndpoint a b side) v ta.val.1 ta.val.2
    (orderedIncidence c i).2 x (hz _ _ _ x)
  have hn := nodal_physical_edge hN ta.val.1 (physicalEndpoint a b side)
    ta.val.2 (orderedIncidence c i).2 x
  rw [hga, hgb] at hn
  have hn' : eval (segmentPoint (vertex ta.val.1 ta.val.2)
      (vertex ta.val.1 (orderedIncidence c i).2) x)
      (NodalMesh.meshNodalPolynomial ta.val.1 (VertexStarSymmetry.integerGrid (physicalEndpoint a b side))) =
        hatFactor side x := by
    rw [hn]
    cases side <;> simp [physicalEndpoint, hatFactor,
      canonical_endpoints_distinct a b c hd, Ne.symm (canonical_endpoints_distinct a b c hd)]
  rw [hn', ha, hb] at hdiv
  exact hdiv

def hatEndpointLift {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) :
    sourceSpace c →ₗ[ℝ] velocitySpace N 5 :=
  (multiplyConforming (physicalEndpoint a b multiplier)).comp (endpointLift hN a b c hd hl side)

theorem hatEndpointLift_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl
      (divergence N (hatEndpointLift hN a b c hd hl side multiplier q).val) x =
        (hatFactor multiplier x * modeFactor side 1 x) • q.val := by
  change orderedPressureTrace hN a b c hd hl
    (divergence N (multiplyNode (physicalEndpoint a b multiplier)
      (endpointLift hN a b c hd hl side q).val)) x = _
  rw [ordered_hat_trace hN a b c hd hl multiplier _ (by
    intro t l m x j
    exact patternLinear_edge_values hN a b c hd hl side 1 (by norm_num)
      (inverseMap c side q.val) t l m x j) x, endpointLift_trace, smul_smul]

def quinticLift {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) :
    sourceSpace c × sourceSpace c × sourceSpace c →ₗ[ℝ] velocitySpace N 5 :=
  (hatEndpointLift hN a b c hd hl false false).comp (LinearMap.fst ℝ _ _) +
    (hatEndpointLift hN a b c hd hl false true).comp
      ((LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)) +
    (hatEndpointLift hN a b c hd hl true true).comp
      ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _))

theorem quinticLift_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c × sourceSpace c) (x : ℝ) :
    orderedPressureTrace hN a b c hd hl (divergence N (quinticLift hN a b c hd hl q).val) x =
      quarticTrace q.1.val q.2.1.val q.2.2.val x := by
  have he : (quinticLift hN a b c hd hl q).val =
      (hatEndpointLift hN a b c hd hl false false q.1).val +
        (hatEndpointLift hN a b c hd hl false true q.2.1).val +
        (hatEndpointLift hN a b c hd hl true true q.2.2).val := rfl
  rw [he, map_add, map_add, ordered_trace_add, ordered_trace_add,
    hatEndpointLift_trace, hatEndpointLift_trace, hatEndpointLift_trace]
  funext i
  simp only [hatFactor, modeFactor, Bool.false_eq_true, if_false, if_true,
    quarticTrace, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Matching the whole actual quartic pressure trace by the fixed quintic
linear map, with compatibility supplied by actual mesh conformity. -/
theorem quintic_pressure_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : pressureSpace N 5)
    (hz : ∀ t l, eval (vertex t l) (q.val t) = 0) (x : ℝ) :
    let hc := quintic_pressure_data hN a b hab c hd hl q hz
    let α : sourceSpace c := ⟨orderedCoefficients hN a b c hd hl 4 1 q.val, hc.1⟩
    let μ : sourceSpace c := ⟨orderedCoefficients hN a b c hd hl 4 2 q.val, hc.2.1⟩
    let β : sourceSpace c := ⟨orderedCoefficients hN a b c hd hl 4 3 q.val, hc.2.2⟩
    orderedPressureTrace hN a b c hd hl (divergence N (quinticLift hN a b c hd hl (α, μ, β)).val) x =
      orderedPressureTrace hN a b c hd hl q.val x := by
  dsimp only
  rw [quinticLift_trace, ordered_quartic_trace hN a b hab c hd hl q.val
    (PressureVertexBound.pressure_degree_bound q) hz x]

end FreudenthalSVLean.ActualCanonicalEdgeLift
