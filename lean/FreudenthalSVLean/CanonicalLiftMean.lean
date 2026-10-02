import FreudenthalSVLean.DivergenceMean
import FreudenthalSVLean.CanonicalPressureLift

/-!
# Proved total-mean compatibility of the actual canonical edge lifts

For manuscript Proposition `edge`, all quartic and quintic canonical
lifts have zero total genuine divergence mean.  This includes borrowed
face terms and the quintic middle multiplier.  The identity is propagated
from proved actual paired face means through the fixed linear coefficient
maps; no conformity-to-divergence-theorem implication is assumed.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.ActualCanonicalEdgeLift
open FreudenthalSVLean.StableCanonicalPattern
open FreudenthalSVLean.StableCanonicalEdgeLift
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.DivergenceMean

noncomputable section

namespace FreudenthalSVLean.CanonicalLiftMean

set_option backward.isDefEq.respectTransparency false

theorem termField_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e : ℕ) (he : 0 < e) :
    totalMean hN (termField hN a b c hd hl side p r e) = 0 := by
  have hg := actual_pair_geometry hN a b c hd hl side p r
  exact weightedFace_totalMean_zero hN _ _ _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 _ e he _

theorem patternField_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (he : 0 < e) : totalMean hN (patternField hN a b c hd hl side p e) = 0 := by
  rw [patternField, map_sum]
  exact Finset.sum_eq_zero (fun r _ => termField_totalMean_zero hN a b c hd hl side p r e he)

theorem patternLinear_totalMean_zero {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (e : ℕ) (he : 0 < e) (hk : 3 + e ≤ k)
    (w : Fin (patternCount c) → ℝ) :
    totalMean hN (patternLinear hN a b c hd hl side e hk w).val = 0 := by
  rw [patternLinear_val, map_sum]
  simp only [map_smul, patternField_totalMean_zero hN a b c hd hl side _ e he,
    smul_zero, Finset.sum_const_zero]

theorem endpointLift_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c) :
    totalMean hN (endpointLift hN a b c hd hl side q).val = 0 := by
  exact patternLinear_totalMean_zero hN a b c hd hl side 1 (by norm_num) (by norm_num) _

theorem quarticLift_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c) :
    totalMean hN (quarticLift hN a b c hd hl q).val = 0 := by
  change totalMean hN ((endpointLift hN a b c hd hl false q.1).val +
    (endpointLift hN a b c hd hl true q.2).val) = 0
  rw [map_add, endpointLift_totalMean_zero, endpointLift_totalMean_zero, add_zero]

theorem bilinearTerm_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (m : GridVertex N) :
    totalMean hN (weightedTerm hN a b c hd hl side p r 1 1 m) = 0 := by
  have hg := actual_pair_geometry hN a b c hd hl side p r
  exact bilinearFace_totalMean_zero hN _ _ _ _ hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 _ _ _

theorem bilinearPattern_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c)) (m : GridVertex N) :
    totalMean hN (weightedPattern hN a b c hd hl side p 1 1 m) = 0 := by
  rw [weightedPattern, map_sum]
  exact Finset.sum_eq_zero (fun r _ => bilinearTerm_totalMean_zero hN a b c hd hl side p r m)

theorem hatEndpointLift_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c) :
    totalMean hN (hatEndpointLift hN a b c hd hl side multiplier q).val = 0 := by
  rw [hatEndpointLift_val, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [map_smul, ← weightedPattern_one_power hN a b c hd hl side p 1,
    bilinearPattern_totalMean_zero, smul_zero]

theorem quinticLift_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : sourceSpace c × sourceSpace c × sourceSpace c) :
    totalMean hN (quinticLift hN a b c hd hl q).val = 0 := by
  change totalMean hN ((hatEndpointLift hN a b c hd hl false false q.1).val +
    (hatEndpointLift hN a b c hd hl false true q.2.1).val +
    (hatEndpointLift hN a b c hd hl true true q.2.2).val) = 0
  rw [map_add, map_add, hatEndpointLift_totalMean_zero, hatEndpointLift_totalMean_zero,
    hatEndpointLift_totalMean_zero, add_zero, add_zero]

theorem quarticMap_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 4) :
    totalMean hN (quarticMap hN a b c hd hl q).val = 0 :=
  quarticLift_totalMean_zero hN a b c hd hl (quarticData hN a b c hd hl q)

theorem quinticMap_totalMean_zero {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 5) :
    totalMean hN (quinticMap hN a b c hd hl q).val = 0 :=
  quinticLift_totalMean_zero hN a b c hd hl (quinticData hN a b c hd hl q)

end FreudenthalSVLean.CanonicalLiftMean
