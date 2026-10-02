import FreudenthalSVLean.ActualCanonicalEdgeLift
import FreudenthalSVLean.StableWeightedFaceField

/-!
# Mesh-independent energy of actual canonical pattern generators

For manuscript Lemma edge-star, the actual generators, including the
borrowed sum and the nodally weighted quintic generators, have energy
bounded by C h cubed. The vector amplitudes are h times fixed integer
vectors; the proved weighted-face estimate and exact two-term support
give one constant before all mesh, edge, endpoint, and pattern parameters.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.ConformingNodalMultiplication
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableCanonicalPattern

theorem integer_vector_square_bound : ∀ (c : Fin 7) (side : Bool) (p : Fin (patternCount c))
    (r : Fin 2),
    (∑ j : Coordinate,
      ((patternTerm c side (p.castLE (patternCount_le_six c)) r).vector j) ^ 2) ≤ (3 : ℤ) := by
  decide +kernel

theorem real_vector_square_bound (c : Fin 7) (side : Bool) (p : Fin (patternCount c)) (r : Fin 2) :
    (∑ j : Coordinate,
      (((patternTerm c side (p.castLE (patternCount_le_six c)) r).vector j : ℝ)) ^ 2) ≤ 3 := by
  have h := integer_vector_square_bound c side p r
  have hr : ((∑ j : Coordinate,
      ((patternTerm c side (p.castLE (patternCount_le_six c)) r).vector j) ^ 2 : ℤ) : ℝ) ≤ 3 := by
    exact_mod_cast h
  simpa only [Int.cast_sum, Int.cast_pow] using hr

def weightedTerm {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (r : ActiveTerm c side p) (e q : ℕ) (m : GridVertex N) : BrokenVelocity N :=
  weightedFaceField N (firstOwner hN a b c hd hl side p r).val.1
    (termPair c side p r).firstOmitted (physicalEndpoint a b side) m e q
    (fun j => meshScale N *
      ((patternTerm c side (p.castLE (patternCount_le_six c)) r.val).vector j : ℝ))

theorem weightedTerm_uniform_energy (e q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
      (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
      (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
      (r : ActiveTerm c side p) (m : GridVertex N),
      velocityEnergy (weightedTerm hN a b c hd hl side p r e q m) ≤ C * (meshScale N) ^ 3 := by
  classical
  obtain ⟨C, hC, hb⟩ := StableWeightedFaceField.weighted_global_bound e q
  refine ⟨3 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN a b c hd hl side p r m
  have hg := actual_pair_geometry hN a b c hd hl side p r
  have h := hb N hN a _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2 (physicalEndpoint a b side) m
    (fun j => meshScale N *
      ((patternTerm c side (p.castLE (patternCount_le_six c)) r.val).vector j : ℝ))
  have hs :
      (∑ j : Coordinate,
        (meshScale N * ((patternTerm c side (p.castLE (patternCount_le_six c)) r.val).vector j : ℝ)) ^ 2) =
      (meshScale N) ^ 2 * ∑ j : Coordinate,
        (((patternTerm c side (p.castLE (patternCount_le_six c)) r.val).vector j : ℝ)) ^ 2 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [hs] at h
  have hi := mul_le_mul_of_nonneg_left (real_vector_square_bound c side p r.val)
    (show 0 ≤ C * meshScale N * (meshScale N) ^ 2 by positivity [meshScale_pos N hN])
  change velocityEnergy (weightedTerm hN a b c hd hl side p r e q m) ≤ _ at h
  nlinarith

def weightedPattern {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e q : ℕ) (m : GridVertex N) : BrokenVelocity N :=
  ∑ r : ActiveTerm c side p, weightedTerm hN a b c hd hl side p r e q m

theorem weightedPattern_uniform_energy (e q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
      (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
      (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c)) (m : GridVertex N),
      velocityEnergy (weightedPattern hN a b c hd hl side p e q m) ≤ C * (meshScale N) ^ 3 := by
  classical
  obtain ⟨C, hC, hb⟩ := weightedTerm_uniform_energy e q
  refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN a b c hd hl side p m
  have hc : Fintype.card (ActiveTerm c side p) ≤ 2 := by
    simpa using Fintype.card_le_of_injective
      (fun r : ActiveTerm c side p => r.val) Subtype.val_injective
  have hcr : (Fintype.card (ActiveTerm c side p) : ℝ) ≤ 2 := by exact_mod_cast hc
  have hbase : 0 ≤ C * (meshScale N) ^ 3 := by positivity [meshScale_pos N hN]
  have hs := velocityEnergy_sum hN (Finset.univ : Finset (ActiveTerm c side p))
    (fun r => weightedTerm hN a b c hd hl side p r e q m)
  change velocityEnergy (weightedPattern hN a b c hd hl side p e q m) ≤
    (Fintype.card (ActiveTerm c side p) : ℝ) *
      ∑ r : ActiveTerm c side p, velocityEnergy (weightedTerm hN a b c hd hl side p r e q m) at hs
  calc
    _ ≤ _ := hs
    _ ≤ (Fintype.card (ActiveTerm c side p) : ℝ) *
        ∑ _r : ActiveTerm c side p, C * (meshScale N) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun r _ => hb N hN a b c hd hl side p r m)) (Nat.cast_nonneg _)
    _ = (Fintype.card (ActiveTerm c side p) : ℝ) ^ 2 * (C * (meshScale N) ^ 3) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ 4 * (C * (meshScale N) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ hbase
      have hnn : (0 : ℝ) ≤ (Fintype.card (ActiveTerm c side p) : ℝ) := Nat.cast_nonneg _
      nlinarith
    _ = _ := by ring

theorem weightedPattern_zero_power {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (m : GridVertex N) :
    weightedPattern hN a b c hd hl side p e 0 m = patternField hN a b c hd hl side p e := by
  funext t j
  simp only [weightedPattern, weightedTerm, patternField, termField, weightedFaceField,
    Finset.sum_apply, pow_zero, mul_one]

theorem weightedPattern_one_power {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side : Bool) (p : Fin (patternCount c))
    (e : ℕ) (m : GridVertex N) :
    weightedPattern hN a b c hd hl side p e 1 m =
      multiplyNode m (patternField hN a b c hd hl side p e) := by
  funext t j
  simp only [weightedPattern, weightedTerm, patternField, termField, weightedFaceField,
    Finset.sum_apply, multiplyNode, LinearMap.coe_mk, AddHom.coe_mk, pow_one, pow_zero,
    mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end FreudenthalSVLean.StableCanonicalPattern
