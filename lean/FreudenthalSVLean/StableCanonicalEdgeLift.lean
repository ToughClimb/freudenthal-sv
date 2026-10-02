import FreudenthalSVLean.StableCanonicalPattern

/-!
# Uniform energy of the actual canonical incidence lift maps

For manuscript Lemma edge-star, the explicit fixed incidence inverse
and actual pattern generators give an h-independent bound C h cubed
times the sum of input coefficient squares. Both quartic endpoint
lifts and their nodally multiplied quintic endpoint/middle lifts use
one constant before all mesh and edge parameters. This is an estimate
of the actual whole-mesh Lebesgue gradient energy, not a matrix norm
substituted for that energy. Arbitrary-orientation transport and mean
correction remain separate.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalFaces
open FreudenthalSVLean.ActualCanonicalData
open FreudenthalSVLean.ActualCanonicalEdgeLift
open FreudenthalSVLean.ConformingNodalMultiplication
open FreudenthalSVLean.StableCanonicalPattern
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableCanonicalEdgeLift

theorem generator_sum_energy {N : ℕ} (hN : 0 < N) (c : Fin 7)
    (g : Fin (patternCount c) → BrokenVelocity N) (w : Fin (patternCount c) → ℝ)
    (G : ℝ) (hG : 0 ≤ G) (hg : ∀ p, velocityEnergy (g p) ≤ G * (meshScale N) ^ 3) :
    velocityEnergy (∑ p : Fin (patternCount c), w p • g p) ≤
      6 * G * (meshScale N) ^ 3 * ∑ p : Fin (patternCount c), (w p) ^ 2 := by
  classical
  have hc : (patternCount c : ℝ) ≤ 6 := by exact_mod_cast patternCount_le_six c
  calc
    _ ≤ (patternCount c : ℝ) * ∑ p : Fin (patternCount c), velocityEnergy (w p • g p) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        velocityEnergy_sum hN (Finset.univ : Finset (Fin (patternCount c))) (fun p => w p • g p)
    _ = (patternCount c : ℝ) * ∑ p : Fin (patternCount c), (w p) ^ 2 * velocityEnergy (g p) := by
      simp only [velocityEnergy_smul]
    _ ≤ (patternCount c : ℝ) * ∑ p : Fin (patternCount c), (w p) ^ 2 * (G * (meshScale N) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hg p) (sq_nonneg _))
    _ = (patternCount c : ℝ) * (G * (meshScale N) ^ 3) *
        ∑ p : Fin (patternCount c), (w p) ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ 6 * (G * (meshScale N) ^ 3) * ∑ p : Fin (patternCount c), (w p) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul_of_nonneg_right hc
        (mul_nonneg hG (pow_nonneg (meshScale_pos N hN).le _))
    _ = _ := by ring

theorem hatEndpointLift_val {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (side multiplier : Bool) (q : sourceSpace c) :
    (hatEndpointLift hN a b c hd hl side multiplier q).val =
      ∑ p : Fin (patternCount c), (inverseMap c side q.val p) •
        multiplyNode (physicalEndpoint a b multiplier) (patternField hN a b c hd hl side p 1) := by
  change multiplyNode (physicalEndpoint a b multiplier)
    (patternLinear hN a b c hd hl side 1 (by norm_num) (inverseMap c side q.val)).val = _
  rw [patternLinear_val, map_sum]
  simp only [map_smul]

/-- Uniform physical bounds for both degrees' fixed endpoint maps, including
the quintic middle map with first endpoint pattern and second endpoint hat. -/
theorem uniform_endpoint_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
      (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
      (hl : CanonicalLocation a c) (side : Bool) (q : sourceSpace c),
      velocityEnergy (endpointLift hN a b c hd hl side q).val ≤
        C * (meshScale N) ^ 3 * ∑ i : Fin (incidenceValence c), (q.val i) ^ 2 ∧
      ∀ multiplier : Bool,
      velocityEnergy (hatEndpointLift hN a b c hd hl side multiplier q).val ≤
        C * (meshScale N) ^ 3 * ∑ i : Fin (incidenceValence c), (q.val i) ^ 2 := by
  classical
  obtain ⟨G₀, hG₀, hb₀⟩ := weightedPattern_uniform_energy 1 0
  obtain ⟨G₁, hG₁, hb₁⟩ := weightedPattern_uniform_energy 1 1
  obtain ⟨J, hJ, hInv⟩ := inverse_square_bound
  let G := G₀ + G₁
  have hG : 0 < G := add_pos hG₀ hG₁
  refine ⟨6 * G * J, by positivity, ?_⟩
  intro N hN a b c hd hl side q
  have hdata := hInv c side q
  have hscale : 0 ≤ 6 * G * (meshScale N) ^ 3 := by positivity [meshScale_pos N hN]
  have hright := mul_le_mul_of_nonneg_left hdata hscale
  have hgen₀ (p : Fin (patternCount c)) :
      velocityEnergy (patternField hN a b c hd hl side p 1) ≤ G * (meshScale N) ^ 3 := by
    have h := hb₀ N hN a b c hd hl side p a
    rw [weightedPattern_zero_power] at h
    have hG₀' : G₀ ≤ G := by dsimp [G]; linarith
    exact h.trans (mul_le_mul_of_nonneg_right hG₀' (pow_nonneg (meshScale_pos N hN).le _))
  constructor
  · have h := generator_sum_energy hN c (fun p => patternField hN a b c hd hl side p 1)
      (inverseMap c side q.val) G hG.le hgen₀
    change velocityEnergy (patternLinear hN a b c hd hl side 1 (by norm_num)
      (inverseMap c side q.val)).val ≤ _
    rw [patternLinear_val]
    nlinarith
  · intro multiplier
    have hgen₁ (p : Fin (patternCount c)) :
        velocityEnergy (multiplyNode (physicalEndpoint a b multiplier)
          (patternField hN a b c hd hl side p 1)) ≤ G * (meshScale N) ^ 3 := by
      have h := hb₁ N hN a b c hd hl side p (physicalEndpoint a b multiplier)
      rw [weightedPattern_one_power] at h
      have hG₁' : G₁ ≤ G := by dsimp [G]; linarith
      exact h.trans (mul_le_mul_of_nonneg_right hG₁' (pow_nonneg (meshScale_pos N hN).le _))
    have h := generator_sum_energy hN c
      (fun p => multiplyNode (physicalEndpoint a b multiplier) (patternField hN a b c hd hl side p 1))
      (inverseMap c side q.val) G hG.le hgen₁
    rw [hatEndpointLift_val]
    nlinarith

theorem add_energy_bound {N : ℕ} (hN : 0 < N) (v w : BrokenVelocity N) :
    velocityEnergy (v + w) ≤ 2 * (velocityEnergy v + velocityEnergy w) := by
  have h := velocityEnergy_sum hN (Finset.univ : Finset (Fin 2)) ![v, w]
  simpa [Fin.sum_univ_succ] using h

theorem triple_energy_bound {N : ℕ} (hN : 0 < N) (v w u : BrokenVelocity N) :
    velocityEnergy (v + w + u) ≤ 3 * (velocityEnergy v + velocityEnergy w + velocityEnergy u) := by
  have h := velocityEnergy_sum hN (Finset.univ : Finset (Fin 3)) ![v, w, u]
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- The complete two-mode and three-mode canonical edge maps have one
mesh-independent physical energy constant on all compatible inputs. -/
theorem uniform_canonical_lift_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
      (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
      (hl : CanonicalLocation a c),
      (∀ q : sourceSpace c × sourceSpace c,
        velocityEnergy (quarticLift hN a b c hd hl q).val ≤ C * (meshScale N) ^ 3 *
          ((∑ i : Fin (incidenceValence c), (q.1.val i) ^ 2) +
            (∑ i : Fin (incidenceValence c), (q.2.val i) ^ 2))) ∧
      (∀ q : sourceSpace c × sourceSpace c × sourceSpace c,
        velocityEnergy (quinticLift hN a b c hd hl q).val ≤ C * (meshScale N) ^ 3 *
          ((∑ i : Fin (incidenceValence c), (q.1.val i) ^ 2) +
            (∑ i : Fin (incidenceValence c), (q.2.1.val i) ^ 2) +
            (∑ i : Fin (incidenceValence c), (q.2.2.val i) ^ 2))) := by
  obtain ⟨C, hC, hb⟩ := uniform_endpoint_energy
  refine ⟨6 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN a b c hd hl
  have hs (q : sourceSpace c) : 0 ≤ C * (meshScale N) ^ 3 *
      ∑ i : Fin (incidenceValence c), (q.val i) ^ 2 :=
    mul_nonneg (mul_nonneg hC.le (pow_nonneg (meshScale_pos N hN).le _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  constructor
  · intro q
    have h₁ := (hb N hN a b c hd hl false q.1).1
    have h₂ := (hb N hN a b c hd hl true q.2).1
    have hsum := add_energy_bound hN (endpointLift hN a b c hd hl false q.1).val
      (endpointLift hN a b c hd hl true q.2).val
    change velocityEnergy ((endpointLift hN a b c hd hl false q.1).val +
      (endpointLift hN a b c hd hl true q.2).val) ≤ _
    nlinarith [hs q.1, hs q.2]
  · intro q
    have h₁ := (hb N hN a b c hd hl false q.1).2 false
    have h₂ := (hb N hN a b c hd hl false q.2.1).2 true
    have h₃ := (hb N hN a b c hd hl true q.2.2).2 true
    have hsum := triple_energy_bound hN (hatEndpointLift hN a b c hd hl false false q.1).val
      (hatEndpointLift hN a b c hd hl false true q.2.1).val
      (hatEndpointLift hN a b c hd hl true true q.2.2).val
    change velocityEnergy ((hatEndpointLift hN a b c hd hl false false q.1).val +
      (hatEndpointLift hN a b c hd hl false true q.2.1).val +
      (hatEndpointLift hN a b c hd hl true true q.2.2).val) ≤ _
    nlinarith [hs q.1, hs q.2.1, hs q.2.2]

end FreudenthalSVLean.StableCanonicalEdgeLift
