import FreudenthalSVLean.ActualCanonicalSource
import FreudenthalSVLean.PressureVertexBound
import FreudenthalSVLean.StableVertexLift

/-!
# Compatible actual canonical edge coefficients and explicit pattern weights

For manuscript Lemma `edge-star`, actual pressure in `Q_{h,4}` or
`Q_{h,5}` whose vertex values vanish has respectively two or three
compatible coefficient vectors on each canonical edge.  The compatibility
is derived from the pointwise actual-mesh theorem and exact polynomial
trace decompositions, not supplied as a hypothesis about the coefficients.
The explicit canonical inverse then gives pattern weights, with one
coefficient-square bound before every type and endpoint.

These are the data and inverse stages.  Realization of the pattern weights
by supported physical velocity polynomials is a separate obligation.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalSource
open FreudenthalSVLean.EdgePressureData
open FreudenthalSVLean.EdgeModeUnisolvence
open FreudenthalSVLean.PressureVertexBound
open FreudenthalSVLean.StableVertexLift

noncomputable section

namespace FreudenthalSVLean.ActualCanonicalData

def orderingLinear {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) : Data a b →ₗ[ℝ] (Fin (incidenceValence c) → ℝ) :=
  LinearMap.pi (fun i => LinearMap.proj (orderedActualEdge hN a b c hd hl i))

def orderedCoefficients {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (d : ℕ) (ν : Fin (d + 1)) :
    BrokenPressure N →ₗ[ℝ] (Fin (incidenceValence c) → ℝ) :=
  (orderingLinear hN a b c hd hl).comp (coefficientData a b d ν)

theorem ordered_cubic_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : BrokenPressure N)
    (hp : ∀ t, (q t).totalDegree ≤ 3) (hz : ∀ t l, eval (vertex t l) (q t) = 0) (s : ℝ) :
    orderedPressureTrace hN a b c hd hl q s =
      cubicTrace (orderedCoefficients hN a b c hd hl 3 1 q)
        (orderedCoefficients hN a b c hd hl 3 2 q) s := by
  funext i
  exact congrFun (cubic_trace_decomposition a b hab q hp hz s)
    (orderedActualEdge hN a b c hd hl i)

theorem ordered_quartic_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : BrokenPressure N)
    (hp : ∀ t, (q t).totalDegree ≤ 4) (hz : ∀ t l, eval (vertex t l) (q t) = 0) (s : ℝ) :
    orderedPressureTrace hN a b c hd hl q s =
      quarticTrace (orderedCoefficients hN a b c hd hl 4 1 q)
        (orderedCoefficients hN a b c hd hl 4 2 q)
        (orderedCoefficients hN a b c hd hl 4 3 q) s := by
  funext i
  exact congrFun (quartic_trace_decomposition a b hab q hp hz s)
    (orderedActualEdge hN a b c hd hl i)

/-- All actual quartic-stage endpoint coefficient vectors satisfy the
source relation forced by mesh conformity and boundary values. -/
theorem quartic_pressure_data {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : pressureSpace N 4)
    (hz : ∀ t l, eval (vertex t l) (q.val t) = 0) :
    orderedCoefficients hN a b c hd hl 3 1 q.val ∈ sourceSpace c ∧
      orderedCoefficients hN a b c hd hl 3 2 q.val ∈ sourceSpace c := by
  apply cubic_coefficients_mem (sourceSpace c)
  intro s hs
  rw [← ordered_cubic_trace hN a b hab c hd hl q.val (pressure_degree_bound q) hz s]
  exact pressure_canonical_trace_mem_source hN a b c hd hl q s hs

/-- All actual quintic-stage endpoint and middle coefficient vectors
satisfy the same canonical source relation. -/
theorem quintic_pressure_data {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (hab : a ≠ b)
    (c : Fin 7) (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : pressureSpace N 5)
    (hz : ∀ t l, eval (vertex t l) (q.val t) = 0) :
    orderedCoefficients hN a b c hd hl 4 1 q.val ∈ sourceSpace c ∧
      orderedCoefficients hN a b c hd hl 4 2 q.val ∈ sourceSpace c ∧
      orderedCoefficients hN a b c hd hl 4 3 q.val ∈ sourceSpace c := by
  apply quartic_coefficients_mem (sourceSpace c)
  intro s hs
  rw [← ordered_quartic_trace hN a b hab c hd hl q.val (pressure_degree_bound q) hz s]
  exact pressure_canonical_trace_mem_source hN a b c hd hl q s hs

/-- One common square bound for the explicit integer inverse family.
It is independent of the mesh and of the pressure datum. -/
theorem inverse_square_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (c : Fin 7) (side : Bool) (q : sourceSpace c),
      (∑ p : Fin (patternCount c), (inverseMap c side q.val p) ^ 2) ≤
        C * ∑ i : Fin (incidenceValence c), (q.val i) ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := fixed_inverse_bound
  refine ⟨6 * C ^ 2, by positivity, ?_⟩
  intro c side q
  have hi (p : Fin (patternCount c)) :
      (inverseMap c side q.val p) ^ 2 ≤ C ^ 2 * ‖q‖ ^ 2 := by
    have hn : |inverseMap c side q.val p| ≤ ‖inverseMap c side q.val‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (inverseMap c side q.val) p
    have he : |inverseMap c side q.val p| ≤ C * ‖q‖ := hn.trans (hb c side q)
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC.le (norm_nonneg q))).mpr he
  calc
    _ ≤ ∑ _p : Fin (patternCount c), C ^ 2 * ‖q‖ ^ 2 :=
      Finset.sum_le_sum (fun p _ => hi p)
    _ = (patternCount c : ℝ) * (C ^ 2 * ‖q‖ ^ 2) := by simp
    _ ≤ 6 * (C ^ 2 * ‖q‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast patternCount_le_six c) (by positivity)
    _ ≤ 6 * (C ^ 2 * ∑ i : Fin (incidenceValence c), (q.val i) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (pi_norm_square_le_sum q.val) (sq_nonneg C)
    _ = _ := by ring

/-- Ordered coefficient squares are exactly the actual incidence sum;
there is no factor depending on `N`. -/
theorem ordered_coefficient_squares {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (d : ℕ) (ν : Fin (d + 1)) (q : BrokenPressure N) :
    (∑ i : Fin (incidenceValence c), (orderedCoefficients hN a b c hd hl d ν q i) ^ 2) =
      ∑ x : ActualEdgeStar a b, (coefficientData a b d ν q x) ^ 2 :=
  (orderedActualEquiv hN a b c hd hl).sum_comp (fun x => (coefficientData a b d ν q x) ^ 2)

end FreudenthalSVLean.ActualCanonicalData
