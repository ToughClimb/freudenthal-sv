import FreudenthalSVLean.StableCanonicalEdgeLift
import FreudenthalSVLean.CanonicalEdgeProtection

/-!
# Fixed canonical edge maps on actual vertex-zero pressures

For manuscript Lemma `edge-lift`, compatible coefficient vectors are
extracted by fixed linear maps from the actual divergence image.  They
are not supplied as additional hypotheses on an enlarged pressure space.
The quartic and quintic constructions match the full edge polynomial,
preserve all other edge traces and vertex derivatives, and have an
integral energy bound by the pressure energy on the actual edge star.
Preservation of element means is a subsequent, separate routing stage.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.CanonicalPatternSpan
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.ActualCanonicalSource
open FreudenthalSVLean.ActualCanonicalData
open FreudenthalSVLean.EdgePressureData
open FreudenthalSVLean.ActualCanonicalEdgeLift
open FreudenthalSVLean.CanonicalEdgeProtection
open FreudenthalSVLean.StableCanonicalEdgeLift

noncomputable section

namespace FreudenthalSVLean.CanonicalPressureLift

set_option backward.isDefEq.respectTransparency false

def vertexZeroSpace (N k : ℕ) : Submodule ℝ (BrokenPressure N) where
  carrier := {q | q ∈ pressureSpace N k ∧ ∀ t l, eval (vertex t l) (q t) = 0}
  zero_mem' := ⟨(pressureSpace N k).zero_mem, by intros; simp⟩
  add_mem' := by
    rintro p q ⟨hp, hzp⟩ ⟨hq, hzq⟩
    refine ⟨(pressureSpace N k).add_mem hp hq, ?_⟩
    intro t l
    simp only [Pi.add_apply, map_add, hzp, hzq, add_zero]
  smul_mem' := by
    rintro c q ⟨hq, hzq⟩
    refine ⟨(pressureSpace N k).smul_mem c hq, ?_⟩
    intro t l
    simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, hzq, mul_zero]

def asPressure {N k : ℕ} (q : vertexZeroSpace N k) : pressureSpace N k :=
  ⟨q.val, q.property.1⟩

def compatibleCoefficient {N k : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (d : ℕ) (ν : Fin (d + 1))
    (hc : ∀ q : vertexZeroSpace N k, orderedCoefficients hN a b c hd hl d ν q.val ∈ sourceSpace c) :
    vertexZeroSpace N k →ₗ[ℝ] sourceSpace c :=
  ((orderedCoefficients hN a b c hd hl d ν).comp (vertexZeroSpace N k).subtype).codRestrict _ hc

def quarticData {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) :
    vertexZeroSpace N 4 →ₗ[ℝ] sourceSpace c × sourceSpace c :=
  (compatibleCoefficient hN a b c hd hl 3 1 (fun q =>
    (quartic_pressure_data hN a b (canonical_endpoints_distinct a b c hd)
      c hd hl (asPressure q) q.property.2).1)).prod
    (compatibleCoefficient hN a b c hd hl 3 2 (fun q =>
      (quartic_pressure_data hN a b (canonical_endpoints_distinct a b c hd)
        c hd hl (asPressure q) q.property.2).2))

def quinticData {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) :
    vertexZeroSpace N 5 →ₗ[ℝ] sourceSpace c × sourceSpace c × sourceSpace c :=
  (compatibleCoefficient hN a b c hd hl 4 1 (fun q =>
    (quintic_pressure_data hN a b (canonical_endpoints_distinct a b c hd)
      c hd hl (asPressure q) q.property.2).1)).prod
    ((compatibleCoefficient hN a b c hd hl 4 2 (fun q =>
      (quintic_pressure_data hN a b (canonical_endpoints_distinct a b c hd)
        c hd hl (asPressure q) q.property.2).2.1)).prod
      (compatibleCoefficient hN a b c hd hl 4 3 (fun q =>
        (quintic_pressure_data hN a b (canonical_endpoints_distinct a b c hd)
          c hd hl (asPressure q) q.property.2).2.2)))

def quarticMap {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4 :=
  (quarticLift hN a b c hd hl).comp (quarticData hN a b c hd hl)

def quinticMap {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5 :=
  (quinticLift hN a b c hd hl).comp (quinticData hN a b c hd hl)

theorem quarticMap_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 4) (x : ActualEdgeStar a b) (s : ℝ) :
    pressureTrace a b s (divergence N (quarticMap hN a b c hd hl q).val) x =
      pressureTrace a b s q.val x := by
  let i := (orderedActualEquiv hN a b c hd hl).symm x
  have he := congrFun (quartic_pressure_trace hN a b (canonical_endpoints_distinct a b c hd)
    c hd hl (asPressure q) q.property.2 s) i
  change pressureTrace a b s (divergence N (quarticMap hN a b c hd hl q).val)
    (orderedActualEquiv hN a b c hd hl i) =
      pressureTrace a b s q.val (orderedActualEquiv hN a b c hd hl i) at he
  simpa only [i, Equiv.apply_symm_apply] using he

theorem quinticMap_trace {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 5) (x : ActualEdgeStar a b) (s : ℝ) :
    pressureTrace a b s (divergence N (quinticMap hN a b c hd hl q).val) x =
      pressureTrace a b s q.val x := by
  let i := (orderedActualEquiv hN a b c hd hl).symm x
  have he := congrFun (quintic_pressure_trace hN a b (canonical_endpoints_distinct a b c hd)
    c hd hl (asPressure q) q.property.2 s) i
  change pressureTrace a b s (divergence N (quinticMap hN a b c hd hl q).val)
    (orderedActualEquiv hN a b c hd hl i) =
      pressureTrace a b s q.val (orderedActualEquiv hN a b c hd hl i) at he
  simpa only [i, Equiv.apply_symm_apply] using he

theorem quarticMap_vertex {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 4) (t : Tet N) (l : Vertex)
    (i j : Coordinate) : eval (vertex t l) (pderiv i ((quarticMap hN a b c hd hl q).val t j)) = 0 :=
  quarticLift_vertex_derivative hN a b c hd hl _ t l i j

theorem quinticMap_vertex {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 5) (t : Tet N) (l : Vertex)
    (i j : Coordinate) : eval (vertex t l) (pderiv i ((quinticMap hN a b c hd hl q).val t j)) = 0 :=
  quinticLift_vertex_derivative hN a b c hd hl _ t l i j

theorem quarticMap_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 4) (t : Tet N) (l m : Vertex)
    (hlm : l ≠ m) (he : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (s : ℝ) : eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (quarticMap hN a b c hd hl q).val t) = 0 :=
  quarticLift_other_edge hN a b c hd hl _ t l m hlm he s

theorem quinticMap_other_edge {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation a c) (q : vertexZeroSpace N 5) (t : Tet N) (l m : Vertex)
    (hlm : l ≠ m) (he : ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b})
    (s : ℝ) : eval (segmentPoint (vertex t l) (vertex t m) s)
      (divergence N (quinticMap hN a b c hd hl q).val t) = 0 :=
  quinticLift_other_edge hN a b c hd hl _ t l m hlm he s

def starPressureEnergy {N : ℕ} (a b : GridVertex N) (q : BrokenPressure N) : ℝ :=
  ∑ x : ActualEdgeStar a b, ∫ y in tetrahedron x.val.1.val.1, (eval y (q x.val.1.val.1)) ^ 2

theorem mode_squares_le_all {N : ℕ} (a b : GridVertex N) (d : ℕ)
    (modes : Finset (Fin (d + 1))) (q : BrokenPressure N) :
    (∑ ν ∈ modes, ∑ x : ActualEdgeStar a b, (coefficientData a b d ν q x) ^ 2) ≤
      ∑ x : ActualEdgeStar a b, ∑ ν : Fin (d + 1), (coefficientData a b d ν q x) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ modes)
    (fun _ _ _ => sq_nonneg _)

/-- The canonical maps are bounded by actual local pressure integrals;
the constant is chosen before both the mesh size and the seven types. -/
theorem canonical_pressure_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
      (hd : displacement a b = positiveDirection (canonicalDirectionIndex c))
      (hl : CanonicalLocation a c),
      (∀ q : vertexZeroSpace N 4,
        velocityEnergy (quarticMap hN a b c hd hl q).val ≤ C * starPressureEnergy a b q.val) ∧
      (∀ q : vertexZeroSpace N 5,
        velocityEnergy (quinticMap hN a b c hd hl q).val ≤ C * starPressureEnergy a b q.val) := by
  obtain ⟨A, hA, hLift⟩ := uniform_canonical_lift_energy
  obtain ⟨B, hB, hCoeff3⟩ := edge_data_square_bound 3
  obtain ⟨D, hD, hCoeff4⟩ := edge_data_square_bound 4
  refine ⟨A * (B + D), by positivity, ?_⟩
  intro N hN a b c hd hl
  have hs : 0 ≤ (meshScale N) ^ 3 := pow_nonneg (meshScale_pos N hN).le _
  have hp (q : BrokenPressure N) : 0 ≤ starPressureEnergy a b q :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  constructor
  · intro q
    have h₀ := (hLift N hN a b c hd hl).1 (quarticData hN a b c hd hl q)
    have h₁ := hCoeff3 N hN a b q.val (PressureVertexBound.pressure_degree_bound (asPressure q))
    have h₂ := mode_squares_le_all a b 3 ({1, 2} : Finset (Fin 4)) q.val
    have h₂' : ((∑ x : ActualEdgeStar a b, (coefficientData a b 3 1 q.val x) ^ 2) +
        (∑ x : ActualEdgeStar a b, (coefficientData a b 3 2 q.val x) ^ 2)) ≤
        ∑ x : ActualEdgeStar a b, ∑ ν : Fin 4, (coefficientData a b 3 ν q.val x) ^ 2 := by
      simpa using h₂
    change velocityEnergy (quarticMap hN a b c hd hl q).val ≤ A * (meshScale N) ^ 3 *
      ((∑ i, (orderedCoefficients hN a b c hd hl 3 1 q.val i) ^ 2) +
        (∑ i, (orderedCoefficients hN a b c hd hl 3 2 q.val i) ^ 2)) at h₀
    rw [ordered_coefficient_squares, ordered_coefficient_squares] at h₀
    calc
      _ ≤ A * ((meshScale N) ^ 3 *
          (∑ x : ActualEdgeStar a b, ∑ ν : Fin 4, (coefficientData a b 3 ν q.val x) ^ 2)) :=
        h₀.trans (by nlinarith [mul_le_mul_of_nonneg_left h₂' (mul_nonneg hA.le hs)])
      _ ≤ A * (B * starPressureEnergy a b q.val) :=
        mul_le_mul_of_nonneg_left h₁ hA.le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD.le) hA.le) (hp q.val)
  · intro q
    have h₀ := (hLift N hN a b c hd hl).2 (quinticData hN a b c hd hl q)
    have h₁ := hCoeff4 N hN a b q.val (PressureVertexBound.pressure_degree_bound (asPressure q))
    have h₂ := mode_squares_le_all a b 4 ({1, 2, 3} : Finset (Fin 5)) q.val
    have h₂' : ((∑ x : ActualEdgeStar a b, (coefficientData a b 4 1 q.val x) ^ 2) +
        (∑ x : ActualEdgeStar a b, (coefficientData a b 4 2 q.val x) ^ 2) +
        (∑ x : ActualEdgeStar a b, (coefficientData a b 4 3 q.val x) ^ 2)) ≤
        ∑ x : ActualEdgeStar a b, ∑ ν : Fin 5, (coefficientData a b 4 ν q.val x) ^ 2 := by
      simpa [add_assoc] using h₂
    change velocityEnergy (quinticMap hN a b c hd hl q).val ≤ A * (meshScale N) ^ 3 *
      ((∑ i, (orderedCoefficients hN a b c hd hl 4 1 q.val i) ^ 2) +
        (∑ i, (orderedCoefficients hN a b c hd hl 4 2 q.val i) ^ 2) +
        (∑ i, (orderedCoefficients hN a b c hd hl 4 3 q.val i) ^ 2)) at h₀
    rw [ordered_coefficient_squares, ordered_coefficient_squares, ordered_coefficient_squares] at h₀
    calc
      _ ≤ A * ((meshScale N) ^ 3 *
          (∑ x : ActualEdgeStar a b, ∑ ν : Fin 5, (coefficientData a b 4 ν q.val x) ^ 2)) :=
        h₀.trans (by nlinarith [mul_le_mul_of_nonneg_left h₂' (mul_nonneg hA.le hs)])
      _ ≤ A * (D * starPressureEnergy a b q.val) :=
        mul_le_mul_of_nonneg_left h₁ hA.le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hB.le) hA.le) (hp q.val)

end FreudenthalSVLean.CanonicalPressureLift
