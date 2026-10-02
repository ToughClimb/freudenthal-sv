import FreudenthalSVLean.ActualEdgeCoverage
import FreudenthalSVLean.StableEdgeCoefficients
import FreudenthalSVLean.EdgeModeUnisolvence

/-!
# Complete actual edge-star pressure data

For manuscript Lemma `edge-star`, the fixed physical edge and its actual
incident tetrahedra define linear trace and coefficient maps.  The complete
cubic/quartic trace decompositions are proved for actual broken pressure
polynomials with zero vertex values.  Any pointwise linear compatibility
subspace therefore contains every extracted endpoint/middle coefficient
vector.  The coefficient-square bound uses actual element integrals and
one constant before every mesh and edge parameter.

The concrete source subspaces, supported lifting maps, and their global
assembly are separate obligations; no edge lifting theorem is assumed
by these pressure-data statements.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.ActualPressureEdgeModes
open FreudenthalSVLean.StableEdgeCoefficients
open FreudenthalSVLean.EdgeModeUnisolvence

noncomputable section

namespace FreudenthalSVLean.EdgePressureData

abbrev Data {N : ℕ} (a b : GridVertex N) := ActualEdgeStar a b → ℝ

def pressureTrace {N : ℕ} (a b : GridVertex N) (s : ℝ) : BrokenPressure N →ₗ[ℝ] Data a b where
  toFun q x := eval (segmentPoint (gridPoint a) (gridPoint b) s) (q x.val.1.val.1)
  map_add' p q := by
    funext x
    simp only [Pi.add_apply, map_add]
  map_smul' c p := by
    funext x
    simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, RingHom.id_apply, smul_eq_mul]

def coefficientData {N : ℕ} (a b : GridVertex N) (d : ℕ) (ν : Fin (d + 1)) :
    BrokenPressure N →ₗ[ℝ] Data a b :=
  LinearMap.pi (fun x => (LinearMap.proj ν).comp
    ((edgeCoefficients x.val.1.val.1 x.val.1.val.2 x.val.2 d).comp
      (LinearMap.proj x.val.1.val.1)))

theorem coefficientData_apply {N : ℕ} (a b : GridVertex N) (d : ℕ) (ν : Fin (d + 1))
    (q : BrokenPressure N) (x : ActualEdgeStar a b) :
    coefficientData a b d ν q x =
      edgeCoefficients x.val.1.val.1 x.val.1.val.2 x.val.2 d (q x.val.1.val.1) ν := rfl

theorem first_physical_endpoint {N : ℕ} (a b : GridVertex N) (x : ActualEdgeStar a b) :
    vertex x.val.1.val.1 x.val.1.val.2 = gridPoint a := by
  rw [← gridVertexOfTet_point, x.val.1.property]

theorem second_physical_endpoint {N : ℕ} (a b : GridVertex N) (x : ActualEdgeStar a b) :
    vertex x.val.1.val.1 x.val.2 = gridPoint b := by
  rw [← gridVertexOfTet_point, x.property]

theorem local_endpoint_distinct {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (x : ActualEdgeStar a b) : x.val.1.val.2 ≠ x.val.2 := by
  intro h
  apply hab
  calc
    a = gridVertexOfTet x.val.1.val.1 x.val.1.val.2 := x.val.1.property.symm
    _ = gridVertexOfTet x.val.1.val.1 x.val.2 := congrArg (gridVertexOfTet x.val.1.val.1) h
    _ = b := x.property

theorem cubic_trace_decomposition {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (q : BrokenPressure N) (hp : ∀ t, (q t).totalDegree ≤ 3)
    (hz : ∀ t l, eval (vertex t l) (q t) = 0) (s : ℝ) :
    pressureTrace a b s q = cubicTrace (coefficientData a b 3 1 q) (coefficientData a b 3 2 q) s := by
  funext x
  have he := cubic_physical_zero_endpoint_trace x.val.1.val.1 (q x.val.1.val.1)
    (hp _) x.val.1.val.2 x.val.2 (local_endpoint_distinct a b hab x) (hz _ _) (hz _ _) s
  rw [first_physical_endpoint a b x, second_physical_endpoint a b x] at he
  change eval (segmentPoint (gridPoint a) (gridPoint b) s) (q x.val.1.val.1) = _
  rw [he]
  change _ = ((1 - s) ^ 2 * s) * coefficientData a b 3 1 q x +
    ((1 - s) * s ^ 2) * coefficientData a b 3 2 q x
  rw [coefficientData_apply, coefficientData_apply]
  ring

theorem quartic_trace_decomposition {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (q : BrokenPressure N) (hp : ∀ t, (q t).totalDegree ≤ 4)
    (hz : ∀ t l, eval (vertex t l) (q t) = 0) (s : ℝ) :
    pressureTrace a b s q = quarticTrace (coefficientData a b 4 1 q)
      (coefficientData a b 4 2 q) (coefficientData a b 4 3 q) s := by
  funext x
  have he := quartic_physical_zero_endpoint_trace x.val.1.val.1 (q x.val.1.val.1)
    (hp _) x.val.1.val.2 x.val.2 (local_endpoint_distinct a b hab x) (hz _ _) (hz _ _) s
  rw [first_physical_endpoint a b x, second_physical_endpoint a b x] at he
  change eval (segmentPoint (gridPoint a) (gridPoint b) s) (q x.val.1.val.1) = _
  rw [he]
  change _ = ((1 - s) ^ 3 * s) * coefficientData a b 4 1 q x +
    ((1 - s) ^ 2 * s ^ 2) * coefficientData a b 4 2 q x +
    ((1 - s) * s ^ 3) * coefficientData a b 4 3 q x
  rw [coefficientData_apply, coefficientData_apply, coefficientData_apply]
  ring

theorem cubic_data_compatibility {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (q : BrokenPressure N) (hp : ∀ t, (q t).totalDegree ≤ 3)
    (hz : ∀ t l, eval (vertex t l) (q t) = 0) (C : Submodule ℝ (Data a b))
    (hc : ∀ s ∈ Icc (0 : ℝ) 1, pressureTrace a b s q ∈ C) :
    coefficientData a b 3 1 q ∈ C ∧ coefficientData a b 3 2 q ∈ C := by
  apply cubic_coefficients_mem C
  intro s hs
  rw [← cubic_trace_decomposition a b hab q hp hz s]
  exact hc s hs

theorem quartic_data_compatibility {N : ℕ} (a b : GridVertex N) (hab : a ≠ b)
    (q : BrokenPressure N) (hp : ∀ t, (q t).totalDegree ≤ 4)
    (hz : ∀ t l, eval (vertex t l) (q t) = 0) (C : Submodule ℝ (Data a b))
    (hc : ∀ s ∈ Icc (0 : ℝ) 1, pressureTrace a b s q ∈ C) :
    coefficientData a b 4 1 q ∈ C ∧ coefficientData a b 4 2 q ∈ C ∧
      coefficientData a b 4 3 q ∈ C := by
  apply quartic_coefficients_mem C
  intro s hs
  rw [← quartic_trace_decomposition a b hab q hp hz s]
  exact hc s hs

theorem edge_data_square_bound (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N) (a b : GridVertex N) (q : BrokenPressure N),
      (∀ t, (q t).totalDegree ≤ d) →
      (meshScale N) ^ 3 *
        (∑ x : ActualEdgeStar a b, ∑ ν : Fin (d + 1), (coefficientData a b d ν q x) ^ 2) ≤
        C * ∑ x : ActualEdgeStar a b, ∫ y in tetrahedron x.val.1.val.1, (eval y (q x.val.1.val.1)) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := physical_coefficients_bound d
  refine ⟨C, hC, ?_⟩
  intro N hN a b q hp
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  exact hb N hN x.val.1.val.1 x.val.1.val.2 x.val.2 (q x.val.1.val.1) (hp _)

end FreudenthalSVLean.EdgePressureData
