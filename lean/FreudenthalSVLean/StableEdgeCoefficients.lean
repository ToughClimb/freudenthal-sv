import FreudenthalSVLean.ActualPressureEdgeModes
import FreudenthalSVLean.FiniteLinearLifting

/-!
# Uniform actual-volume control of edge coefficient data

For the edge-stage estimate in manuscript Lemma `edge-star`, the
coefficients of the actual barycentric edge expansion are bounded in the
genuine tetrahedron volume norm.  The reference coefficient maps are
fixed linear maps on the fixed-degree polynomial space with its already
proved Lebesgue `L²` norm.  A finite family over endpoint indices gives a
single constant, and the actual element pullback gives exactly the factor
`h³`.  No assumed coefficient norm or scale-dependent operator bound is
introduced.

The estimate controls the coefficient data; stability of the supported
edge lifting map itself is a separate obligation.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.HomogeneousBarycentric
open FreudenthalSVLean.HomogeneousEdgeModes
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.PolynomialL2Space
open FreudenthalSVLean.FiniteLinearLifting
open FreudenthalSVLean.ActualPressureEdgeModes

noncomputable section

namespace FreudenthalSVLean.StableEdgeCoefficients

def referenceCoefficients (a b : Vertex) (d : ℕ) : degreeSpace d →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  LinearMap.pi (fun ν => (lcoeff ℝ (edgeExponent a b d ν)).comp
    ((representationLinear (Equiv.refl Coordinate) (0 : Space) d).comp (degreeSpace d).subtype))

theorem reference_coefficients_bound (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (a b : Vertex) (p : degreeSpace d), ‖referenceCoefficients a b d p‖ ≤ C * ‖p‖ := by
  obtain ⟨C, hC, hb⟩ := finite_family_map_bounds
    (fun _ : Vertex × Vertex => degreeSpace d)
    (fun _ : Vertex × Vertex => Fin (d + 1) → ℝ)
    (fun ab => referenceCoefficients ab.1 ab.2 d)
  exact ⟨C, hC, fun a b p => hb (a, b) p⟩

/-- One positive constant is selected before mesh size, element,
orientation, endpoint pair, and input polynomial. -/
theorem physical_coefficients_bound (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N) (t : Tet N) (a b : Vertex) (p : Poly),
      p.totalDegree ≤ d →
      (meshScale N) ^ 3 * (∑ ν : Fin (d + 1), (edgeCoefficients t a b d p ν) ^ 2) ≤
        C * ∫ x in tetrahedron t, (eval x p) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := reference_coefficients_bound d
  refine ⟨(d + 1 : ℝ) * C ^ 2, by positivity, ?_⟩
  intro N hN t a b p hp
  let q : degreeSpace d := ⟨PolynomialInverseEstimate.pullback t.2 (cellOrigin t.1) (meshScale N) p,
    (mem_restrictTotalDegree _ _ _).mpr
      ((PolynomialInverseEstimate.pullback_degree _ _ _ p).trans hp)⟩
  have hnorm : ‖q‖ ^ 2 = referenceSquareIntegral q.val := norm_square_eq_integral q.val
  have hsq (ν : Fin (d + 1)) : (edgeCoefficients t a b d p ν) ^ 2 ≤
      C ^ 2 * referenceSquareIntegral q.val := by
    have hn := (norm_le_pi_norm (referenceCoefficients a b d q) ν).trans (hb a b q)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg q))).mpr hn
    change ‖edgeCoefficients t a b d p ν‖ ^ 2 ≤ (C * ‖q‖) ^ 2 at hs
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, hnorm] using hs
  calc
    _ ≤ (meshScale N) ^ 3 * ∑ _ν : Fin (d + 1), C ^ 2 * referenceSquareIntegral q.val := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ν _ => hsq ν))
      positivity [meshScale_pos N hN]
    _ = ((d + 1 : ℝ) * C ^ 2) * ((meshScale N) ^ 3 * referenceSquareIntegral q.val) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring
    _ = _ := by
      rw [← PolynomialInverseEstimate.pullback_square_integral t.2 (cellOrigin t.1) (meshScale N)
        (meshScale_pos N hN) p]
      rfl

end FreudenthalSVLean.StableEdgeCoefficients
