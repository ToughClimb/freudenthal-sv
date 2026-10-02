import FreudenthalSVLean.StarMeanRouting
import FreudenthalSVLean.ConformingSkeletonBubble

/-!
# Exact means of the raw vertex edge-jet bubbles

For manuscript equations `vertex-raw-bubble` and `vertex-raw-properties`,
the true unit-element mean of `D_j(λ_a² λ_b)` is `(g_a,j+g_b,j)/60`
for distinct endpoints.  The proof uses the already derived simplex
integral formula and product differentiation, then transports the formula
to actual global nodal cubic fields at every positive mesh size.
Cancellation of the means over a complete active edge star is a separate
compatibility step, not assumed by this local mean calculation.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BernsteinMean
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.LowDegreeBubbleExpansion
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.ConformingSkeletonBubble

noncomputable section

namespace FreudenthalSVLean.RawVertexMean

theorem single_factorialProduct (a : Vertex) :
    factorialProduct (R := ℝ) (Finsupp.single a 1) = 1 := by
  apply Finset.prod_eq_one
  intro i _
  by_cases h : a = i <;> simp [h]

theorem pair_degree (a b : Vertex) :
    (Finsupp.single a 1 + Finsupp.single b 1 : Vertex →₀ ℕ).degree = 2 := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem pair_factorialProduct (a b : Vertex) :
    factorialProduct (R := ℝ) (Finsupp.single a 1 + Finsupp.single b 1) =
      if a = b then 2 else 1 := by
  rw [factorialProduct_raised, single_factorialProduct]
  by_cases h : a = b
  · simp [h]
    norm_num
  · simp [h]

theorem substitute_pair (σ : Equiv.Perm Coordinate) (o : Space) (a b : Vertex) :
    eval₂Hom C (ChainGeometry.barycentric σ o)
      (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : ℝ)) =
        ChainGeometry.barycentric σ o a * ChainGeometry.barycentric σ o b := by
  rw [monomial_add_single, ← C_mul_X_eq_monomial]
  simp only [map_mul, eval₂Hom_X', C_1, pow_one, one_mul]

theorem barycentric_product_mean (σ : Equiv.Perm Coordinate) (o : Space) (a b : Vertex) :
    unitSpatialIntegral σ o (ChainGeometry.barycentric σ o a * ChainGeometry.barycentric σ o b) =
      (if a = b then 2 else 1) / 120 := by
  rw [← substitute_pair, substitution_integral, monomial_mean, pair_degree, pair_factorialProduct]
  norm_num

theorem vertexBubble_derivative (σ : Equiv.Perm Coordinate) (o : Space)
    (a b : Vertex) (j : Coordinate) :
    pderiv j (SkeletonBubble.vertexBubble σ o a b) =
      C (2 * ChainGeometry.barycentricGradient σ a j) *
        (ChainGeometry.barycentric σ o a * ChainGeometry.barycentric σ o b) +
      C (ChainGeometry.barycentricGradient σ b j) * ChainGeometry.barycentric σ o a ^ 2 := by
  simp only [SkeletonBubble.vertexBubble, pderiv_mul, pderiv_pow,
    ChainGeometry.pderiv_barycentric, C_mul, map_ofNat]
  ring

theorem vertexBubble_derivative_mean (σ : Equiv.Perm Coordinate) (o : Space)
    (a b : Vertex) (hab : a ≠ b) (j : Coordinate) :
    unitSpatialIntegral σ o (pderiv j (SkeletonBubble.vertexBubble σ o a b)) =
      (ChainGeometry.barycentricGradient σ a j + ChainGeometry.barycentricGradient σ b j) / 60 := by
  rw [vertexBubble_derivative, map_add, unitSpatialIntegral_C_mul,
    unitSpatialIntegral_C_mul, pow_two, barycentric_product_mean, barycentric_product_mean]
  simp only [if_neg hab, ite_true]
  ring

theorem cubicField_mean {N : ℕ} (hN : 0 < N) (n m : Coordinate → ℤ) (s : Space)
    (t : Tet N) (a b : Vertex) (hab : a ≠ b)
    (hn : GridNodalSupport.intPoint n = chainVertex t.2 (cellOrigin t.1) a)
    (hm : GridNodalSupport.intPoint m = chainVertex t.2 (cellOrigin t.1) b) :
    (∫ x in tetrahedron t, eval x (divergence N (edgeBubbleField N 2 n m s) t)) =
      (meshScale N) ^ 2 * ∑ j : Coordinate,
        s j * (ChainGeometry.barycentricGradient t.2 a j +
          ChainGeometry.barycentricGradient t.2 b j) / 60 := by
  have hj (j : Coordinate) : tetIntegral hN t (pderiv j (edgeBubbleField N 2 n m s t j)) =
      (meshScale N) ^ 2 * (s j *
        (ChainGeometry.barycentricGradient t.2 a j +
          ChainGeometry.barycentricGradient t.2 b j) / 60) := by
    change (∫ x in ScaledChainGeometry.scaledChainSet t.2 (cellOrigin t.1) (meshScale N),
      eval x (pderiv j (edgeBubbleField N 2 n m s t j))) = _
    rw [cubicField_on_incident_tet n m s t a b hn hm j,
      derivative_mean_scaling t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN)]
    change s j * (meshScale N) ^ 2 *
      unitSpatialIntegral t.2 (cellOrigin t.1) (pderiv j (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b)) = _
    rw [vertexBubble_derivative_mean t.2 (cellOrigin t.1) a b hab j]
    ring
  change tetIntegral hN t (∑ j : Coordinate, pderiv j (edgeBubbleField N 2 n m s t j)) = _
  simp only [map_sum, hj, Finset.mul_sum]

end FreudenthalSVLean.RawVertexMean
