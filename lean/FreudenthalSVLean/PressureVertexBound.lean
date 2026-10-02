import FreudenthalSVLean.PolynomialInverseEstimate

/-!
# Uniform control of all pressure vertex incidences

The last estimate in manuscript Proposition `vertex` sums the fixed-degree
inverse estimate over tetrahedron--vertex incidences.  This module proves
the pressure degree bound from the exact image definition
`Q_{h,k}=div V_{h,k}`, then proves the summed inverse estimate using actual
polynomials and volume integrals for every `N≥1`.  The constant is selected
before `N`.  Construction and stability of the supported vertex-star
operator itself remain separate obligations.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.PolynomialInverseEstimate

noncomputable section

namespace FreudenthalSVLean.PressureVertexBound

theorem pressure_degree_bound {N k : ℕ} (q : pressureSpace N k) (t : Tet N) :
    (q.val t).totalDegree ≤ k - 1 := by
  obtain ⟨v, hv, hq⟩ := q.property
  rw [← hq]
  change (∑ j : Fin 3, pderiv j (v t j)).totalDegree ≤ k - 1
  apply totalDegree_finsetSum_le
  intro j _
  exact (PolynomialDegree.pderiv_degree_le j (v t j)).trans
    (Nat.sub_le_sub_right (hv.1 t j) 1)

/-- The data estimate in the vertex-stage global stability proof, including
boundary incidences and the meshes `N=1,2`. -/
theorem pressure_vertex_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ q : pressureSpace N k,
      (meshScale N) ^ 3 *
        (∑ t : Tet N, ∑ a : Fin 4, (eval (vertex t a) (q.val t)) ^ 2) ≤
          C * pressureEnergy q.val := by
  obtain ⟨C, hC, hb⟩ := scaled_vertex_bound (k - 1)
  refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN q
  calc
    _ = ∑ t : Tet N, ∑ a : Fin 4,
        (meshScale N) ^ 3 * (eval (vertex t a) (q.val t)) ^ 2 := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ t : Tet N, ∑ _a : Fin 4,
        C * ∫ x in tetrahedron t, (eval x (q.val t)) ^ 2 := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro a _
      exact hb t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN)
        (q.val t) (pressure_degree_bound q t) a
    _ = _ := by
      simp [pressureEnergy, Finset.mul_sum, mul_assoc]

end FreudenthalSVLean.PressureVertexBound
