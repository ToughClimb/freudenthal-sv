import FreudenthalSVLean.FreudenthalMesh
import Mathlib.Algebra.Order.Chebyshev

/-!
# Genuine finite-sum gradient-energy estimates

For the manuscript's local lifting estimates and bounded-overlap assembly,
this module proves nonnegativity, scalar scaling, and finite-sum bounds
for the actual Lebesgue integral of all nine spatial polynomial gradient
components.  Cauchy--Schwarz is applied pointwise before integration.
No discrete coefficient norm is substituted for the physical energy.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.VelocityEnergy

abbrev LocalVelocity := Coordinate → MvPolynomial Coordinate ℝ

def gradientDensity (v : LocalVelocity) (x : Space) : ℝ :=
  ∑ e : Coordinate × Coordinate, (eval x (pderiv e.2 (v e.1))) ^ 2

theorem gradientDensity_nonneg (v : LocalVelocity) (x : Space) : 0 ≤ gradientDensity v x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gradientDensity_continuous (v : LocalVelocity) : Continuous (gradientDensity v) := by
  unfold gradientDensity
  exact continuous_finsetSum _ (fun e _ => (continuous_eval (pderiv e.2 (v e.1))).pow 2)

theorem gradientDensity_smul (c : ℝ) (v : LocalVelocity) (x : Space) :
    gradientDensity (c • v) x = c ^ 2 * gradientDensity v x := by
  simp only [gradientDensity, Pi.smul_apply, smul_eq_C_mul, pderiv_C_mul,
    map_mul, eval_C, mul_pow, Finset.mul_sum]

theorem gradientDensity_sum {I : Type*} (s : Finset I) (v : I → LocalVelocity) (x : Space) :
    gradientDensity (∑ a ∈ s, v a) x ≤ (s.card : ℝ) * ∑ a ∈ s, gradientDensity (v a) x := by
  simp only [gradientDensity, Finset.sum_apply, map_sum]
  calc
    (∑ e : Coordinate × Coordinate, (∑ a ∈ s, eval x (pderiv e.2 (v a e.1))) ^ 2) ≤
        ∑ e : Coordinate × Coordinate, (s.card : ℝ) *
          ∑ a ∈ s, (eval x (pderiv e.2 (v a e.1))) ^ 2 := by
      apply Finset.sum_le_sum
      intro e _
      exact sq_sum_le_card_mul_sum_sq
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]

def localEnergy {N : ℕ} (t : Tet N) (v : LocalVelocity) : ℝ :=
  ∫ x in tetrahedron t, gradientDensity v x

theorem localEnergy_nonneg {N : ℕ} (t : Tet N) (v : LocalVelocity) : 0 ≤ localEnergy t v :=
  integral_nonneg (gradientDensity_nonneg v)

theorem localEnergy_zero {N : ℕ} (t : Tet N) : localEnergy t 0 = 0 := by
  simp [localEnergy, gradientDensity]

theorem localEnergy_smul {N : ℕ} (t : Tet N) (c : ℝ) (v : LocalVelocity) :
    localEnergy t (c • v) = c ^ 2 * localEnergy t v := by
  simp only [localEnergy, gradientDensity_smul, integral_const_mul]

theorem localEnergy_sum {I : Type*} {N : ℕ} (hN : 0 < N) (t : Tet N)
    (s : Finset I) (v : I → LocalVelocity) :
    localEnergy t (∑ a ∈ s, v a) ≤ (s.card : ℝ) * ∑ a ∈ s, localEnergy t (v a) := by
  have hv (a : I) : IntegrableOn (gradientDensity (v a)) (tetrahedron t) :=
    (gradientDensity_continuous (v a)).continuousOn.integrableOn_compact
      (μ := volume) (tetrahedron_isCompact hN t)
  have hs : IntegrableOn (gradientDensity (∑ a ∈ s, v a)) (tetrahedron t) :=
    (gradientDensity_continuous _).continuousOn.integrableOn_compact
      (μ := volume) (tetrahedron_isCompact hN t)
  have ht : IntegrableOn (fun x => (s.card : ℝ) * ∑ a ∈ s, gradientDensity (v a) x)
      (tetrahedron t) := (integrable_finsetSum s (fun a _ => hv a)).const_mul _
  have hi := integral_mono hs ht (gradientDensity_sum s v)
  simpa only [localEnergy, integral_const_mul, integral_finsetSum s (fun a _ => hv a)] using hi

theorem localEnergy_eq_sum {N : ℕ} (hN : 0 < N) (t : Tet N) (v : LocalVelocity) :
    localEnergy t v = ∑ j : Coordinate, ∑ i : Coordinate,
      ∫ x in tetrahedron t, (eval x (pderiv i (v j))) ^ 2 := by
  have hv (e : Coordinate × Coordinate) :
      IntegrableOn (fun x => (eval x (pderiv e.2 (v e.1))) ^ 2) (tetrahedron t) :=
    ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
      (μ := volume) (tetrahedron_isCompact hN t)
  unfold localEnergy gradientDensity
  rw [integral_finsetSum _ (fun e _ => hv e)]
  exact Fintype.sum_prod_type _

theorem velocityEnergy_eq_sum {N : ℕ} (v : BrokenVelocity N) :
    velocityEnergy v = ∑ t : Tet N, localEnergy t (v t) := by
  unfold velocityEnergy localEnergy gradientDensity
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  funext x
  exact (Fintype.sum_prod_type
    (fun e : Coordinate × Coordinate => (eval x (pderiv e.2 (v t e.1))) ^ 2)).symm

theorem velocityEnergy_nonneg {N : ℕ} (v : BrokenVelocity N) : 0 ≤ velocityEnergy v := by
  rw [velocityEnergy_eq_sum]
  exact Finset.sum_nonneg (fun t _ => localEnergy_nonneg t (v t))

theorem velocityEnergy_smul {N : ℕ} (c : ℝ) (v : BrokenVelocity N) :
    velocityEnergy (c • v) = c ^ 2 * velocityEnergy v := by
  simp only [velocityEnergy_eq_sum, Pi.smul_apply, localEnergy_smul, Finset.mul_sum]

theorem velocityEnergy_sum {I : Type*} {N : ℕ} (hN : 0 < N)
    (s : Finset I) (v : I → BrokenVelocity N) :
    velocityEnergy (∑ a ∈ s, v a) ≤ (s.card : ℝ) * ∑ a ∈ s, velocityEnergy (v a) := by
  simp only [velocityEnergy_eq_sum, Finset.sum_apply]
  calc
    (∑ t : Tet N, localEnergy t (∑ a ∈ s, v a t)) ≤
        ∑ t : Tet N, (s.card : ℝ) * ∑ a ∈ s, localEnergy t (v a t) :=
      Finset.sum_le_sum (fun t _ => localEnergy_sum hN t s (fun a => v a t))
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end FreudenthalSVLean.VelocityEnergy
