import FreudenthalSVLean.VelocityEnergy

/-!
# Integral estimates for pressure residuals and divergence

For the manuscript's successive lifting stages, pressure subtraction and
the actual polynomial divergence satisfy squared integral bounds on every
physical mesh.  The factor three in the divergence estimate is obtained
from the three diagonal gradient components before integration.  No
conformity, polynomial degree or guessed coefficient norm is required.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.DivergenceEnergy

theorem pressureEnergy_nonneg {N : ℕ} (q : BrokenPressure N) : 0 ≤ pressureEnergy q :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem pressureEnergy_sub {N : ℕ} (hN : 0 < N) (p q : BrokenPressure N) :
    pressureEnergy (p - q) ≤ 2 * (pressureEnergy p + pressureEnergy q) := by
  unfold pressureEnergy
  calc
    _ ≤ ∑ t : Tet N, ∫ x in tetrahedron t, 2 * ((eval x (p t)) ^ 2 + (eval x (q t)) ^ 2) := by
      apply Finset.sum_le_sum
      intro t _
      have hi (r : BrokenPressure N) : IntegrableOn (fun x => (eval x (r t)) ^ 2)
          (tetrahedron t) :=
        ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
          (μ := volume) (tetrahedron_isCompact hN t)
      apply integral_mono (hi (p - q)) ((hi p).add (hi q) |>.const_mul 2)
      intro x
      simp only [Pi.sub_apply, map_sub, Pi.add_apply]
      nlinarith [sq_nonneg (eval x (p t) + eval x (q t))]
    _ = _ := by
      have hi (t : Tet N) (r : BrokenPressure N) :
          IntegrableOn (fun x => (eval x (r t)) ^ 2) (tetrahedron t) :=
        ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
          (μ := volume) (tetrahedron_isCompact hN t)
      simp only [integral_const_mul, integral_add (hi _ p) (hi _ q)]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

theorem divergence_density_bound {N : ℕ} (v : BrokenVelocity N) (t : Tet N) (x : Space) :
    (eval x (divergence N v t)) ^ 2 ≤
      3 * ∑ j : Coordinate, ∑ i : Coordinate, (eval x (pderiv i (v t j))) ^ 2 := by
  change (eval x (∑ j : Coordinate, pderiv j (v t j))) ^ 2 ≤ _
  rw [map_sum]
  have hc : (∑ j : Coordinate, eval x (pderiv j (v t j))) ^ 2 ≤
      (Finset.univ : Finset Coordinate).card *
        ∑ j : Coordinate, (eval x (pderiv j (v t j))) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hd : (∑ j : Coordinate, (eval x (pderiv j (v t j))) ^ 2) ≤
      ∑ j : Coordinate, ∑ i : Coordinate, (eval x (pderiv i (v t j))) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    exact Finset.single_le_sum (f := fun i : Coordinate => (eval x (pderiv i (v t j))) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hc' : (∑ j : Coordinate, eval x (pderiv j (v t j))) ^ 2 ≤
      3 * ∑ j : Coordinate, (eval x (pderiv j (v t j))) ^ 2 := by simpa using hc
  exact hc'.trans (mul_le_mul_of_nonneg_left hd (by norm_num))

theorem divergence_energy_bound {N : ℕ} (hN : 0 < N) (v : BrokenVelocity N) :
    pressureEnergy (divergence N v) ≤ 3 * velocityEnergy v := by
  unfold pressureEnergy velocityEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hi : IntegrableOn (fun x => (eval x (divergence N v t)) ^ 2) (tetrahedron t) :=
    ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
      (μ := volume) (tetrahedron_isCompact hN t)
  have hg : IntegrableOn (fun x => ∑ j : Coordinate, ∑ i : Coordinate,
      (eval x (pderiv i (v t j))) ^ 2) (tetrahedron t) := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro i _
    exact ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
      (μ := volume) (tetrahedron_isCompact hN t)
  rw [← integral_const_mul]
  exact integral_mono hi (hg.const_mul 3) (divergence_density_bound v t)

end FreudenthalSVLean.DivergenceEnergy
