import FreudenthalSVLean.MainTheorem

/-!
# Actual uniform reduced inf-sup witnesses for k=4,5

This proves the inf-sup consequence in manuscript Theorem `thm:main`.
The pairing is the genuine sum of physical element Lebesgue integrals;
the denominator is the actual gradient seminorm times the pressure L2
norm. Every nonzero pressure has a nonzero velocity with strictly
positive denominator and ratio bounded below by a single positive beta
before every N>=1. This quantified witness formulation implies the usual
infimum--supremum inequality and avoids conventions for empty spaces.
It follows from the proved uniform linear right inverse and true positive
definiteness of the pressure energy, not an assumed norm equivalence.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.DivergenceEnergy
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.MainTheorem

noncomputable section

namespace FreudenthalSVLean.DiscreteInfSup

set_option backward.isDefEq.respectTransparency false

def pressurePairing {N : ℕ} (p q : BrokenPressure N) : ℝ :=
  ∑ t : Tet N, ∫ x in tetrahedron t, eval x (p t) * eval x (q t)

theorem pressurePairing_self {N : ℕ} (q : BrokenPressure N) :
    pressurePairing q q = pressureEnergy q := by simp only [pressurePairing, pressureEnergy, sq]

def HasUniformInfSup (k : ℕ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ N : ℕ, 0 < N → ∀ q : pressureSpace N k, q ≠ 0 →
    ∃ v : velocitySpace N k, v ≠ 0 ∧ 0 < velocityEnergy v.val ∧
      β ≤ pressurePairing (divergence N v.val) q.val /
        (Real.sqrt (velocityEnergy v.val) * Real.sqrt (pressureEnergy q.val))

theorem uniform_inf_sup_of_right_inverse {k : ℕ} (h : HasUniformRightInverse k) :
    HasUniformInfSup k := by
  obtain ⟨C, hC, hR⟩ := h
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro N hN q hq
  obtain ⟨R, hr, he⟩ := hR N hN
  have hp : 0 < pressureEnergy q.val := by
    apply lt_of_le_of_ne (pressureEnergy_nonneg q.val)
    intro hz
    exact hq (Subtype.ext ((pressureEnergy_eq_zero_iff hN q.val).mp hz.symm))
  have hv : 0 < velocityEnergy (R q).val := by
    have hb := divergence_energy_bound hN (R q).val
    rw [hr q] at hb
    linarith
  have hv0 : R q ≠ 0 := by
    intro hz
    have hzero : velocityEnergy (R q).val = 0 := by rw [hz]; simp [velocityEnergy]
    linarith
  refine ⟨R q, hv0, hv, ?_⟩
  rw [hr q, pressurePairing_self]
  have hsn : Real.sqrt (velocityEnergy (R q).val) ≤ C * Real.sqrt (pressureEnergy q.val) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt hv.le, mul_pow, Real.sq_sqrt hp.le]
    exact he q
  have hd : 0 < Real.sqrt (velocityEnergy (R q).val) * Real.sqrt (pressureEnergy q.val) :=
    mul_pos (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr hp)
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ C⁻¹ * (C * Real.sqrt (pressureEnergy q.val) * Real.sqrt (pressureEnergy q.val)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsn (Real.sqrt_nonneg _)) (inv_nonneg.mpr hC.le)
    _ = pressureEnergy q.val := by
      rw [mul_assoc C, ← sq, Real.sq_sqrt hp.le, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

theorem quartic_uniform_inf_sup : HasUniformInfSup 4 :=
  uniform_inf_sup_of_right_inverse quartic_uniform_right_inverse

theorem quintic_uniform_inf_sup : HasUniformInfSup 5 :=
  uniform_inf_sup_of_right_inverse quintic_uniform_right_inverse

end FreudenthalSVLean.DiscreteInfSup
