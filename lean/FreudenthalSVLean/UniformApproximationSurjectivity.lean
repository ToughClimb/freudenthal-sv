import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Genuine surjectivity from uniformly bounded approximate preimages

For the continuous lift in manuscript Lemma `means`, uniformly bounded
approximate preimages must be converted to actual preimages; mere dense
range does not suffice. This is the geometric-series argument used in
Mathlib's Banach open-mapping proof, with the uniform half-error hypothesis
supplied directly rather than inferred from an assumed surjectivity.
Completeness, norm summability, continuity and telescoping are all checked.
-/

open scoped BigOperators Topology
open Filter Function

noncomputable section

namespace FreudenthalSVLean.UniformApproximationSurjectivity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem surjective_of_uniform_half_approximation (f : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (happrox : ∀ y : F, ∃ x : E, ‖f x - y‖ ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Function.Surjective f := by
  choose g hg using happrox
  let h : F → F := fun y => y - f (g y)
  have hle (y : F) : ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    simpa only [h, norm_sub_rev] using (hg y).1
  intro y
  have hnle (n : ℕ) : ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    induction n with
    | zero => simp only [iterate_zero_apply, pow_zero, one_mul, le_rfl]
    | succ n ih =>
      rw [iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (by norm_num)
  let u : ℕ → E := fun n => g (h^[n] y)
  have ule (n : ℕ) : ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by
    calc
      _ ≤ C * ‖h^[n] y‖ := (hg _).2
      _ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) hC
      _ = _ := by ring
  have sn : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ule
      (summable_geometric_two.mul_right (C * ‖y‖))
  have su : Summable u := sn.of_norm
  let x := ∑' n, u n
  have hsum (n : ℕ) : f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, map_zero, iterate_zero_apply, sub_self]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, iterate_succ_apply']
      change y - h^[n] y + f (g (h^[n] y)) = y - (h^[n] y - f (g (h^[n] y)))
      abel
  have hx : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) :=
    su.hasSum.tendsto_sum_nat
  have hfx : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto x).comp hx
  simp only [hsum] at hfx
  have hz : Tendsto (fun n : ℕ => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hnle
    simpa only [zero_mul] using
      (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul
          (tendsto_const_nhds (x := ‖y‖))
  have he := tendsto_nhds_unique hfx (tendsto_const_nhds.sub hz)
  exact ⟨x, by simpa only [sub_zero] using he⟩

end FreudenthalSVLean.UniformApproximationSurjectivity
