import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Genuine weighted Cauchy--Schwarz for the continuous lifting estimate

For manuscript Lemma `means`, the small-scale Bogovskii derivative
estimate uses a nonnegative Fourier weight. The actual integral square
inequality is proved here by the nonnegativity of weighted variance.
All integrability hypotheses refer to genuine Lebesgue integrals; no
quadrature or stipulated positive functional is used.
-/

open MeasureTheory Filter

noncomputable section

namespace FreudenthalSVLean.WeightedIntegralSquare

set_option backward.isDefEq.respectTransparency false

theorem weighted_integral_square {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w g : α → ℝ} (hw : Integrable w μ)
    (h1 : Integrable (fun x => w x * g x) μ)
    (h2 : Integrable (fun x => w x * (g x) ^ 2) μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ w x) :
    (∫ x, w x * g x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * ∫ x, w x * (g x) ^ 2 ∂μ := by
  let M := ∫ x, w x ∂μ
  let b := ∫ x, w x * g x ∂μ
  let c := ∫ x, w x * (g x) ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg_of_ae hn
  rcases eq_or_lt_of_le hM with hz | hp
  · have hae : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hn hw).mp (Eq.symm hz)
    have hb : b = 0 := integral_eq_zero_of_ae (by
      filter_upwards [hae] with x hx
      simp [hx])
    change b ^ 2 ≤ M * c
    rw [hb, ← hz]
    norm_num
  ·
    have hv : 0 ≤ ∫ x, w x * (M * g x - b) ^ 2 ∂μ :=
      integral_nonneg_of_ae (hn.mono (fun x hx => mul_nonneg hx (sq_nonneg _)))
    have he : (∫ x, w x * (M * g x - b) ^ 2 ∂μ) = M * (M * c - b ^ 2) := by
      calc
        _ = ∫ x, M ^ 2 * (w x * (g x) ^ 2) -
            (2 * M * b) * (w x * g x) + b ^ 2 * w x ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by ring)
        _ = _ := by
          rw [integral_add
            (f := fun x => M ^ 2 * (w x * (g x) ^ 2) - (2 * M * b) * (w x * g x))
            (g := fun x => b ^ 2 * w x)
            ((h2.const_mul _).sub (h1.const_mul _)) (hw.const_mul _),
            integral_sub (f := fun x => M ^ 2 * (w x * (g x) ^ 2))
              (g := fun x => (2 * M * b) * (w x * g x)) (h2.const_mul _) (h1.const_mul _)]
          simp only [integral_const_mul]
          change M ^ 2 * c - (2 * M * b) * b + b ^ 2 * M = M * (M * c - b ^ 2)
          ring
    rw [he] at hv
    change b ^ 2 ≤ M * c
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hv)

end FreudenthalSVLean.WeightedIntegralSquare
