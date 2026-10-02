import FreudenthalSVLean.FourierRayBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The genuine small-scale change of variables

For the continuous Bogovskii estimate underlying manuscript Lemma `means`,
the substitution s=t/(1-t) changes the three-dimensional Fourier weight
(1-t)^(-4) into (1+s)^2. On the lower half interval the latter is at most
four. The resulting bound uses the actual ray integral, independently of
any positive truncation parameter. This proves the change of variables in
Durán, arXiv:1103.3718, Section 2; it does not assume an L2 operator bound.
-/

open scoped SchwartzMap
open MeasureTheory Set
open FreudenthalSVLean.FourierDirectionalDecay
open FreudenthalSVLean.FourierRayBound

noncomputable section

namespace FreudenthalSVLean.BogovskiiRayRescaling

set_option backward.isDefEq.respectTransparency false

def compression (t : ℝ) : ℝ := t / (1 - t)

theorem compression_hasDerivAt {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt compression ((1 - t) ^ 2)⁻¹ t := by
  have hn : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hd := (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) hn
  convert! hd using 1
  dsimp [compression]
  ring

theorem compression_continuousOn : ContinuousOn compression (Icc 0 (1 / 2 : ℝ)) :=
  continuousOn_id.div (continuousOn_const.sub continuousOn_id)
    (fun t ht => by linarith [ht.2])

theorem compression_deriv_continuousOn :
    ContinuousOn (fun t : ℝ => ((1 - t) ^ 2)⁻¹) (Icc 0 (1 / 2 : ℝ)) :=
  ((continuousOn_const.sub continuousOn_id).pow 2).inv₀
    (fun t ht => pow_ne_zero 2 (by change 1 - t ≠ 0; linarith [ht.2]))

theorem small_half_change (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t in Icc 0 (1 / 2 : ℝ), ((1 - t) ^ 4)⁻¹ * w (compression t)) =
      ∫ s in Icc 0 1, (1 + s) ^ 2 * w s := by
  have hg : Continuous (fun s : ℝ => (1 + s) ^ 2 * w s) :=
    ((continuous_const.add continuous_id).pow 2).mul hw
  have hs := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (f := compression)
    (f' := fun t => ((1 - t) ^ 2)⁻¹)
    (fun t ht => compression_hasDerivAt (by rw [uIcc_of_le (by norm_num)] at ht; linarith [ht.2]))
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
      compression_deriv_continuousOn) hg
  have he : compression 0 = 0 ∧ compression (1 / 2) = 1 := by norm_num [compression]
  rw [he.1, he.2] at hs
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  calc
    _ = ∫ t in (0 : ℝ)..(1 / 2 : ℝ),
        ((1 - t) ^ 2)⁻¹ • ((1 + compression t) ^ 2 * w (compression t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have hn : 1 - t ≠ 0 := by linarith [ht.2]
      simp only [smul_eq_mul, compression]
      field_simp
      ring
    _ = _ := hs

theorem small_half_integrable (w : ℝ → ℝ) (hw : Continuous w) :
    IntegrableOn (fun t : ℝ => ((1 - t) ^ 4)⁻¹ * w (compression t))
      (Icc 0 (1 / 2 : ℝ)) := by
  have hc : ContinuousOn (fun t : ℝ => ((1 - t) ^ 4)⁻¹ * w (compression t))
      (Icc 0 (1 / 2 : ℝ)) :=
    (((continuousOn_const.sub continuousOn_id).pow 4).inv₀
      (fun t ht => pow_ne_zero 4 (by change 1 - t ≠ 0; linarith [ht.2]))).mul
        (hw.continuousOn.comp compression_continuousOn (mapsTo_univ _ _))
  exact hc.integrableOn_compact isCompact_Icc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem small_half_ray_bound (φ : 𝓢(E, ℂ)) (η m : E) :
    (∫ t in Icc 0 (1 / 2 : ℝ), ((1 - t) ^ 4)⁻¹ *
      weightedFourierRay φ η m (compression t)) ≤ 4 * (Real.pi * decayConstant φ m) := by
  rw [small_half_change _ (weightedFourierRay_continuous φ η m)]
  calc
    _ ≤ ∫ s in Icc (0 : ℝ) 1, 4 * weightedFourierRay φ η m s := by
      apply setIntegral_mono_on
        ((((continuous_const.add continuous_id).pow 2).mul
          (weightedFourierRay_continuous φ η m)).integrableOn_Icc)
        (((weightedFourierRay_continuous φ η m).const_mul 4).integrableOn_Icc)
        measurableSet_Icc
      intro s hs
      exact mul_le_mul_of_nonneg_right (by change (1 + s) ^ 2 ≤ 4; nlinarith [hs.1, hs.2])
        (weightedFourierRay_nonneg φ η m s)
    _ = 4 * ∫ s in Icc (0 : ℝ) 1, weightedFourierRay φ η m s := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weightedFourierRay_setIntegral_bound φ η m (Icc 0 1)) (by norm_num)

theorem truncated_small_half_ray_bound (φ : 𝓢(E, ℂ)) (η m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ t in Icc ε (1 / 2 : ℝ), ((1 - t) ^ 4)⁻¹ *
      weightedFourierRay φ η m (compression t)) ≤ 4 * (Real.pi * decayConstant φ m) := by
  apply le_trans _ (small_half_ray_bound φ η m)
  exact setIntegral_mono_set (small_half_integrable _ (weightedFourierRay_continuous φ η m))
    (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity)
      (weightedFourierRay_nonneg φ η m (compression t))))
    (Filter.Eventually.of_forall (fun t ht => ⟨hε.trans ht.1, ht.2⟩))

end FreudenthalSVLean.BogovskiiRayRescaling
