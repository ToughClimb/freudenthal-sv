import FreudenthalSVLean.FourierEnergyDilation

/-!
# Uniform genuine L2 bound for the lower-half Fourier integral

For manuscript Lemma `means`, weighted Cauchy--Schwarz, genuine Fubini,
the three-dimensional dilation and Plancherel prove the lower-half
Fourier bound with one constant before every truncation epsilon>=0.
All product integrability obligations are checked, not inferred from
a formal exchange of integrals. This proves the Fourier-side estimate
in Durán, arXiv:1103.3718, Section 2. Identifying this Fourier expression
with the actual spatial Bogovskii derivative remains a separate theorem.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set Filter
open FreudenthalSVLean.FourierDirectionalDecay
open FreudenthalSVLean.FourierRayBound
open FreudenthalSVLean.SmallScaleFourierKernel
open FreudenthalSVLean.RescaledFourierEnergy
open FreudenthalSVLean.FourierEnergyDilation

noncomputable section

namespace FreudenthalSVLean.SmallScaleFourierL2

set_option backward.isDefEq.respectTransparency false

theorem energyDensity_prod_continuous (φ f : 𝓢(E, ℂ)) (m : E) :
    Continuous (fun p : ℝ × E => energyDensity φ f m p.2 p.1) := by
  unfold energyDensity weightedFourierRay frequency
  fun_prop

theorem energyDensity_prod_integrable (φ f : 𝓢(E, ℂ)) (m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun p : ℝ × E => energyDensity φ f m p.2 p.1)
      ((volume.restrict (Icc ε (1 / 2 : ℝ))).prod (volume : Measure E)) := by
  have hr := rescaledDensity_prod_integrable φ f m hε
  apply (integrable_prod_iff (energyDensity_prod_continuous φ f m).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hr.prod_left_ae, ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 / 2 : ℝ)))]
      with t ht hti
    exact (energyDensity_integrable_iff φ f m (by linarith [hti.2])).mpr ht
  · apply hr.integral_prod_right.congr
    filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 / 2 : ℝ)))]
      with t ht
    calc
      _ = ∫ ξ : E, energyDensity φ f m ξ t :=
        (energyDensity_integral_rescale φ f m (by linarith [ht.2])).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun ξ =>
        (Real.norm_of_nonneg (energyDensity_nonneg φ f m ξ t)).symm))

theorem energyDensity_double_integral_bound (φ f : 𝓢(E, ℂ)) (m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ ξ : E, ∫ t in Icc ε (1 / 2 : ℝ), energyDensity φ f m ξ t) ≤
      (4 * (Real.pi * decayConstant φ m)) * ∫ ξ : E, ‖𝓕 f ξ‖ ^ 2 := by
  calc
    _ = ∫ t in Icc ε (1 / 2 : ℝ), ∫ ξ : E, energyDensity φ f m ξ t :=
      (integral_integral_swap (energyDensity_prod_integrable φ f m hε)).symm
    _ = ∫ t in Icc ε (1 / 2 : ℝ), ∫ η : E, rescaledDensity φ f m η t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 / 2 : ℝ)))]
        with t ht
      exact energyDensity_integral_rescale φ f m (by linarith [ht.2])
    _ = ∫ η : E, ∫ t in Icc ε (1 / 2 : ℝ), rescaledDensity φ f m η t :=
      (integral_integral_swap (rescaledDensity_prod_integrable φ f m hε)).symm
    _ ≤ _ := rescaledDensity_double_integral_bound φ f m hε

theorem lowerHalf_measurable (ε : ℝ) (φ f : 𝓢(E, ℂ)) (m : E) :
    StronglyMeasurable (lowerHalf ε φ f m) := by
  have hc : Continuous (fun p : E × ℝ => FourierKernel φ f m p.1 p.2) := by
    unfold FourierKernel
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

theorem lowerHalf_square_integrable (φ f : 𝓢(E, ℂ)) (m : E)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun ξ : E => ‖lowerHalf ε φ f m ξ‖ ^ 2) (volume : Measure E) := by
  apply ((energyDensity_prod_integrable φ f m hε).integral_prod_right.const_mul
    (Real.pi * decayConstant φ m)).mono'
    (((lowerHalf_measurable ε φ f m).norm.pow 2).aestronglyMeasurable)
  filter_upwards with ξ
  change ‖(‖lowerHalf ε φ f m ξ‖ ^ 2 : ℝ)‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact lowerHalf_pointwise_bound ε φ f m ξ

theorem lowerHalf_memLp (φ f : 𝓢(E, ℂ)) (m : E) {ε : ℝ} (hε : 0 ≤ ε) :
    MemLp (lowerHalf ε φ f m) 2 (volume : Measure E) :=
  (memLp_two_iff_integrable_sq_norm (lowerHalf_measurable ε φ f m).aestronglyMeasurable).mpr
    (lowerHalf_square_integrable φ f m hε)

theorem lowerHalf_L2_bound (φ f : 𝓢(E, ℂ)) (m : E) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ ξ : E, ‖lowerHalf ε φ f m ξ‖ ^ 2) ≤
      4 * (Real.pi * decayConstant φ m) ^ 2 * ∫ x : E, ‖f x‖ ^ 2 := by
  have hC : 0 ≤ Real.pi * decayConstant φ m :=
    mul_nonneg Real.pi_pos.le (decayConstant_nonneg φ m)
  calc
    _ ≤ ∫ ξ : E, (Real.pi * decayConstant φ m) *
        ∫ t in Icc ε (1 / 2 : ℝ), energyDensity φ f m ξ t :=
      integral_mono (lowerHalf_square_integrable φ f m hε)
        ((energyDensity_prod_integrable φ f m hε).integral_prod_right.const_mul _)
        (lowerHalf_pointwise_bound ε φ f m)
    _ = (Real.pi * decayConstant φ m) *
        ∫ ξ : E, ∫ t in Icc ε (1 / 2 : ℝ), energyDensity φ f m ξ t := integral_const_mul _ _
    _ ≤ (Real.pi * decayConstant φ m) *
        ((4 * (Real.pi * decayConstant φ m)) * ∫ ξ : E, ‖𝓕 f ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (energyDensity_double_integral_bound φ f m hε) hC
    _ = _ := by rw [SchwartzMap.integral_norm_sq_fourier]; ring

end FreudenthalSVLean.SmallScaleFourierL2
