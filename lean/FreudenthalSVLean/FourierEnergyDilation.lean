import FreudenthalSVLean.RescaledFourierEnergy

/-!
# Exact physical Fourier-energy dilation

For the continuous Bogovskii estimate in manuscript Lemma `means`, the
actual substitution eta=(1-t)xi is proved with its three-dimensional
Lebesgue Jacobian and the true directional frequency identity. The
unrescaled and rescaled frequency energies have equal genuine integrals.
No Fourier representation of the spatial lifting is assumed here.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set
open FreudenthalSVLean.FourierDirectionalDecay
open FreudenthalSVLean.FourierRayBound
open FreudenthalSVLean.BogovskiiRayRescaling
open FreudenthalSVLean.SmallScaleFourierKernel
open FreudenthalSVLean.RescaledFourierEnergy

noncomputable section

namespace FreudenthalSVLean.FourierEnergyDilation

set_option backward.isDefEq.respectTransparency false

theorem energyDensity_rescale (φ f : 𝓢(E, ℂ)) (m ξ : E)
    {t : ℝ} (ht : t < 1) :
    energyDensity φ f m ξ t =
      (1 - t) ^ 3 * rescaledDensity φ f m ((1 - t) • ξ) t := by
  have hr : 0 < 1 - t := sub_pos.mpr ht
  have he : compression t • ((1 - t) • ξ) = t • ξ := by
    rw [smul_smul]
    congr 1
    exact div_mul_cancel₀ t hr.ne'
  unfold energyDensity rescaledDensity weightedFourierRay
  rw [frequency_smul, abs_of_pos hr, he]
  field_simp

theorem energyDensity_integrable_iff (φ f : 𝓢(E, ℂ)) (m : E)
    {t : ℝ} (ht : t < 1) :
    Integrable (fun ξ : E => energyDensity φ f m ξ t) (volume : Measure E) ↔
      Integrable (fun η : E => rescaledDensity φ f m η t) (volume : Measure E) := by
  have hr : 0 < 1 - t := sub_pos.mpr ht
  simp_rw [energyDensity_rescale φ f m _ ht]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 3 hr.ne'))]
  exact integrable_comp_smul_iff (volume : Measure E)
    (fun η => rescaledDensity φ f m η t) hr.ne'

theorem energyDensity_integral_rescale (φ f : 𝓢(E, ℂ)) (m : E)
    {t : ℝ} (ht : t < 1) :
    (∫ ξ : E, energyDensity φ f m ξ t) = ∫ η : E, rescaledDensity φ f m η t := by
  have hr : 0 < 1 - t := sub_pos.mpr ht
  simp_rw [energyDensity_rescale φ f m _ ht]
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure E)
    (fun η => rescaledDensity φ f m η t) (1 - t)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr 3)), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hr.ne')]
  exact one_mul _

end FreudenthalSVLean.FourierEnergyDilation
