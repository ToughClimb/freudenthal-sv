import FreudenthalSVLean.BogovskiiMixtureFourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual Fourier exchange for compact parameter integrals

For the continuous lifting in manuscript Lemma `means`, a jointly
continuous spatial integrand with one compact spatial support on a
compact time set has a genuine continuous, compactly supported integral.
Its actual Fourier integral equals the integral of its actual Fourier
integrals by compact-product integrability and Fubini. The input and
output L1/L2 conditions are proved from true support and continuity.
-/

open scoped SchwartzMap Real
open MeasureTheory FourierTransform Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport

noncomputable section

namespace FreudenthalSVLean.CompactFourierIntegration

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def timeIntegral (K : Set ℝ) (F : ℝ → E → ℂ) (x : E) : ℂ := ∫ t in K, F t x

theorem timeIntegral_continuous {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → E → ℂ} (hF : Continuous F.uncurry) : Continuous (timeIntegral K F) := by
  change Continuous (fun x : E => ∫ t in K, F t x)
  have hc : Continuous (fun p : E × ℝ => F p.2 p.1) :=
    hF.comp (continuous_snd.prodMk continuous_fst)
  exact continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun x : E => fun t : ℝ => F t x) hc hK

theorem timeIntegral_zero {K : Set ℝ} (hK : IsCompact K)
    {S : Set E} {F : ℝ → E → ℂ} (hs : ∀ t ∈ K, ∀ x ∉ S, F t x = 0)
    {x : E} (hx : x ∉ S) : timeIntegral K F x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  exact hs t ht x hx

theorem timeIntegral_compact {K : Set ℝ} (hK : IsCompact K)
    {S : Set E} (hS : IsCompact S) {F : ℝ → E → ℂ}
    (hs : ∀ t ∈ K, ∀ x ∉ S, F t x = 0) : HasCompactSupport (timeIntegral K F) := by
  apply hS.of_isClosed_subset (isClosed_tsupport (timeIntegral K F))
  apply closure_minimal _ hS.isClosed
  intro x hx
  by_contra hn
  exact hx (timeIntegral_zero hK hs hn)

theorem timeIntegral_integrable {K : Set ℝ} (hK : IsCompact K)
    {S : Set E} (hS : IsCompact S) {F : ℝ → E → ℂ}
    (hF : Continuous F.uncurry) (hs : ∀ t ∈ K, ∀ x ∉ S, F t x = 0) :
    Integrable (timeIntegral K F) :=
  (timeIntegral_continuous hK hF).integrable_of_hasCompactSupport
    (timeIntegral_compact hK hS hs)

theorem timeIntegral_memLp_two {K : Set ℝ} (hK : IsCompact K)
    {S : Set E} (hS : IsCompact S) {F : ℝ → E → ℂ}
    (hF : Continuous F.uncurry) (hs : ∀ t ∈ K, ∀ x ∉ S, F t x = 0) :
    MemLp (timeIntegral K F) 2 volume :=
  (timeIntegral_continuous hK hF).memLp_of_hasCompactSupport
    (timeIntegral_compact hK hS hs)

theorem timeIntegral_fourier {K : Set ℝ} (hK : IsCompact K)
    {S : Set E} (hS : IsCompact S) {F : ℝ → E → ℂ}
    (hF : Continuous F.uncurry) (hs : ∀ t ∈ K, ∀ x ∉ S, F t x = 0) (ξ : E) :
    𝓕 (timeIntegral K F) ξ = ∫ t in K, 𝓕 (F t) ξ := by
  have hc : Continuous (fun p : E × ℝ => 𝐞 (-inner ℝ p.1 ξ) • F p.2 p.1) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hF.comp (continuous_snd.prodMk continuous_fst))
  have hi : Integrable (fun p : E × ℝ => 𝐞 (-inner ℝ p.1 ξ) • F p.2 p.1)
      (((volume : Measure E).restrict S).prod ((volume : Measure ℝ).restrict K)) := by
    rw [Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (hS.prod hK)
  rw [Real.fourier_eq]
  calc
    _ = ∫ x in S, 𝐞 (-inner ℝ x ξ) • timeIntegral K F x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [timeIntegral_zero hK hs hx, smul_zero])).symm
    _ = ∫ x in S, ∫ t in K, 𝐞 (-inner ℝ x ξ) • F t x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [timeIntegral, Circle.smul_def, integral_smul]
    _ = ∫ t in K, ∫ x in S, 𝐞 (-inner ℝ x ξ) • F t x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
      rw [Real.fourier_eq]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hs t ht x hx, smul_zero])

end FreudenthalSVLean.CompactFourierIntegration
