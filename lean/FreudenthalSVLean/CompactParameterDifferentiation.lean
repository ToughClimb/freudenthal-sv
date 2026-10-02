import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual C1 differentiation over compact parameter sets

For the truncated continuous lifting in manuscript Lemma `means`, a
genuine compact parameter integral is differentiated by Mathlib's
proved dominated derivative theorem. Joint continuity of the supplied
actual derivative gives the required local uniform bound on a product
of compact sets. The resulting true Frechet derivative is continuous.
No differentiability of a parameter cutoff is required.
-/

open scoped ContDiff
open MeasureTheory Set Filter Metric

noncomputable section

namespace FreudenthalSVLean.CompactParameterDifferentiation

set_option backward.isDefEq.respectTransparency false

variable {X A Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [SecondCountableTopology A] {μ : Measure A} [IsFiniteMeasureOnCompacts μ]

theorem compact_integral_hasFDerivAt (K : Set A) (hK : IsCompact K)
    (F : X → A → Y) (D : X → A → X →L[ℝ] Y)
    (hF : Continuous F.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ a ∈ K, ∀ x : X, HasFDerivAt (F · a) (D x a) x) (x₀ : X) :
    HasFDerivAt (fun x : X => ∫ a in K, F x a ∂μ) (∫ a in K, D x₀ a ∂μ) x₀ := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ 1).prod hK).exists_bound_of_continuousOn
    hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ zero_lt_one)
    (F' := D) (bound := fun _ => M)
  · exact Eventually.of_forall (fun x =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro x hx
    exact hM (x, a) ⟨ball_subset_closedBall hx, ha⟩
  · exact integrableOn_const hK.measure_ne_top
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro x _
    exact hd a ha x

theorem compact_integral_contDiff_one [LocallyCompactSpace A] (K : Set A) (hK : IsCompact K)
    (F : X → A → Y) (D : X → A → X →L[ℝ] Y)
    (hF : Continuous F.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ a ∈ K, ∀ x : X, HasFDerivAt (F · a) (D x a) x) :
    ContDiff ℝ 1 (fun x : X => ∫ a in K, F x a ∂μ) := by
  apply contDiff_one_iff_fderiv.mpr
  constructor
  · intro x
    exact (compact_integral_hasFDerivAt K hK F D hF hD hd x).differentiableAt
  · have he : fderiv ℝ (fun x : X => ∫ a in K, F x a ∂μ) =
        (fun x : X => ∫ a in K, D x a ∂μ) := by
      funext x
      exact (compact_integral_hasFDerivAt K hK F D hF hD hd x).fderiv
    rw [he]
    exact continuous_parametric_integral_of_continuous hD hK

end FreudenthalSVLean.CompactParameterDifferentiation
