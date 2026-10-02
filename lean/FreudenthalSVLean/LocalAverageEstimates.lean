import FreudenthalSVLean.VolumeNodalInterpolation

/-!
# True local coefficient bounds for volume-averaging interpolation

For the local interpolation argument in manuscript Lemma `means` and
equation `SZ`, genuine volume means satisfy L2 Cauchy--Schwarz and
constant-shift identities.  An averaging box contained in a larger
box therefore has its mean difference controlled by the larger box's
actual weak derivative energy.  At a boundary-centered larger box, the
uncentered mean has the same scale-correct control from zero extension.
All set containment is explicit, and no quadrature or point-evaluation
estimate on arbitrary H1 functions is used.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.IntervalH1Estimate
open FreudenthalSVLean.TranslatedBoxH1Estimate
open FreudenthalSVLean.BoundaryBoxH1Estimate
open FreudenthalSVLean.BoundaryHalfBoxGeometry
open FreudenthalSVLean.ConformingH1Zero

noncomputable section

namespace FreudenthalSVLean.LocalAverageEstimates

set_option backward.isDefEq.respectTransparency false

theorem finite_mean_square_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ univ ≠ ⊤) (hpos : 0 < μ.real univ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    μ.real univ * ((μ.real univ)⁻¹ * ∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have ht := mul_le_mul_of_nonneg_left (integral_square_bound hμ hf)
    (inv_nonneg.mpr hpos.le)
  have he : (μ.real univ)⁻¹ * (∫ x, f x ∂μ) ^ 2 =
      μ.real univ * ((μ.real univ)⁻¹ * ∫ x, f x ∂μ) ^ 2 := by
    field_simp [hpos.ne']
  rw [he] at ht
  simpa only [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] using ht

theorem translatedBox_volume_pos {a b : ℝ} (hab : a < b) (o : Space) :
    0 < volume.real (translatedBox a b o) := by
  rw [translatedBox_volume hab.le]
  exact pow_pos (sub_pos.mpr hab) 3

theorem translatedBoxMean_sub_const {f : Space → ℝ} (hf : MemLp f 2 volume)
    {a b : ℝ} (hab : a < b) (o : Space) (c : ℝ) :
    translatedBoxMean a b o (fun x => f x - c) = translatedBoxMean a b o f - c := by
  let : IsFiniteMeasure (volume.restrict (translatedBox a b o)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top
  have hi := (hf.restrict (translatedBox a b o)).integrable (by norm_num)
  have hc : IntegrableOn (fun _ : Space => c) (translatedBox a b o) := integrable_const c
  rw [translatedBoxMean_eq_volume_average hab.le,
    translatedBoxMean_eq_volume_average hab.le, integral_sub hi hc, setIntegral_const]
  simp only [smul_eq_mul, mul_sub, ← mul_assoc,
    inv_mul_cancel₀ (translatedBox_volume_pos hab o).ne', one_mul]

theorem translatedBoxMean_square_bound {f : Space → ℝ} (hf : MemLp f 2 volume)
    {a b : ℝ} (hab : a < b) (o : Space) :
    (b - a) ^ 3 * (translatedBoxMean a b o f) ^ 2 ≤
      ∫ x in translatedBox a b o, (f x) ^ 2 := by
  have hμ : (volume.restrict (translatedBox a b o)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top
  have hpos : 0 < (volume.restrict (translatedBox a b o)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact translatedBox_volume_pos hab o
  have ht := finite_mean_square_bound hμ hpos (hf.restrict (translatedBox a b o))
  rw [measureReal_restrict_apply_univ, ← translatedBoxMean_eq_volume_average hab.le,
    translatedBox_volume hab.le] at ht
  exact ht

theorem translatedBoxMean_center_square_bound {f : Space → ℝ} (hf : MemLp f 2 volume)
    {a b : ℝ} (hab : a < b) (o : Space) (c : ℝ) :
    (b - a) ^ 3 * (translatedBoxMean a b o f - c) ^ 2 ≤
      ∫ x in translatedBox a b o, (f x - c) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (translatedBox a b o)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top
  have hμ : (volume.restrict (translatedBox a b o)) univ ≠ ⊤ := measure_ne_top _ _
  have hpos : 0 < (volume.restrict (translatedBox a b o)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact translatedBox_volume_pos hab o
  have ht := finite_mean_square_bound hμ hpos
    ((hf.restrict (translatedBox a b o)).sub (memLp_const c))
  have hs : volume.real (translatedBox a b o) *
      ((volume.real (translatedBox a b o))⁻¹ *
        ∫ x in translatedBox a b o, f x - c) ^ 2 ≤
          ∫ x in translatedBox a b o, (f x - c) ^ 2 := by
    simpa only [measureReal_restrict_apply_univ, Pi.sub_apply] using! ht
  rw [← translatedBoxMean_eq_volume_average hab.le,
    translatedBoxMean_sub_const hf hab o c, translatedBox_volume hab.le] at hs
  exact hs

theorem nested_box_mean_bound {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (o p : Space) (hsub : translatedBox a b o ⊆ translatedBox c d p) :
    (b - a) ^ 3 * (translatedBoxMean a b o f - translatedBoxMean c d p f) ^ 2 ≤
      3 * (d - c) ^ 2 * ∑ j : Fin 3, ∫ x in translatedBox c d p, (g j x) ^ 2 := by
  obtain ⟨u, hu⟩ := hf
  let : IsFiniteMeasure (volume.restrict (translatedBox c d p)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc : IsCompact (translatedBox c d p)).measure_ne_top
  have hi : IntegrableOn (fun x => (f x - translatedBoxMean c d p f) ^ 2)
      (translatedBox c d p) := by
    simpa only [Pi.sub_apply] using!
      ((hu.weak_gradient.1.restrict (translatedBox c d p)).sub
        (memLp_const (translatedBoxMean c d p f))).integrable_sq
  exact (translatedBoxMean_center_square_bound hu.weak_gradient.1 hab o _).trans
    ((setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall hsub)).trans (weak_translated_box_mean_poincare ⟨u, hu⟩ hcd p))

theorem nested_boundary_box_mean_bound {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) {a b h : ℝ} (hab : a < b) (hh : 0 < h)
    (o p : Space) (hp : ∃ j : Fin 3, p j = 0 ∨ p j = 1)
    (hsub : translatedBox a b o ⊆ translatedBox (-h) h p) :
    (b - a) ^ 3 * (translatedBoxMean a b o f) ^ 2 ≤
      72 * h ^ 2 * ∑ j : Fin 3, ∫ x in translatedBox (-h) h p, (g j x) ^ 2 :=
  (translatedBoxMean_square_bound hf.1.1 hab o).trans
    ((setIntegral_mono_set (hf.1.1.restrict _).integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hsub)).trans
        (boundary_centered_box_poincare hf hh p hp))

end FreudenthalSVLean.LocalAverageEstimates
