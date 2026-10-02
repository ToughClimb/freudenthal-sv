import FreudenthalSVLean.WeakBoxH1Estimate

/-!
# Uniform local mean estimates on translated physical boxes

For manuscript Lemma `means` and equation `SZ`, every Cartesian box of
side length `b-a` with arbitrary physical origin has a true volume mean
and the same local H1 estimate.  Translation preserves actual Lebesgue
measure and the actual Frechet derivatives.  The result is proved for
smooth functions and transported to weak H1 data through the established
genuine L2 approximation criterion.  Choosing side length proportional
to the mesh spacing supplies an h-squared local estimate; no interpolant
or continuous divergence inverse is postulated here.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.BoxH1Estimate
open FreudenthalSVLean.WeakBoxH1Estimate

noncomputable section

namespace FreudenthalSVLean.TranslatedBoxH1Estimate

set_option backward.isDefEq.respectTransparency false

def translatedBox (a b : ℝ) (o : Space) : Set Space :=
  Icc (fun j => a + o j) (fun j => b + o j)

theorem translatedBox_preimage (a b : ℝ) (o : Space) :
    translatedBox a b o = (MeasurableEquiv.subRight o) ⁻¹' boxSet a b := by
  ext x
  change ((∀ j, a + o j ≤ x j) ∧ ∀ j, x j ≤ b + o j) ↔
    ((∀ j, a ≤ x j - o j) ∧ ∀ j, x j - o j ≤ b)
  simp only [le_sub_iff_add_le, sub_le_iff_le_add]

theorem translatedBox_integral (a b : ℝ) (o : Space) (f : Space → ℝ) :
    (∫ x in translatedBox a b o, f x) = ∫ y in boxSet a b, f (y + o) := by
  have he := (measurePreserving_sub_right volume o).setIntegral_preimage_emb
    (MeasurableEquiv.subRight o).measurableEmbedding (fun y => f (y + o)) (boxSet a b)
  change (∫ x in (MeasurableEquiv.subRight o) ⁻¹' boxSet a b, f ((x - o) + o)) = _ at he
  simpa only [sub_add_cancel, ← translatedBox_preimage] using he

theorem translatedBox_volume {a b : ℝ} (hab : a ≤ b) (o : Space) :
    volume.real (translatedBox a b o) = (b - a) ^ 3 := by
  change (volume (Icc (fun j => a + o j) (fun j => b + o j))).toReal = _
  have hl : (fun j : Fin 3 => a + o j) ≤ fun j => b + o j := by
    intro j
    linarith
  rw [Real.volume_Icc_pi_toReal hl]
  have hs (j : Fin 3) : (b + o j) - (a + o j) = b - a := by ring
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The actual physical volume mean, with the proved volume normalization. -/
def translatedBoxMean (a b : ℝ) (o : Space) (f : Space → ℝ) : ℝ :=
  ((b - a)⁻¹) ^ 3 * ∫ x in translatedBox a b o, f x

theorem translatedBoxMean_eq_volume_average {a b : ℝ} (hab : a ≤ b)
    (o : Space) (f : Space → ℝ) :
    translatedBoxMean a b o f =
      (volume.real (translatedBox a b o))⁻¹ * ∫ x in translatedBox a b o, f x := by
  rw [translatedBox_volume hab]
  simp only [translatedBoxMean, inv_pow]

theorem translatedBoxMean_pullback (a b : ℝ) (o : Space) (f : Space → ℝ) :
    translatedBoxMean a b o f = boxMean a b (fun y => f (y + o)) := by
  rw [translatedBoxMean, translatedBox_integral]
  rfl

theorem translated_box_mean_poincare {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) (o : Space) :
    (∫ x in translatedBox a b o, (f x - translatedBoxMean a b o f) ^ 2) ≤
      3 * (b - a) ^ 2 *
        ∑ j : Fin 3, ∫ x in translatedBox a b o, (fderiv ℝ f x (Pi.single j 1)) ^ 2 := by
  let u : Space → ℝ := fun y => f (y + o)
  have hu : ContDiff ℝ 1 u := hf.comp (contDiff_id.add contDiff_const)
  have ht := box_mean_poincare hab hu
  have he : (∫ x in translatedBox a b o, (f x - translatedBoxMean a b o f) ^ 2) =
      ∫ y in boxSet a b, (u y - boxMean a b u) ^ 2 := by
    rw [translatedBox_integral, translatedBoxMean_pullback]
  have hg (j : Fin 3) : (∫ y in boxSet a b, (fderiv ℝ u y (Pi.single j 1)) ^ 2) =
      ∫ x in translatedBox a b o, (fderiv ℝ f x (Pi.single j 1)) ^ 2 := by
    rw [translatedBox_integral]
    simp only [u, fderiv_comp_add_right]
  rw [he]
  simpa only [hg] using ht

theorem translated_box_mean_error_tendsto {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (a b : ℝ) (o : Space) :
    Tendsto (fun n => ∫ x in translatedBox a b o,
      (u n x - translatedBoxMean a b o (u n)) ^ 2) atTop
        (𝓝 (∫ x in translatedBox a b o, (f x - translatedBoxMean a b o f) ^ 2)) := by
  have hμ : (volume.restrict (translatedBox a b o)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top
  exact centered_square_integral_tendsto hμ
    (fun n => (hu.memLp n).restrict (translatedBox a b o))
    (hu.weak_gradient.1.restrict (translatedBox a b o))
    (smooth_value_local_L2_tendsto hu (translatedBox a b o)) (((b - a)⁻¹) ^ 3)

theorem weak_translated_box_mean_poincare {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u) {a b : ℝ} (hab : a < b) (o : Space) :
    (∫ x in translatedBox a b o, (f x - translatedBoxMean a b o f) ^ 2) ≤
      3 * (b - a) ^ 2 * ∑ j : Fin 3, ∫ x in translatedBox a b o, (g j x) ^ 2 := by
  obtain ⟨u, hu⟩ := hf
  have hl := translated_box_mean_error_tendsto hu a b o
  have hr := (tendsto_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j _ => smooth_gradient_local_square_integral_tendsto hu (translatedBox a b o) j)).const_mul
      (3 * (b - a) ^ 2)
  exact le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n => translated_box_mean_poincare (hu.smooth n) hab o))

end FreudenthalSVLean.TranslatedBoxH1Estimate
