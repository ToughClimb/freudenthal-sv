import FreudenthalSVLean.TranslatedBoxH1Estimate

/-!
# Boundary-compatible local box estimates

For the boundary interpolation step in manuscript Lemma `means` and
equation `SZ`, the genuine H1_0 smooth-closure criterion implies zero
extension outside the open cube in the actual almost-everywhere sense.
A local box with at least half its volume in that zero region satisfies
an uncentered Poincare estimate with the square of its side length.  This
does not assume pointwise traces of an arbitrary H1 function, a stable
interpolation theorem, or a continuous divergence inverse.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.TranslatedBoxH1Estimate

noncomputable section

namespace FreudenthalSVLean.BoundaryBoxH1Estimate

set_option backward.isDefEq.respectTransparency false

theorem inH1ZeroCube_zero_outside {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) :
    f =ᵐ[volume.restrict openCubeᶜ] (0 : Space → ℝ) := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hz (n : ℕ) : ((ha.memLp n).restrict openCubeᶜ).toLp (u n) = 0 := by
    have he : u n =ᵐ[volume.restrict openCubeᶜ] (0 : Space → ℝ) := by
      filter_upwards [ae_restrict_mem openCube_isOpen.measurableSet.compl] with x hx
      exact image_eq_zero_of_notMem_tsupport (fun ht => hx ((hu n).2.2.1 ht))
    have hzero : MemLp (0 : Space → ℝ) 2 (volume.restrict openCubeᶜ) := MemLp.zero
    exact (MemLp.toLp_congr ((ha.memLp n).restrict openCubeᶜ) hzero he).trans
      (MemLp.toLp_zero hzero)
  have hl := smooth_value_local_L2_tendsto ha openCubeᶜ
  have he : (hw.1.restrict openCubeᶜ).toLp f = 0 :=
    tendsto_nhds_unique hl (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 2 (volume.restrict openCubeᶜ)))
        atTop (𝓝 0)))
  exact (MemLp.coeFn_toLp (hw.1.restrict openCubeᶜ)).symm.trans
    (Lp.eq_zero_iff_ae_eq_zero.mp he)

theorem inH1ZeroCube_zero_on_set {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) {S : Set Space} (hS : S ⊆ openCubeᶜ) :
    f =ᵐ[volume.restrict S] (0 : Space → ℝ) :=
  (inH1ZeroCube_zero_outside hf).filter_mono (ae_mono (Measure.restrict_mono hS le_rfl))

/-- An uncentered estimate from a genuine zero subset of at least half the volume. -/
theorem square_integral_bound_of_zero_half {f : Space → ℝ}
    (hf : MemLp f 2 volume) {B S : Set Space} (hB : MeasurableSet B)
    (hfinite : volume B ≠ ⊤) (hSB : S ⊆ B)
    (hzero : f =ᵐ[volume.restrict S] (0 : Space → ℝ))
    (hhalf : volume.real B ≤ 2 * volume.real S) (m R : ℝ)
    (hlocal : (∫ x in B, (f x - m) ^ 2) ≤ R) :
    (∫ x in B, (f x) ^ 2) ≤ 6 * R := by
  let : IsFiniteMeasure (volume.restrict B) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfinite⟩
  have hi : IntegrableOn (fun x => (f x - m) ^ 2) B := by
    simpa only [Pi.sub_apply] using!
      ((hf.restrict B).sub (memLp_const (μ := volume.restrict B) (p := 2) m)).integrable_sq
  have hm : (∫ x in S, (f x - m) ^ 2) = volume.real S * m ^ 2 := by
    calc
      _ = ∫ _x in S, m ^ 2 := integral_congr_ae
        (hzero.mono (fun x hx => by simp only [hx, Pi.zero_apply]; ring))
      _ = _ := by rw [setIntegral_const]; rfl
  have hS : (∫ x in S, (f x - m) ^ 2) ≤ ∫ x in B, (f x - m) ^ 2 :=
    setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall hSB)
  have hmean : volume.real B * m ^ 2 ≤ 2 * R := by
    calc
      _ ≤ (2 * volume.real S) * m ^ 2 :=
        mul_le_mul_of_nonneg_right hhalf (sq_nonneg m)
      _ = 2 * ∫ x in S, (f x - m) ^ 2 := by rw [hm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hS.trans hlocal) (by norm_num)
  have hiSum : IntegrableOn (fun x => (f x - m) ^ 2 + m ^ 2) B := by
    exact hi.add (integrable_const (μ := volume.restrict B) (m ^ 2))
  have ht : (∫ x in B, (f x) ^ 2) ≤
      ∫ x in B, 2 * ((f x - m) ^ 2 + m ^ 2) :=
    setIntegral_mono_on (hf.restrict B).integrable_sq (hiSum.const_mul 2) hB
      (fun x _ => by nlinarith [sq_nonneg (f x - 2 * m)])
  have he : (∫ x in B, (f x - m) ^ 2 + m ^ 2) =
      (∫ x in B, (f x - m) ^ 2) + volume.real B * m ^ 2 := by
    rw [integral_add hi (integrable_const (μ := volume.restrict B) (m ^ 2)),
      setIntegral_const]
    rfl
  rw [integral_const_mul, he] at ht
  linarith

theorem weak_boundary_box_poincare {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) {a b : ℝ} (hab : a < b) (o : Space)
    {S : Set Space} (hSB : S ⊆ translatedBox a b o) (hS : S ⊆ openCubeᶜ)
    (hhalf : volume.real (translatedBox a b o) ≤ 2 * volume.real S) :
    (∫ x in translatedBox a b o, (f x) ^ 2) ≤
      18 * (b - a) ^ 2 * ∑ j : Fin 3, ∫ x in translatedBox a b o, (g j x) ^ 2 := by
  have ht := square_integral_bound_of_zero_half (B := translatedBox a b o) hf.1.1 measurableSet_Icc
    (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top hSB
    (inH1ZeroCube_zero_on_set hf hS) hhalf (translatedBoxMean a b o f) _
    (weak_translated_box_mean_poincare (inH1ZeroCube_has_smoothApproximation hf) hab o)
  calc
    _ ≤ 6 * (3 * (b - a) ^ 2 *
        ∑ j : Fin 3, ∫ x in translatedBox a b o, (g j x) ^ 2) := ht
    _ = _ := by ring

end FreudenthalSVLean.BoundaryBoxH1Estimate
