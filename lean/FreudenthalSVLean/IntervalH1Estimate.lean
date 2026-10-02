import FreudenthalSVLean.WeakFaceGauss
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual interval H1 difference estimates for stable interpolation

For the local interpolation estimate in manuscript Lemma `means` and
equation `SZ`, the fundamental theorem of calculus and genuine L2
Cauchy--Schwarz bound endpoint differences by interval derivative energy.
The finite-measure integral inequality is proved from the actual L2
inner product, not a stipulated quadrature functional.  Enlarging the
interval gives a bound valid for arbitrary points of a fixed interval;
coordinate fibers will supply the required local box Poincare estimate.
No interpolant or continuous divergence inverse is assumed here.
-/

open scoped BigOperators Topology
open MeasureTheory Set
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakFaceGauss

noncomputable section

namespace FreudenthalSVLean.IntervalH1Estimate

set_option backward.isDefEq.respectTransparency false

theorem integral_square_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ univ ≠ ⊤) {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, (f x) ^ 2 ∂μ := by
  let c : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ hμ (1 : ℝ)
  have hc : ‖c‖ ^ 2 = μ.real univ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      MeasurableSet.univ MeasurableSet.univ hμ hμ).trans (by rw [Set.inter_self])
  have he : inner ℝ c (hf.toLp f) = ∫ x, f x ∂μ := l2Integral_toLp μ hμ hf
  have ht := real_inner_mul_inner_self_le c (hf.toLp f)
  simpa only [he, real_inner_self_eq_norm_sq, hc, toLp_norm_square, ← pow_two] using ht

theorem interval_square_bound {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in Icc a b, f x) ^ 2 ≤ (b - a) * ∫ x in Icc a b, (f x) ^ 2 := by
  have hm : MemLp f 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.restrict).mpr
      ((hf.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have ht := integral_square_bound
    (by simpa only [Measure.restrict_apply_univ] using
      (isCompact_Icc : IsCompact (Icc a b)).measure_ne_top) hm
  have hv : (volume.restrict (Icc a b)).real univ = b - a := by
    change ((volume.restrict (Icc a b)) univ).toReal = b - a
    rw [Measure.restrict_apply_univ]
    exact Real.volume_real_Icc_of_le hab
  simpa only [hv] using ht

theorem endpoint_difference_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in Icc a b, (deriv f x) ^ 2 := by
  have he : (∫ x in Icc a b, deriv f x) = f b - f a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt)
      (hf.continuous_deriv_one.intervalIntegrable _ _)
  rw [← he]
  exact interval_square_bound hab hf.continuous_deriv_one

theorem interval_difference_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f x - f y) ^ 2 ≤ (b - a) * ∫ s in Icc a b, (deriv f s) ^ 2 := by
  have hab := hx.1.trans hx.2
  have hi : IntegrableOn (fun s => (deriv f s) ^ 2) (Icc a b) :=
    (hf.continuous_deriv_one.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hG : 0 ≤ ∫ s in Icc a b, (deriv f s) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  rcases le_total x y with hxy | hyx
  · have ht := endpoint_difference_bound hf hxy
    have hg : (∫ s in Icc x y, (deriv f s) ^ 2) ≤ ∫ s in Icc a b, (deriv f s) ^ 2 :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun s hs => ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩))
    have hw : y - x ≤ b - a := by linarith [hx.1, hy.2]
    have hm := mul_le_mul hw hg (integral_nonneg (fun _ => sq_nonneg _)) (sub_nonneg.mpr hab)
    nlinarith
  · have ht := endpoint_difference_bound hf hyx
    have hg : (∫ s in Icc y x, (deriv f s) ^ 2) ≤ ∫ s in Icc a b, (deriv f s) ^ 2 :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun s hs => ⟨hy.1.trans hs.1, hs.2.trans hx.2⟩))
    have hw : x - y ≤ b - a := by linarith [hy.1, hx.2]
    exact ht.trans (mul_le_mul hw hg (integral_nonneg (fun _ => sq_nonneg _)) (sub_nonneg.mpr hab))

/-- The actual Lebesgue average over a nondegenerate interval. -/
def intervalMean (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ y in Icc a b, f y

theorem interval_mean_square_bound {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (b - a) * (intervalMean a b f) ^ 2 ≤
      ∫ y in Icc a b, (f y) ^ 2 := by
  have hl : 0 < b - a := sub_pos.mpr hab
  have ht := mul_le_mul_of_nonneg_left (interval_square_bound hab.le hf)
    (inv_nonneg.mpr hl.le)
  have he : (b - a)⁻¹ * (∫ y in Icc a b, f y) ^ 2 =
      (b - a) * (intervalMean a b f) ^ 2 := by
    simp only [intervalMean]
    field_simp [hl.ne']
  rw [he] at ht
  simpa only [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] using ht

theorem interval_mean_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) :
    intervalMean a b (fun x => f x - g x) =
      intervalMean a b f - intervalMean a b g := by
  simp only [intervalMean, integral_sub hf.integrableOn_Icc hg.integrableOn_Icc,
    mul_sub]

theorem interval_mean_const (a b c : ℝ) (hab : a < b) :
    intervalMean a b (fun _ => c) = c := by
  rw [intervalMean, setIntegral_const, Real.volume_real_Icc_of_le hab.le]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hab).ne', one_mul]

theorem interval_mean_difference_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    (f x - intervalMean a b f) ^ 2 ≤
      (b - a) * ∫ s in Icc a b, (deriv f s) ^ 2 := by
  have hl : 0 < b - a := sub_pos.mpr hab
  have hd : Continuous (fun y => f x - f y) := continuous_const.sub hf.continuous
  have hi_const (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Icc a b) :=
    continuous_const.integrableOn_Icc
  have he : (∫ y in Icc a b, f x - f y) =
      (b - a) * (f x - intervalMean a b f) := by
    rw [integral_sub (hi_const (f x))
      hf.continuous.integrableOn_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le hab.le]
    simp only [smul_eq_mul, intervalMean]
    field_simp [hl.ne']
  have hm : (∫ y in Icc a b, (f x - f y) ^ 2) ≤
      (b - a) ^ 2 * ∫ s in Icc a b, (deriv f s) ^ 2 := by
    calc
      _ ≤ ∫ _y in Icc a b,
          (b - a) * ∫ s in Icc a b, (deriv f s) ^ 2 :=
        setIntegral_mono_on (hd.pow 2).integrableOn_Icc
          (hi_const _) measurableSet_Icc
          (fun y hy => interval_difference_bound hf hx hy)
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab.le]
        simp only [smul_eq_mul]
        ring
  have ht := (interval_square_bound hab.le hd).trans
    (mul_le_mul_of_nonneg_left hm hl.le)
  rw [he, mul_pow] at ht
  have hs : (b - a) ^ 2 * (f x - intervalMean a b f) ^ 2 ≤
      (b - a) ^ 2 * ((b - a) * ∫ s in Icc a b, (deriv f s) ^ 2) := by
    calc
      _ ≤ (b - a) * ((b - a) ^ 2 * ∫ s in Icc a b, (deriv f s) ^ 2) := ht
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hl)).mp hs

theorem interval_mean_poincare {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, (f x - intervalMean a b f) ^ 2) ≤
      (b - a) ^ 2 * ∫ s in Icc a b, (deriv f s) ^ 2 := by
  have hi_const (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Icc a b) :=
    continuous_const.integrableOn_Icc
  calc
    _ ≤ ∫ _x in Icc a b,
        (b - a) * ∫ s in Icc a b, (deriv f s) ^ 2 :=
      setIntegral_mono_on
        ((hf.continuous.sub continuous_const).pow 2).integrableOn_Icc
        (hi_const _) measurableSet_Icc
        (fun x hx => interval_mean_difference_bound hf hab hx)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le hab.le]
      simp only [smul_eq_mul]
      ring

end FreudenthalSVLean.IntervalH1Estimate
