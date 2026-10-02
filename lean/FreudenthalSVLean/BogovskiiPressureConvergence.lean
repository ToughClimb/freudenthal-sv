import FreudenthalSVLean.BogovskiiPressureMixture
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine L2 convergence of the truncated divergence pressures

For the continuous lift in manuscript Lemma `means`, the actual mass
mixtures converge to every smooth cube-supported input in genuine squared
L2 error. The nonsingular pressure formula, normalized nonnegative bump
and dominated convergence give pointwise convergence and a uniform bound.
All errors have actual cube support, giving an integrable L2 dominator.
The positive truncations are explicit and tend to zero.
-/

open scoped ContDiff Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiKernelDivergence
open FreudenthalSVLean.BogovskiiDivergenceIdentity
open FreudenthalSVLean.BogovskiiPressureMixture

noncomputable section

namespace FreudenthalSVLean.BogovskiiPressureConvergence

set_option backward.isDefEq.respectTransparency false

def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity

theorem epsilon_le_half (n : ℕ) : epsilon n ≤ 1 / 2 := by
  unfold epsilon
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 3) (by norm_num)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem epsilon_lt_one (n : ℕ) : epsilon n < 1 :=
  (epsilon_le_half n).trans_lt (by norm_num)

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) := by
  have he := (tendsto_add_atTop_iff_nat 2).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) atTop (𝓝 0)
  convert! he using 1
  funext n
  push_cast
  ring

theorem rho_integrable : Integrable rho := rho_contDiff.continuous.integrable_of_hasCompactSupport rho_compact

theorem smoothedPressure_continuous (t : ℝ) {q : Space → ℝ} (hq : Continuous q)
    (hs : ∀ y : Space, y ∉ cube → q y = 0) : Continuous (smoothedPressure t q) := by
  have hc : Continuous (fun p : Space × Space => massKernel t p.1 p.2 * q p.2) := by
    unfold massKernel kernelArgument
    exact (continuous_const.mul (rho_contDiff.continuous.comp
      (continuous_snd.add ((continuous_const (y := (t⁻¹ : ℝ))).smul
        (continuous_fst.sub continuous_snd))))).mul
        (hq.comp continuous_snd)
  have he : (fun x : Space => ∫ y in cube, massKernel t x y * q y) = smoothedPressure t q := by
    funext x
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hs y hy, mul_zero])
  rw [← he]
  exact continuous_parametric_integral_of_continuous hc isCompact_Icc

theorem smoothedPressure_zero {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {q : Space → ℝ} (hs : ∀ y : Space, y ∉ cube → q y = 0)
    {x : Space} (hx : x ∉ cube) : smoothedPressure t q x = 0 := by
  have hi : x ∉ interiorBox t := fun h => hx
    ((interiorBox_subset_openCube ht).trans openCube_subset_cube h)
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change (t ^ 3)⁻¹ * rho (kernelArgument t x y) * q y = 0
  rw [mul_assoc, kernel_zero_outside ht le_rfl ht1 q hs x y hi, mul_zero]

theorem smoothedPressure_norm_bound {t : ℝ} (ht : 0 < t) (hth : t ≤ 1 / 2)
    (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    {M : ℝ} (hb : ∀ y : Space, ‖q y‖ ≤ M) (x : Space) :
    ‖smoothedPressure t q x‖ ≤ 8 * M := by
  have ht1 : t < 1 := by linarith
  have hp : 0 < 1 - t := sub_pos.mpr ht1
  have hpow : 1 / 8 ≤ (1 - t) ^ 3 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 1 / 2 ≤ 1 - t) 3
    norm_num at he
    exact he
  have hinv : ((1 - t) ^ 3)⁻¹ ≤ 8 := by
    have he := (inv_le_inv₀ (pow_pos hp 3) (by norm_num : (0 : ℝ) < 1 / 8)).mpr hpow
    norm_num at he
    exact he
  have hi : ‖∫ z : Space, rho z * q (pressureArgument t x z)‖ ≤ M := by
    calc
      _ ≤ ∫ z : Space, M * rho z := by
        apply norm_integral_le_of_norm_le (rho_integrable.const_mul M)
        filter_upwards with z
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg z)]
        exact (mul_le_mul_of_nonneg_left (hb _) (rho_nonneg z)).trans_eq (mul_comm _ _)
      _ = _ := by rw [integral_const_mul, rho_integral, mul_one]
  rw [smoothedPressure_formula ht ht1 q hd hc x, norm_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hp 3))]
  exact mul_le_mul hinv hi (norm_nonneg _) (by norm_num)

theorem pressureArgument_tendsto (x z : Space) :
    Tendsto (fun n => pressureArgument (epsilon n) x z) atTop (𝓝 x) := by
  have he : Tendsto (fun n => (1 : ℝ) - epsilon n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub epsilon_tendsto
  have hi := he.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hz := epsilon_tendsto.smul (tendsto_const_nhds (x := z))
  have hd := (tendsto_const_nhds (x := x)).sub hz
  simpa only [pressureArgument, inv_one, zero_smul, sub_zero, one_smul] using hi.smul hd

theorem smoothedPressure_pointwise_tendsto (q : Space → ℝ) (hd : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (x : Space) :
    Tendsto (fun n => smoothedPressure (epsilon n) q x) atTop (𝓝 (q x)) := by
  obtain ⟨M, hb⟩ := hc.exists_bound_of_continuous hd.continuous
  have hm (n : ℕ) : AEStronglyMeasurable (fun z : Space => rho z * q (pressureArgument (epsilon n) x z)) :=
    (rho_contDiff.continuous.mul (hd.continuous.comp (by unfold pressureArgument; fun_prop))).aestronglyMeasurable
  have hi := tendsto_integral_of_dominated_convergence (fun z : Space => M * rho z) hm
    (rho_integrable.const_mul M)
    (fun n => Eventually.of_forall (fun z => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg z)]
      exact (mul_le_mul_of_nonneg_left (hb _) (rho_nonneg z)).trans_eq (mul_comm _ _)))
    (Eventually.of_forall (fun z =>
      (tendsto_const_nhds (x := rho z)).mul ((hd.continuous.tendsto x).comp (pressureArgument_tendsto x z))))
  have hp : Tendsto (fun n => ((1 - epsilon n) ^ 3)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have he : Tendsto (fun n => (1 : ℝ) - epsilon n) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub epsilon_tendsto
    simpa only [one_pow, inv_one] using (he.pow 3).inv₀ (by norm_num : (1 : ℝ) ^ 3 ≠ 0)
  have hh := hp.mul hi
  simp only [integral_mul_const, rho_integral, one_mul] at hh
  convert! hh using 1
  funext n
  exact smoothedPressure_formula (epsilon_pos n) (epsilon_lt_one n) q hd hc x

theorem smoothedPressure_L2_tendsto (q : Space → ℝ) (hd : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hs : Function.support q ⊆ cube) :
    Tendsto (fun n => ∫ x : Space, (smoothedPressure (epsilon n) q x - q x) ^ 2) atTop (𝓝 0) := by
  have hzero : ∀ y : Space, y ∉ cube → q y = 0 :=
    fun y hy => Function.notMem_support.mp (fun h => hy (hs h))
  obtain ⟨M, hb⟩ := hc.exists_bound_of_continuous hd.continuous
  have hM : 0 ≤ M := (norm_nonneg (q 0)).trans (hb 0)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x : Space => (smoothedPressure (epsilon n) q x - q x) ^ 2)
      (volume.restrict cube) :=
    (((smoothedPressure_continuous _ hd.continuous hzero).sub hd.continuous).pow 2).aestronglyMeasurable
  have hbnd (n : ℕ) : ∀ᵐ x ∂volume.restrict cube,
      ‖(smoothedPressure (epsilon n) q x - q x) ^ 2‖ ≤ 81 * M ^ 2 := by
    filter_upwards with x
    have hn := (norm_sub_le _ _).trans (add_le_add
      (smoothedPressure_norm_bound (epsilon_pos n) (epsilon_le_half n) q hd hc hb x) (hb x))
    rw [norm_pow]
    nlinarith [norm_nonneg (smoothedPressure (epsilon n) q x - q x)]
  have hl : ∀ᵐ x ∂volume.restrict cube,
      Tendsto (fun n => (smoothedPressure (epsilon n) q x - q x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((smoothedPressure_pointwise_tendsto q hd hc x).sub
        (tendsto_const_nhds (x := q x))).pow 2
  have he := tendsto_integral_of_dominated_convergence (fun _ : Space => 81 * M ^ 2)
    hm (integrableOn_const (isCompact_Icc : IsCompact cube).measure_ne_top) hbnd hl
  simp only [integral_zero] at he
  convert! he using 1
  funext n
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [smoothedPressure_zero (epsilon_pos n) (epsilon_lt_one n).le hzero hx, hzero x hx,
      sub_self, zero_pow (by decide)])

end FreudenthalSVLean.BogovskiiPressureConvergence
