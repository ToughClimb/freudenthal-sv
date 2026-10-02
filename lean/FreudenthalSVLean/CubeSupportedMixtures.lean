import FreudenthalSVLean.BogovskiiMixtureFourier
import FreudenthalSVLean.BogovskiiKernelDifferentiation

/-!
# Actual continuity and support of affine cube mixtures

For the continuous lifting in manuscript Lemma `means`, normalized
mixtures of continuous cube-supported functions are jointly continuous
away from t=0 and supported in the actual closed cube for 0<t<=1.
One fixed continuous positive time clipping supplies a global continuous
parameter integrand, equal to the original mixture on every positive
truncated interval. All support assertions follow from cube convexity.
-/

open scoped Real SchwartzMap LineDeriv
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.BogovskiiMixtureFourier

noncomputable section

namespace FreudenthalSVLean.CubeSupportedMixtures

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def cubeE : Set E := coordinates ⁻¹' cube

theorem cubeE_compact : IsCompact cubeE :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.isCompact_preimage.mpr
    isCompact_Icc

theorem cubeE_closed : IsClosed cubeE := cubeE_compact.isClosed

theorem cubeE_volume : (volume : Measure E) cubeE = 1 := by
  rw [cubeE, cube, coordinates_volume.measure_preimage measurableSet_Icc.nullMeasurableSet]
  simp only [Real.volume_Icc_pi, Pi.one_apply, Pi.zero_apply, sub_zero,
    ENNReal.ofReal_one, Finset.prod_const_one]

theorem cubeE_convex : Convex ℝ cubeE :=
  (convex_Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ : Fin 3 => (1 : ℝ))).linear_preimage
    coordinates.toLinearMap

def mixtureArgument (t : ℝ) (x y : E) : E := t⁻¹ • (x - (1 - t) • y)

theorem mixture_reconstruct {t : ℝ} (ht : t ≠ 0) (x y : E) :
    t • mixtureArgument t x y + (1 - t) • y = x := by
  rw [mixtureArgument, smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]

theorem mixtureArgument_outside {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {x y : E} (hx : x ∉ cubeE) (hy : y ∈ cubeE) : mixtureArgument t x y ∉ cubeE := by
  intro hz
  have hm := cubeE_convex hz hy ht.le (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
  rw [mixture_reconstruct ht.ne' x y] at hm
  exact hx hm

theorem spatialMixture_zero {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {g f : E → ℂ} (hg : ∀ z ∉ cubeE, g z = 0) (hf : ∀ y ∉ cubeE, f y = 0)
    {x : E} (hx : x ∉ cubeE) : spatialMixture t g f x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change normalizedDilation t g (x - (1 - t) • y) * f y = 0
  by_cases hy : y ∈ cubeE
  · change (t ^ 3)⁻¹ • g (mixtureArgument t x y) * f y = 0
    rw [hg _ (mixtureArgument_outside ht ht1 hx hy), smul_zero, zero_mul]
  · rw [hf y hy, mul_zero]

def clippedMixtureIntegrand (ε : ℝ) (g f : E → ℂ) (p : ℝ × E) (y : E) : ℂ :=
  normalizedDilation (clippedTime ε p.1) g (p.2 - (1 - clippedTime ε p.1) • y) * f y

theorem clippedMixtureIntegrand_continuous {ε : ℝ} (hε : 0 < ε)
    {g f : E → ℂ} (hg : Continuous g) (hf : Continuous f) :
    Continuous (clippedMixtureIntegrand ε g f).uncurry := by
  have ht : Continuous (fun p : (ℝ × E) × E => clippedTime ε p.1.1) :=
    (continuous_const.max continuous_fst.fst)
  have htn : ∀ p : (ℝ × E) × E, clippedTime ε p.1.1 ≠ 0 :=
    fun p => (clippedTime_pos hε p.1.1).ne'
  have hi := ht.inv₀ htn
  have ha : Continuous (fun p : (ℝ × E) × E =>
      (clippedTime ε p.1.1)⁻¹ • (p.1.2 - (1 - clippedTime ε p.1.1) • p.2)) :=
    hi.smul (continuous_fst.snd.sub ((continuous_const.sub ht).smul continuous_snd))
  exact (((ht.pow 3).inv₀ (fun p => pow_ne_zero 3 (htn p))).smul (hg.comp ha)).mul
    (hf.comp continuous_snd)

def clippedMixture (ε : ℝ) (g f : E → ℂ) (p : ℝ × E) : ℂ :=
  ∫ y in cubeE, clippedMixtureIntegrand ε g f p y

theorem clippedMixture_continuous {ε : ℝ} (hε : 0 < ε)
    {g f : E → ℂ} (hg : Continuous g) (hf : Continuous f) :
    Continuous (clippedMixture ε g f) :=
  continuous_parametric_integral_of_continuous
    (clippedMixtureIntegrand_continuous hε hg hf) cubeE_compact

theorem clippedMixture_eq {ε t : ℝ} (ht : ε ≤ t) {g f : E → ℂ}
    (hf : ∀ y ∉ cubeE, f y = 0) (x : E) :
    clippedMixture ε g f (t, x) = spatialMixture t g f x := by
  unfold clippedMixture clippedMixtureIntegrand
  rw [clippedTime_eq ht]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hf y hy, mul_zero])

theorem schwartz_derivative_support {φ : 𝓢(E, ℂ)}
    (hφ : Function.support (φ : E → ℂ) ⊆ cubeE) (m : E) :
    Function.support (⇑(∂_{m} φ : 𝓢(E, ℂ))) ⊆ cubeE :=
  (subset_tsupport _).trans ((SchwartzMap.tsupport_lineDerivOp_subset m φ).trans
    (closure_minimal hφ cubeE_closed))

end FreudenthalSVLean.CubeSupportedMixtures
