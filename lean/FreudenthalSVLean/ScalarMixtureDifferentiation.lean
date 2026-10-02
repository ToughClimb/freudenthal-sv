import FreudenthalSVLean.ScalarMixtureEstimate
import FreudenthalSVLean.CompactParameterDifferentiation

/-!
# Genuine differentiation of scalar spatial mixtures

For the continuous lift in manuscript Lemma `means`, each normalized
scalar mixture is integrated over the actual compact time/cube domain.
The actual Frechet derivative follows from product/chain rules and the
proved compact-parameter theorem. Its value on a direction is exactly
the actual directional mixture time integral estimated in
`ScalarMixtureEstimate`. The derivative is not stipulated by its Fourier
transform; it is differentiated from the true spatial formula.
-/

open scoped SchwartzMap Real LineDeriv ContDiff
open MeasureTheory Set Filter
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.BogovskiiMixtureFourier
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.CompactParameterDifferentiation
open FreudenthalSVLean.SpatialLowerHalfL2
open FreudenthalSVLean.ScalarMixtureEstimate

noncomputable section

namespace FreudenthalSVLean.ScalarMixtureDifferentiation

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree
abbrev Parameter := ℝ × E

def scalarParameterBox (ε : ℝ) : Set Parameter := Icc ε 1 ×ˢ cubeE

theorem scalarParameterBox_compact (ε : ℝ) : IsCompact (scalarParameterBox ε) :=
  isCompact_Icc.prod cubeE_compact

def scalarField (ε : ℝ) (φ f : 𝓢(E, ℂ)) (x : E) (p : Parameter) : ℂ :=
  normalizedDilation (clippedTime ε p.1) φ (x - (1 - clippedTime ε p.1) • p.2) * f p.2

def scalarFieldDerivative (ε : ℝ) (φ f : 𝓢(E, ℂ)) (x : E) (p : Parameter) : E →L[ℝ] ℂ :=
  f p.2 • ((clippedTime ε p.1 ^ 3)⁻¹ •
    ((fderiv ℝ (φ : E → ℂ) (mixtureArgument (clippedTime ε p.1) x p.2)).comp
      ((clippedTime ε p.1)⁻¹ • ContinuousLinearMap.id ℝ E)))

def scalarMixtureIntegral (ε : ℝ) (φ f : 𝓢(E, ℂ)) (x : E) : ℂ :=
  ∫ p in scalarParameterBox ε, scalarField ε φ f x p

theorem mixtureArgument_hasFDerivAt (t : ℝ) (x y : E) :
    HasFDerivAt (fun z : E => mixtureArgument t z y)
      (t⁻¹ • ContinuousLinearMap.id ℝ E) x := by
  simpa only [mixtureArgument, sub_zero] using!
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub
      (hasFDerivAt_const (𝕜 := ℝ) ((1 - t) • y) x)).const_smul (t⁻¹ : ℝ)

theorem scalarField_hasFDerivAt (ε : ℝ) (φ f : 𝓢(E, ℂ)) (p : Parameter) (x : E) :
    HasFDerivAt (scalarField ε φ f · p) (scalarFieldDerivative ε φ f x p) x := by
  have harg := mixtureArgument_hasFDerivAt (clippedTime ε p.1) x p.2
  have hφ := (φ.differentiableAt (x := mixtureArgument (clippedTime ε p.1) x p.2)).hasFDerivAt
  have h := (hφ.comp x harg).const_smul ((clippedTime ε p.1 ^ 3)⁻¹ : ℝ)
  simpa only [scalarField, scalarFieldDerivative, normalizedDilation, mixtureArgument,
    Function.comp_def] using! h.mul_const (f p.2)

theorem scalarField_continuous {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) : Continuous (scalarField ε φ f).uncurry := by
  have ht : Continuous (fun p : E × Parameter => clippedTime ε p.2.1) :=
    continuous_const.max continuous_snd.fst
  have htn : ∀ p : E × Parameter, clippedTime ε p.2.1 ≠ 0 :=
    fun p => (clippedTime_pos hε p.2.1).ne'
  have harg : Continuous (fun p : E × Parameter =>
      (clippedTime ε p.2.1)⁻¹ • (p.1 - (1 - clippedTime ε p.2.1) • p.2.2)) :=
    (ht.inv₀ htn).smul (continuous_fst.sub ((continuous_const.sub ht).smul continuous_snd.snd))
  exact (((ht.pow 3).inv₀ (fun p => pow_ne_zero 3 (htn p))).smul
    (φ.continuous.comp harg)).mul (f.continuous.comp continuous_snd.snd)

theorem scalarFieldDerivative_continuous {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) : Continuous (scalarFieldDerivative ε φ f).uncurry := by
  have ht : Continuous (fun p : E × Parameter => clippedTime ε p.2.1) :=
    continuous_const.max continuous_snd.fst
  have htn : ∀ p : E × Parameter, clippedTime ε p.2.1 ≠ 0 :=
    fun p => (clippedTime_pos hε p.2.1).ne'
  have hinv := ht.inv₀ htn
  have harg : Continuous (fun p : E × Parameter =>
      mixtureArgument (clippedTime ε p.2.1) p.1 p.2.2) :=
    hinv.smul (continuous_fst.sub ((continuous_const.sub ht).smul continuous_snd.snd))
  have hd := ((φ.smooth (⊤ : ℕ∞)).continuous_fderiv (by simp)).comp harg
  exact (f.continuous.comp continuous_snd.snd).smul
    (((ht.pow 3).inv₀ (fun p => pow_ne_zero 3 (htn p))).smul
      (hd.clm_comp (hinv.smul continuous_const)))

theorem scalarMixtureIntegral_hasFDerivAt {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (x : E) :
    HasFDerivAt (scalarMixtureIntegral ε φ f)
      (∫ p in scalarParameterBox ε, scalarFieldDerivative ε φ f x p) x :=
  compact_integral_hasFDerivAt (scalarParameterBox ε) (scalarParameterBox_compact ε)
    (scalarField ε φ f) (scalarFieldDerivative ε φ f) (scalarField_continuous hε φ f)
    (scalarFieldDerivative_continuous hε φ f) (fun p _ x => scalarField_hasFDerivAt ε φ f p x) x

theorem scalarMixtureIntegral_contDiff_one {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) : ContDiff ℝ 1 (scalarMixtureIntegral ε φ f) :=
  compact_integral_contDiff_one (scalarParameterBox ε) (scalarParameterBox_compact ε)
    (scalarField ε φ f) (scalarFieldDerivative ε φ f) (scalarField_continuous hε φ f)
    (scalarFieldDerivative_continuous hε φ f) (fun p _ x => scalarField_hasFDerivAt ε φ f p x)

theorem scalarFieldDerivative_apply (ε : ℝ) (φ f : 𝓢(E, ℂ)) (x m : E) (p : Parameter) :
    scalarFieldDerivative ε φ f x p m = (clippedTime ε p.1)⁻¹ •
      clippedMixtureIntegrand ε (∂_{m} φ : 𝓢(E, ℂ)) f (p.1, x) p.2 := by
  simp only [scalarFieldDerivative, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, clippedMixtureIntegrand, normalizedDilation,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, mixtureArgument, Complex.real_smul, smul_eq_mul]
  ring

theorem scalarMixtureIntegral_partial {ε : ℝ} (hε : 0 < ε)
    (φ f : 𝓢(E, ℂ)) (x m : E) :
    fderiv ℝ (scalarMixtureIntegral ε φ f) x m = scalarDerivativeIntegral ε φ f m x := by
  have hi : IntegrableOn (scalarFieldDerivative ε φ f x) (scalarParameterBox ε) :=
    ((scalarFieldDerivative_continuous hε φ f).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (scalarParameterBox_compact ε)
  rw [(scalarMixtureIntegral_hasFDerivAt hε φ f x).fderiv,
    ContinuousLinearMap.integral_apply hi m]
  have hic : IntegrableOn (fun p : Parameter => scalarFieldDerivative ε φ f x p m)
      (scalarParameterBox ε) :=
    (((scalarFieldDerivative_continuous hε φ f).comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const).continuousOn.integrableOn_compact
        (scalarParameterBox_compact ε)
  have he : (volume : Measure Parameter).restrict (scalarParameterBox ε) =
      (volume.restrict (Icc ε (1 : ℝ))).prod ((volume : Measure E).restrict cubeE) :=
    (Measure.prod_restrict (Icc ε (1 : ℝ)) cubeE).symm
  change Integrable _ (volume.restrict (scalarParameterBox ε)) at hic
  rw [he] at hic ⊢
  rw [integral_prod _ hic]
  apply integral_congr_ae
  filter_upwards with t
  simp_rw [scalarFieldDerivative_apply]
  rw [integral_smul]
  rfl

end FreudenthalSVLean.ScalarMixtureDifferentiation
