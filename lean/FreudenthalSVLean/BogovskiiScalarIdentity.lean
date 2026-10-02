import FreudenthalSVLean.ScalarMixtureDifferentiation
import FreudenthalSVLean.BogovskiiPressureSchwartz
import FreudenthalSVLean.BogovskiiC1Truncation

/-!
# Identification of actual Bogovskii fields with scalar mixtures

For the continuous lifting in manuscript Lemma `means`, the actual
truncated spatial field is exactly the difference of the coordinate-
moment mixture applied to q and the central-bump mixture applied to y_j q.
The identity is proved pointwise from the actual kernel, then integrated
using genuine compact-product integrability and measure-preserving
coordinate transport. It is not inferred from a proposed Fourier symbol.
-/

open scoped ContDiff SchwartzMap
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.EuclideanCubeTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiTruncation
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.BogovskiiC1Truncation
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.NormalizedFourierDilation
open FreudenthalSVLean.BogovskiiSchwartzKernels
open FreudenthalSVLean.BogovskiiPressureSchwartz
open FreudenthalSVLean.ScalarMixtureDifferentiation

noncomputable section

namespace FreudenthalSVLean.BogovskiiScalarIdentity

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

theorem scalarField_difference {ε : ℝ} (hε : 0 < ε) (q : Space → ℝ)
    (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (j : Fin 3) (x : E) (p : ℝ × E) :
    scalarField ε (momentSchwartz j) (pressureSchwartz q hd hc) x p -
      scalarField ε rhoSchwartz (momentInputSchwartz q hd hc j) x p =
        (parameterField ε q j (coordinates x) (p.1, coordinates p.2) : ℂ) := by
  let t := clippedTime ε p.1
  have ht : t ≠ 0 := (clippedTime_pos hε p.1).ne'
  change ((t ^ 3)⁻¹ : ℝ) • (momentSchwartz j (mixtureArgument t x p.2)) *
      pressureSchwartz q hd hc p.2 -
    ((t ^ 3)⁻¹ : ℝ) • (rhoSchwartz (mixtureArgument t x p.2)) *
      momentInputSchwartz q hd hc j p.2 =
        (kernel t (coordinates x) (coordinates p.2) j * q (coordinates p.2) : ℝ)
  rw [momentSchwartz_apply, rhoSchwartz_apply, pressureSchwartz_apply,
    momentInputSchwartz_apply, coordinates_mixtureArgument ht]
  simp only [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  apply congrArg Complex.ofReal
  rw [kernel_split ht]
  field_simp

theorem scalarMixture_difference {ε : ℝ} (hε : 0 < ε) (q : Space → ℝ)
    (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : ∀ y : Space, y ∉ FreudenthalMesh.cube → q y = 0) (j : Fin 3) (x : E) :
    scalarMixtureIntegral ε (momentSchwartz j) (pressureSchwartz q hd hc) x -
      scalarMixtureIntegral ε rhoSchwartz (momentInputSchwartz q hd hc j) x =
        (truncated ε q j (coordinates x) : ℂ) := by
  have h1 : IntegrableOn (scalarField ε (momentSchwartz j) (pressureSchwartz q hd hc) x)
      (scalarParameterBox ε) :=
    ((scalarField_continuous hε _ _).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (scalarParameterBox_compact ε)
  have h2 : IntegrableOn (scalarField ε rhoSchwartz (momentInputSchwartz q hd hc j) x)
      (scalarParameterBox ε) :=
    ((scalarField_continuous hε _ _).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (scalarParameterBox_compact ε)
  have hp : Continuous (parameterField ε q j (coordinates x)) :=
    (parameterField_continuous hε hd.continuous j).comp
      (continuous_const.prodMk continuous_id)
  have hip : IntegrableOn (parameterField ε q j (coordinates x)) (parameterBox ε) :=
    hp.continuousOn.integrableOn_compact (parameterBox_compact ε)
  calc
    _ = ∫ p in scalarParameterBox ε,
        scalarField ε (momentSchwartz j) (pressureSchwartz q hd hc) x p -
          scalarField ε rhoSchwartz (momentInputSchwartz q hd hc j) x p :=
      (integral_sub h1 h2).symm
    _ = ∫ p in scalarParameterBox ε,
        (parameterField ε q j (coordinates x) (p.1, coordinates p.2) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall (scalarField_difference hε q hd hc j x))
    _ = ∫ p in parameterBox ε, (parameterField ε q j (coordinates x) p : ℂ) :=
      integral_parameter_pullback _ (Complex.ofRealCLM.continuous.comp hp)
    _ = (∫ p in parameterBox ε, parameterField ε q j (coordinates x) p : ℝ) := by
      simpa only [Complex.ofRealCLM_apply, Function.comp_def] using!
        (Complex.ofRealCLM.integral_comp_comm hip)
    _ = _ := by rw [parameter_integral_eq_truncated hε hd.continuous hs]

end FreudenthalSVLean.BogovskiiScalarIdentity
