import FreudenthalSVLean.BogovskiiCubeGeometry
import FreudenthalSVLean.EuclideanCoordinateTransport
import FreudenthalSVLean.FourierDirectionalDecay

/-!
# Actual fixed Schwartz kernels for the cube lifting

For the continuous lifting in manuscript Lemma `means`, the normalized
central bump and its three coordinate moments are genuine smooth,
compactly supported functions. Transport through the measure-preserving
Euclidean coordinate equivalence, followed by the real-to-complex
embedding, gives the exact Schwartz inputs to the Fourier estimate.
In particular these are the actual spatial kernels of the Bogovskii
formula, not abstract functions with assumed decay or normalization.
-/

open scoped ContDiff SchwartzMap
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.EuclideanCoordinateTransport

noncomputable section

namespace FreudenthalSVLean.BogovskiiSchwartzKernels

set_option backward.isDefEq.respectTransparency false

def rhoEuclidean : EuclideanThree → ℝ := fun x => rho (coordinates x)

theorem rhoEuclidean_contDiff : ContDiff ℝ ∞ rhoEuclidean :=
  contDiff_pullback rho_contDiff

theorem rhoEuclidean_compact : HasCompactSupport rhoEuclidean :=
  rho_compact.comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph

theorem rhoEuclidean_integral : (∫ x : EuclideanThree, rhoEuclidean x) = 1 :=
  (integral_pullback rho).trans rho_integral

def rhoComplex : EuclideanThree → ℂ := fun x => (rhoEuclidean x : ℂ)

theorem rhoComplex_contDiff : ContDiff ℝ ∞ rhoComplex :=
  Complex.ofRealCLM.contDiff.comp rhoEuclidean_contDiff

theorem rhoComplex_compact : HasCompactSupport rhoComplex :=
  rhoEuclidean_compact.comp_left (by simp : Complex.ofReal (0 : ℝ) = 0)

def rhoSchwartz : 𝓢(EuclideanThree, ℂ) :=
  rhoComplex_compact.toSchwartzMap rhoComplex_contDiff

theorem rhoSchwartz_apply (x : EuclideanThree) :
    rhoSchwartz x = (rho (coordinates x) : ℂ) := rfl

def momentComplex (j : Fin 3) : EuclideanThree → ℂ :=
  fun x => ((coordinates x) j : ℂ) * rhoComplex x

theorem momentComplex_contDiff (j : Fin 3) : ContDiff ℝ ∞ (momentComplex j) := by
  unfold momentComplex
  exact (Complex.ofRealCLM.contDiff.comp ((ContinuousLinearMap.proj j).contDiff.comp
    coordinates.contDiff)).mul rhoComplex_contDiff

theorem momentComplex_compact (j : Fin 3) : HasCompactSupport (momentComplex j) :=
  rhoComplex_compact.mul_left

def momentSchwartz (j : Fin 3) : 𝓢(EuclideanThree, ℂ) :=
  (momentComplex_compact j).toSchwartzMap (momentComplex_contDiff j)

theorem momentSchwartz_apply (j : Fin 3) (x : EuclideanThree) :
    momentSchwartz j x = ((coordinates x) j * rho (coordinates x) : ℝ) := by
  change ((coordinates x) j : ℂ) * (rho (coordinates x) : ℂ) = _
  exact (Complex.ofReal_mul _ _).symm

end FreudenthalSVLean.BogovskiiSchwartzKernels
