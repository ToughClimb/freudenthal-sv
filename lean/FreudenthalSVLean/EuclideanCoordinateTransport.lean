import FreudenthalSVLean.ChainMeasureTransport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine Euclidean-coordinate transport for the continuous inverse

For the Fourier L2 estimate underlying manuscript Lemma `means`, the
physical coordinate function space carries the usual Pi norm, whereas
Mathlib Fourier analysis uses a Euclidean norm. The fixed coordinate
equivalence preserves actual Lebesgue volume and L2 norms exactly.
The true chain rule preserves every coordinate partial derivative.
No change of norm is silently identified with a measure or derivative
identity, and no Fourier estimate is assumed by this transport module.
-/

open scoped ContDiff
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.EuclideanCoordinateTransport

set_option backward.isDefEq.respectTransparency false

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

def coordinates : EuclideanThree →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap

def euclideanPoint : Space →L[ℝ] EuclideanThree :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

theorem coordinates_euclideanPoint (x : Space) : coordinates (euclideanPoint x) = x := rfl
theorem euclideanPoint_coordinates (x : EuclideanThree) : euclideanPoint (coordinates x) = x := rfl

theorem coordinates_volume : MeasurePreserving coordinates
    (volume : Measure EuclideanThree) (volume : Measure Space) :=
  PiLp.volume_preserving_ofLp (Fin 3)

theorem euclideanPoint_volume : MeasurePreserving euclideanPoint
    (volume : Measure Space) (volume : Measure EuclideanThree) :=
  PiLp.volume_preserving_toLp (Fin 3)

theorem integral_pullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) : (∫ x : EuclideanThree, f (coordinates x)) = ∫ x : Space, f x :=
  coordinates_volume.integral_comp (MeasurableEquiv.toLp 2 Space).symm.measurableEmbedding f

def lpPullback (𝕜 : Type*) [RCLike 𝕜] :
    Lp 𝕜 2 (volume : Measure Space) →ₗᵢ[𝕜] Lp 𝕜 2 (volume : Measure EuclideanThree) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 coordinates coordinates_volume

theorem lpPullback_norm (𝕜 : Type*) [RCLike 𝕜]
    (f : Lp 𝕜 2 (volume : Measure Space)) : ‖lpPullback 𝕜 f‖ = ‖f‖ :=
  (lpPullback 𝕜).norm_map f

theorem contDiff_pullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Space → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x : EuclideanThree => f (coordinates x)) :=
  hf.comp coordinates.contDiff

theorem partial_pullback {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanThree) (i : Fin 3) :
    fderiv ℝ (fun y : EuclideanThree => f (coordinates y)) x (euclideanPoint (Pi.single i 1)) =
      fderiv ℝ f (coordinates x) (Pi.single i 1) := by
  have hd : HasFDerivAt (fun y : EuclideanThree => f (coordinates y))
      ((fderiv ℝ f (coordinates x)).comp coordinates) x :=
    ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x coordinates.hasFDerivAt
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, coordinates_euclideanPoint]

end FreudenthalSVLean.EuclideanCoordinateTransport
