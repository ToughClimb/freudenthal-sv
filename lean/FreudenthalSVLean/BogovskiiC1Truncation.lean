import FreudenthalSVLean.BogovskiiKernelDifferentiation
import FreudenthalSVLean.C1CubeH1Zero
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual C1 and H1_0 Bogovskii truncations

For manuscript Lemma `means`, a continuous cube-supported input gives
a genuine C1 truncated Bogovskii field. The actual derivative follows
from compact-parameter differentiation, after a positive continuous
time clipping that agrees with the original kernel on the integration
interval. Genuine Fubini identifies the compact product integral with
the original iterated integral. The proved interior support and actual
mollification criterion give H1_0 membership, not merely boundary values.
The uniform gradient estimate and divergence limit are separate results.
-/

open scoped ContDiff BigOperators
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiTruncation
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.CompactParameterDifferentiation
open FreudenthalSVLean.C1CubeH1Zero
open FreudenthalSVLean.ConformingH1Zero

noncomputable section

namespace FreudenthalSVLean.BogovskiiC1Truncation

set_option backward.isDefEq.respectTransparency false

abbrev Parameter := ℝ × Space

def parameterBox (ε : ℝ) : Set Parameter := Icc ε 1 ×ˢ cube

theorem parameterBox_compact (ε : ℝ) : IsCompact (parameterBox ε) :=
  isCompact_Icc.prod isCompact_Icc

def parameterField (ε : ℝ) (f : Space → ℝ) (j : Fin 3) (x : Space) (p : Parameter) : ℝ :=
  kernel (clippedTime ε p.1) x p.2 j * f p.2

def parameterDerivative (ε : ℝ) (f : Space → ℝ) (j : Fin 3) (x : Space)
    (p : Parameter) : Space →L[ℝ] ℝ :=
  f p.2 • kernelDerivative (clippedTime ε p.1) x p.2 j

theorem parameterField_continuous {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (j : Fin 3) : Continuous (parameterField ε f j).uncurry :=
  (clipped_kernel_continuous hε j).mul (hf.comp continuous_snd.snd)

theorem parameterDerivative_continuous {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (j : Fin 3) : Continuous (parameterDerivative ε f j).uncurry :=
  (hf.comp continuous_snd.snd).smul (clipped_derivative_continuous hε j)

theorem parameterField_hasFDerivAt (ε : ℝ) (f : Space → ℝ) (j : Fin 3)
    (p : Parameter) (x : Space) :
    HasFDerivAt (parameterField ε f j · p) (parameterDerivative ε f j x p) x := by
  simpa only [parameterField, parameterDerivative, smul_eq_mul, mul_comm] using!
    (kernel_hasFDerivAt (clippedTime ε p.1) x p.2 j).const_smul (f p.2)

theorem parameter_integral_eq_truncated {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (hs : ∀ y : Space, y ∉ cube → f y = 0) (j : Fin 3) (x : Space) :
    (∫ p in parameterBox ε, parameterField ε f j x p) = truncated ε f j x := by
  have hi : IntegrableOn (parameterField ε f j x) (parameterBox ε) :=
    ((parameterField_continuous hε hf j).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact (parameterBox_compact ε)
  have he : (volume : Measure Parameter).restrict (parameterBox ε) =
      (volume.restrict (Icc ε (1 : ℝ))).prod ((volume : Measure Space).restrict cube) :=
    (Measure.prod_restrict (Icc ε (1 : ℝ)) cube).symm
  change Integrable (parameterField ε f j x) (volume.restrict (parameterBox ε)) at hi
  rw [he] at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 : ℝ)))] with t ht
  change (∫ y in cube, kernel (clippedTime ε t) x y j * f y) = ∫ y : Space, kernel t x y j * f y
  rw [clippedTime_eq ht.1]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hs y hy, mul_zero])

theorem truncated_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (hs : ∀ y : Space, y ∉ cube → f y = 0) (j : Fin 3) (x : Space) :
    HasFDerivAt (truncated ε f j) (∫ p in parameterBox ε, parameterDerivative ε f j x p) x := by
  have he : (fun z : Space => ∫ p in parameterBox ε, parameterField ε f j z p) =
      truncated ε f j := funext (parameter_integral_eq_truncated hε hf hs j)
  rw [← he]
  exact compact_integral_hasFDerivAt (parameterBox ε) (parameterBox_compact ε)
    (parameterField ε f j) (parameterDerivative ε f j) (parameterField_continuous hε hf j)
    (parameterDerivative_continuous hε hf j) (fun p _ x => parameterField_hasFDerivAt ε f j p x) x

theorem truncated_contDiff_one {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (hs : ∀ y : Space, y ∉ cube → f y = 0) (j : Fin 3) :
    ContDiff ℝ 1 (truncated ε f j) := by
  have he : (fun z : Space => ∫ p in parameterBox ε, parameterField ε f j z p) =
      truncated ε f j := funext (parameter_integral_eq_truncated hε hf hs j)
  rw [← he]
  exact compact_integral_contDiff_one (parameterBox ε) (parameterBox_compact ε)
    (parameterField ε f j) (parameterDerivative ε f j) (parameterField_continuous hε hf j)
    (parameterDerivative_continuous hε hf j) (fun p _ x => parameterField_hasFDerivAt ε f j p x)

theorem truncated_partial {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (hs : ∀ y : Space, y ∉ cube → f y = 0) (j i : Fin 3) (x : Space) :
    classicalPartial (truncated ε f j) i x =
      ∫ p in parameterBox ε, (parameterDerivative ε f j x p) (Pi.single i 1) := by
  have hi : IntegrableOn (parameterDerivative ε f j x) (parameterBox ε) :=
    ((parameterDerivative_continuous hε hf j).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact (parameterBox_compact ε)
  rw [classicalPartial, (truncated_hasFDerivAt hε hf hs j x).fderiv]
  exact ContinuousLinearMap.integral_apply hi (Pi.single i 1)

theorem truncated_inH1ZeroCube {ε : ℝ} (hε : 0 < ε) {f : Space → ℝ}
    (hf : Continuous f) (hs : ∀ y : Space, y ∉ cube → f y = 0) (j : Fin 3) :
    InH1ZeroCube (truncated ε f j) (classicalPartial (truncated ε f j)) :=
  C1_cube_inH1ZeroCube (truncated_contDiff_one hε hf hs j)
    (truncated_hasCompactSupport hε f hs j)
    ((truncated_support_box hε f hs j).trans
      ((interiorBox_subset_openCube hε).trans openCube_subset_cube))

end FreudenthalSVLean.BogovskiiC1Truncation
