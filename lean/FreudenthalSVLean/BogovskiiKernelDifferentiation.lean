import FreudenthalSVLean.BogovskiiTruncation
import FreudenthalSVLean.CompactParameterDifferentiation

/-!
# Actual spatial derivative of the truncated cube kernel

For the continuous lifting in manuscript Lemma `means`, the Bogovskii
kernel has the genuine Frechet derivative obtained by the product and
chain rules. A positive continuous time clipping agrees with time on
the truncation interval and makes the joint kernel and actual derivative
continuous on the whole compact parameter domain. No derivative with
respect to the clipping parameter is claimed or needed.
-/

open scoped ContDiff
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiTruncation

noncomputable section

namespace FreudenthalSVLean.BogovskiiKernelDifferentiation

set_option backward.isDefEq.respectTransparency false

def kernelDerivative (t : ℝ) (x y : Space) (j : Fin 3) : Space →L[ℝ] ℝ :=
  ((x j - y j) / t ^ 4) •
    ((fderiv ℝ rho (kernelArgument t x y)).comp (t⁻¹ • ContinuousLinearMap.id ℝ Space)) +
  rho (kernelArgument t x y) • ((t ^ 4)⁻¹ • ContinuousLinearMap.proj j)

theorem kernelArgument_hasFDerivAt (t : ℝ) (x y : Space) :
    HasFDerivAt (fun z : Space => kernelArgument t z y)
      (t⁻¹ • ContinuousLinearMap.id ℝ Space) x := by
  have h := (hasFDerivAt_const (𝕜 := ℝ) y x).add
    (((hasFDerivAt_id (𝕜 := ℝ) x).sub (hasFDerivAt_const (𝕜 := ℝ) y x)).const_smul (t⁻¹ : ℝ))
  simpa only [kernelArgument, zero_sub, add_zero, sub_zero, zero_add] using! h

theorem kernel_hasFDerivAt (t : ℝ) (x y : Space) (j : Fin 3) :
    HasFDerivAt (fun z : Space => kernel t z y j) (kernelDerivative t x y j) x := by
  have hcoord : HasFDerivAt (fun z : Space => (z j - y j) / t ^ 4)
      ((t ^ 4)⁻¹ • (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ)) x := by
    convert! ((ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).hasFDerivAt.sub
      (hasFDerivAt_const (𝕜 := ℝ) (y j) x)).const_smul ((t ^ 4)⁻¹ : ℝ) using 1
    · funext z
      simp only [Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul, div_eq_mul_inv]
      ring
    · simp only [sub_zero]
  have hrho : HasFDerivAt (fun z : Space => rho (kernelArgument t z y))
      ((fderiv ℝ rho (kernelArgument t x y)).comp (t⁻¹ • ContinuousLinearMap.id ℝ Space)) x := by
    simpa only [Function.comp_def] using!
      ((rho_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
        (kernelArgument_hasFDerivAt t x y)
  simpa only [kernel, kernelDerivative] using! hcoord.fun_mul hrho

def clippedTime (ε t : ℝ) : ℝ := max ε t

theorem clippedTime_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < clippedTime ε t :=
  hε.trans_le (le_max_left ε t)

theorem clippedTime_eq {ε t : ℝ} (ht : ε ≤ t) : clippedTime ε t = t := max_eq_right ht

theorem clipped_argument_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : Space × (ℝ × Space) =>
      kernelArgument (clippedTime ε p.2.1) p.1 p.2.2) := by
  have ht : Continuous (fun p : Space × (ℝ × Space) => clippedTime ε p.2.1) := by
    unfold clippedTime
    fun_prop
  have hinv := ht.inv₀ (fun p => (clippedTime_pos hε p.2.1).ne')
  exact continuous_snd.snd.add (hinv.smul (continuous_fst.sub continuous_snd.snd))

theorem clipped_kernel_continuous {ε : ℝ} (hε : 0 < ε) (j : Fin 3) :
    Continuous (fun p : Space × (ℝ × Space) =>
      kernel (clippedTime ε p.2.1) p.1 p.2.2 j) := by
  have ht : Continuous (fun p : Space × (ℝ × Space) => clippedTime ε p.2.1) := by
    unfold clippedTime
    fun_prop
  have hnum : Continuous (fun p : Space × (ℝ × Space) => p.1 j - p.2.2 j) := by fun_prop
  have hc : Continuous (fun p : Space × (ℝ × Space) =>
      (p.1 j - p.2.2 j) / (clippedTime ε p.2.1) ^ 4) :=
    hnum.div (ht.pow 4) (fun p => pow_ne_zero 4 (clippedTime_pos hε p.2.1).ne')
  exact hc.mul (rho_contDiff.continuous.comp (clipped_argument_continuous hε))

theorem clipped_derivative_continuous {ε : ℝ} (hε : 0 < ε) (j : Fin 3) :
    Continuous (fun p : Space × (ℝ × Space) =>
      kernelDerivative (clippedTime ε p.2.1) p.1 p.2.2 j) := by
  have ht : Continuous (fun p : Space × (ℝ × Space) => clippedTime ε p.2.1) := by
    unfold clippedTime
    fun_prop
  have hinv := ht.inv₀ (fun p => (clippedTime_pos hε p.2.1).ne')
  have hinv4 := (ht.pow 4).inv₀ (fun p => pow_ne_zero 4 (clippedTime_pos hε p.2.1).ne')
  have harg := clipped_argument_continuous hε
  have hnum : Continuous (fun p : Space × (ℝ × Space) => p.1 j - p.2.2 j) := by fun_prop
  have hc : Continuous (fun p : Space × (ℝ × Space) =>
      (p.1 j - p.2.2 j) / (clippedTime ε p.2.1) ^ 4) :=
    hnum.div (ht.pow 4) (fun p => pow_ne_zero 4 (clippedTime_pos hε p.2.1).ne')
  have hd := (rho_contDiff.continuous_fderiv (by simp)).comp harg
  unfold kernelDerivative
  exact (hc.smul (hd.clm_comp (hinv.smul continuous_const))).add
    ((rho_contDiff.continuous.comp harg).smul (hinv4.smul continuous_const))

end FreudenthalSVLean.BogovskiiKernelDifferentiation
