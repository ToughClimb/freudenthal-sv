import FreudenthalSVLean.BogovskiiKernelDivergence

/-!
# Actual time FTC for the truncated Bogovskii kernel

For the continuous lifting in manuscript Lemma `means`, integrate the
proved genuine time derivative of the mass kernel on epsilon<=t<=1.
The diagonal spatial kernel is genuinely integrable on this interval:
positive continuous clipping gives a continuous global representative
that equals the actual integrand on the interval. The true FTC yields
the two endpoint mass kernels, including the exact endpoint rho(x).
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.BogovskiiKernelDivergence

noncomputable section

namespace FreudenthalSVLean.BogovskiiTimeFTC

set_option backward.isDefEq.respectTransparency false

theorem clipped_diagonal_continuous {ε : ℝ} (hε : 0 < ε) (x y : Space) :
    Continuous (fun t : ℝ => diagonalKernel (clippedTime ε t) x y) := by
  unfold diagonalKernel
  apply continuous_finsetSum
  intro j _
  exact (((clipped_derivative_continuous hε j).comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))).clm_apply continuous_const)

theorem massKernel_one (x y : Space) : massKernel 1 x y = rho x := by
  have he : kernelArgument 1 x y = x := by
    funext i
    change y i + (1 : ℝ)⁻¹ * (x i - y i) = x i
    ring
  simp only [massKernel, one_pow, inv_one, he, one_mul]

theorem diagonal_kernel_integral {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Space) :
    (∫ t in Icc ε (1 : ℝ), diagonalKernel (clippedTime ε t) x y) =
      massKernel ε x y - rho x := by
  have hd : ∀ t ∈ uIcc ε (1 : ℝ),
      HasDerivAt (fun s : ℝ => massKernel s x y) (-diagonalKernel (clippedTime ε t) x y) t := by
    intro t ht
    rw [uIcc_of_le hε1] at ht
    rw [clippedTime_eq ht.1]
    exact massKernel_hasDerivAt (hε.trans_le ht.1).ne' x y
  have hi := ((clipped_diagonal_continuous hε x y).neg).intervalIntegrable
    (μ := (volume : Measure ℝ)) ε 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hε1,
    ← integral_Icc_eq_integral_Ioc, massKernel_one] at he
  linarith

end FreudenthalSVLean.BogovskiiTimeFTC
