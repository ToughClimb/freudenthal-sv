import FreudenthalSVLean.BogovskiiKernelDifferentiation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Genuine time derivative of the Bogovskii mass kernel

For the continuous lifting in manuscript Lemma `means`, the sum of
the three actual spatial diagonal kernel derivatives equals minus the
true time derivative of t^(-3) rho(y+(x-y)/t). The coordinate identity
is proved for every continuous linear functional, and the actual time
derivative follows by the ordinary inverse, product and chain rules.
This is the kernel identity underlying the divergence/FTC computation.
-/

open scoped ContDiff BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiKernelDifferentiation

noncomputable section

namespace FreudenthalSVLean.BogovskiiKernelDivergence

set_option backward.isDefEq.respectTransparency false

theorem coordinate_functional_sum (L : Space →L[ℝ] ℝ) (v : Space) :
    (∑ j : Fin 3, v j * L (Pi.single j 1)) = L v := by
  have hv : (∑ j : Fin 3, v j • (Pi.single j 1 : Space)) = v := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have he := congrArg L hv
  simpa only [map_sum, map_smul, smul_eq_mul] using he

def massKernel (t : ℝ) (x y : Space) : ℝ := (t ^ 3)⁻¹ * rho (kernelArgument t x y)

def diagonalKernel (t : ℝ) (x y : Space) : ℝ :=
  ∑ j : Fin 3, kernelDerivative t x y j (Pi.single j 1)

theorem diagonalKernel_formula (t : ℝ) (x y : Space) :
    diagonalKernel t x y = (t ^ 4)⁻¹ *
      (3 * rho (kernelArgument t x y) + t⁻¹ * fderiv ℝ rho (kernelArgument t x y) (x - y)) := by
  have he (j : Fin 3) : kernelDerivative t x y j (Pi.single j 1) =
      ((t ^ 4)⁻¹ * t⁻¹) * ((x j - y j) * fderiv ℝ rho (kernelArgument t x y) (Pi.single j 1)) +
        (t ^ 4)⁻¹ * rho (kernelArgument t x y) := by
    simp only [kernelDerivative, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul, div_eq_mul_inv, mul_one]
    ring
  unfold diagonalKernel
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum := coordinate_functional_sum (fderiv ℝ rho (kernelArgument t x y)) (x - y)
  simp only [Pi.sub_apply] at hsum
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem kernelArgument_hasDerivAt_time {t : ℝ} (ht : t ≠ 0) (x y : Space) :
    HasDerivAt (fun s : ℝ => kernelArgument s x y) (-(t ^ 2)⁻¹ • (x - y)) t := by
  simpa only [kernelArgument, zero_add] using!
    (hasDerivAt_const (𝕜 := ℝ) t y).add ((hasDerivAt_inv ht).smul_const (x - y))

theorem massKernel_hasDerivAt {t : ℝ} (ht : t ≠ 0) (x y : Space) :
    HasDerivAt (fun s : ℝ => massKernel s x y) (-diagonalKernel t x y) t := by
  have hi := ((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 ht)
  have hr := ((rho_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    (kernelArgument_hasDerivAt_time ht x y)
  convert! hi.fun_mul hr using 1
  rw [diagonalKernel_formula]
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul, id_eq, Pi.pow_apply,
    Function.comp_apply, Pi.inv_apply]
  field_simp
  ring

end FreudenthalSVLean.BogovskiiKernelDivergence
