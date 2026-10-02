import FreudenthalSVLean.BogovskiiTimeFTC
import FreudenthalSVLean.BogovskiiC1Truncation

/-!
# Genuine divergence identity for Bogovskii truncations

For the continuous lifting in manuscript Lemma `means`, the actual
classical divergence of the genuine C1 truncated vector field equals
the affine mass mixture minus rho(x) times the actual input mean.
Every derivative, finite sum, compact-product integral and Fubini exchange
is genuine. The endpoint formula uses the proved mass-kernel time FTC.
The zero-mean compatibility follows by cancellation, not an imported lemma.
-/

open scoped ContDiff BigOperators
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.BogovskiiTruncation
open FreudenthalSVLean.BogovskiiKernelDifferentiation
open FreudenthalSVLean.BogovskiiKernelDivergence
open FreudenthalSVLean.BogovskiiTimeFTC
open FreudenthalSVLean.BogovskiiC1Truncation
open FreudenthalSVLean.C1CubeH1Zero

noncomputable section

namespace FreudenthalSVLean.BogovskiiDivergenceIdentity

set_option backward.isDefEq.respectTransparency false

def smoothedPressure (t : ℝ) (q : Space → ℝ) (x : Space) : ℝ :=
  ∫ y : Space, massKernel t x y * q y

theorem clipped_diagonal_parameter_continuous {ε : ℝ} (hε : 0 < ε) (x : Space) :
    Continuous (fun p : ℝ × Space => diagonalKernel (clippedTime ε p.1) x p.2) := by
  unfold diagonalKernel
  apply continuous_finsetSum
  intro j _
  exact (((clipped_derivative_continuous hε j).comp
    (continuous_const.prodMk continuous_id)).clm_apply continuous_const)

theorem parameter_diagonal_sum (ε : ℝ) (q : Space → ℝ) (x : Space) (p : ℝ × Space) :
    (∑ j : Fin 3, parameterDerivative ε q j x p (Pi.single j 1)) =
      q p.2 * diagonalKernel (clippedTime ε p.1) x p.2 := by
  simp only [parameterDerivative, smul_apply, smul_eq_mul, diagonalKernel, Finset.mul_sum]

theorem truncated_divergence {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {q : Space → ℝ} (hq : Continuous q) (hs : ∀ y : Space, y ∉ cube → q y = 0) (x : Space) :
    (∑ j : Fin 3, classicalPartial (truncated ε q j) j x) =
      smoothedPressure ε q x - rho x * ∫ y : Space, q y := by
  have hi (j : Fin 3) : IntegrableOn
      (fun p : ℝ × Space => parameterDerivative ε q j x p (Pi.single j 1)) (parameterBox ε) :=
    (((parameterDerivative_continuous hε hq j).comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const).continuousOn.integrableOn_compact
        (parameterBox_compact ε)
  have hc : Continuous (fun p : ℝ × Space => q p.2 * diagonalKernel (clippedTime ε p.1) x p.2) :=
    (hq.comp continuous_snd).mul (clipped_diagonal_parameter_continuous hε x)
  have hic : IntegrableOn (fun p : ℝ × Space => q p.2 * diagonalKernel (clippedTime ε p.1) x p.2)
      (parameterBox ε) := hc.continuousOn.integrableOn_compact (parameterBox_compact ε)
  have hprod : (volume : Measure (ℝ × Space)).restrict (parameterBox ε) =
      (volume.restrict (Icc ε (1 : ℝ))).prod ((volume : Measure Space).restrict cube) :=
    (Measure.prod_restrict (Icc ε (1 : ℝ)) cube).symm
  have hm : Continuous (fun y : Space => massKernel ε x y * q y) := by
    unfold massKernel kernelArgument
    exact (continuous_const.mul (rho_contDiff.continuous.comp (by fun_prop))).mul hq
  have him : IntegrableOn (fun y : Space => massKernel ε x y * q y) cube :=
    hm.continuousOn.integrableOn_compact isCompact_Icc
  have hiq : IntegrableOn q cube := hq.continuousOn.integrableOn_compact isCompact_Icc
  calc
    _ = ∑ j : Fin 3, ∫ p in parameterBox ε, parameterDerivative ε q j x p (Pi.single j 1) :=
      Finset.sum_congr rfl (fun j _ => truncated_partial hε hq hs j j x)
    _ = ∫ p in parameterBox ε, ∑ j : Fin 3, parameterDerivative ε q j x p (Pi.single j 1) :=
      (integral_finsetSum Finset.univ (fun j _ => hi j)).symm
    _ = ∫ p in parameterBox ε, q p.2 * diagonalKernel (clippedTime ε p.1) x p.2 :=
      integral_congr_ae (Eventually.of_forall (parameter_diagonal_sum ε q x))
    _ = ∫ y in cube, ∫ t in Icc ε (1 : ℝ), q y * diagonalKernel (clippedTime ε t) x y := by
      change Integrable _ (volume.restrict (parameterBox ε)) at hic
      rw [hprod] at hic ⊢
      exact integral_prod_symm _ hic
    _ = ∫ y in cube, q y * (massKernel ε x y - rho x) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_const_mul, diagonal_kernel_integral hε hε1]
    _ = (∫ y in cube, massKernel ε x y * q y) - rho x * ∫ y in cube, q y := by
      calc
        _ = ∫ y in cube, massKernel ε x y * q y - rho x * q y :=
          integral_congr_ae (Eventually.of_forall (fun y => by ring))
        _ = _ := by
          rw [integral_sub him (hiq.const_mul _), integral_const_mul]
    _ = _ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hs y hy, mul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero hs]
      rfl

theorem truncated_divergence_mean_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {q : Space → ℝ} (hq : Continuous q) (hs : ∀ y : Space, y ∉ cube → q y = 0)
    (hmean : (∫ y : Space, q y) = 0) (x : Space) :
    (∑ j : Fin 3, classicalPartial (truncated ε q j) j x) = smoothedPressure ε q x := by
  rw [truncated_divergence hε hε1 hq hs, hmean, mul_zero, sub_zero]

end FreudenthalSVLean.BogovskiiDivergenceIdentity
