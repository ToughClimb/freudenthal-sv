import FreudenthalSVLean.H1ZeroLinearity
import FreudenthalSVLean.BoundaryBoxH1Estimate
import FreudenthalSVLean.CubeZeroMeanL2
import FreudenthalSVLean.H1ApproximationL2

/-!
# Genuine weak H1_0 gradients have cube support and zero total integral

For the continuous divergence step in manuscript Lemma `means`, every
actual weak derivative of an H1_0 function vanishes almost everywhere
outside the cube. This follows from genuine local L2 convergence of
the C-infinity interior-supported derivatives. Cube volume gives L1
integrability; a proved smooth cutoff tests actual weak integration by
parts and establishes zero integral of every derivative component.
No classical divergence theorem or stipulated boundary identity is used.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.ConformingDivergenceMean
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.BoundaryBoxH1Estimate
open FreudenthalSVLean.CubeZeroMeanL2

noncomputable section

namespace FreudenthalSVLean.WeakH1ZeroGradientSupport

set_option backward.isDefEq.respectTransparency false

theorem inH1ZeroCube_gradient_zero_outside {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) :
    g i =ᵐ[volume.restrict openCubeᶜ] (0 : Space → ℝ) := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hz (n : ℕ) : ((ha.partial_memLp n i).restrict openCubeᶜ).toLp
      (fun x => fderiv ℝ (u n) x (Pi.single i 1)) = 0 := by
    have he : (fun x => fderiv ℝ (u n) x (Pi.single i 1)) =ᵐ[volume.restrict openCubeᶜ]
        (0 : Space → ℝ) := by
      filter_upwards [ae_restrict_mem openCube_isOpen.measurableSet.compl] with x hx
      have hd : fderiv ℝ (u n) x = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun ht => hx ((hu n).2.2.1 ht))
      simp only [hd, zero_apply, Pi.zero_apply]
    have hzero : MemLp (0 : Space → ℝ) 2 (volume.restrict openCubeᶜ) := MemLp.zero
    exact (MemLp.toLp_congr ((ha.partial_memLp n i).restrict openCubeᶜ) hzero he).trans
      (MemLp.toLp_zero hzero)
  have hl := smooth_gradient_local_L2_tendsto ha openCubeᶜ i
  have he : ((hw.2 i).1.restrict openCubeᶜ).toLp (g i) = 0 :=
    tendsto_nhds_unique hl (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp ℝ 2 (volume.restrict openCubeᶜ)))
        atTop (𝓝 0)))
  exact (MemLp.coeFn_toLp ((hw.2 i).1.restrict openCubeᶜ)).symm.trans
    (Lp.eq_zero_iff_ae_eq_zero.mp he)

theorem inH1ZeroCube_gradient_zero_off_cube {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) :
    ∀ᵐ x : Space ∂volume, x ∉ cube → g i x = 0 := by
  have hz := (inH1ZeroCube_gradient_zero_outside hf i).filter_mono
    (ae_mono (Measure.restrict_mono (compl_subset_compl.mpr openCube_subset_cube) le_rfl))
  exact (ae_restrict_iff' (measurableSet_Icc.compl : MeasurableSet cubeᶜ)).mp hz

def maskedGradient (g : Fin 3 → Space → ℝ) (i : Fin 3) : Space → ℝ := cube.indicator (g i)

theorem maskedGradient_ae {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) : g i =ᵐ[volume] maskedGradient g i := by
  filter_upwards [inH1ZeroCube_gradient_zero_off_cube hf i] with x hx
  by_cases hc : x ∈ cube
  · exact (indicator_of_mem hc (g i)).symm
  · rw [maskedGradient, indicator_of_notMem hc]
    exact hx hc

theorem inH1ZeroCube_gradient_integrable {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) : Integrable (g i) := by
  have hi : Integrable (maskedGradient g i) :=
    supported_memLp_integrable ((hf.1.2 i).1.indicator (measurableSet_Icc : MeasurableSet cube))
      (fun x hx => indicator_of_notMem hx (g i))
  exact hi.congr (maskedGradient_ae hf i).symm

theorem inH1ZeroCube_gradient_integral_zero {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (i : Fin 3) : (∫ x, g i x) = 0 := by
  have hw := (hf.1.2 i).2 (cubeCutoff : Space → ℝ) cubeCutoff.contDiff cubeCutoff.hasCompactSupport
  have hgz := inH1ZeroCube_gradient_zero_off_cube hf i
  have hfz : ∀ᵐ x : Space ∂volume, x ∉ cube → f x = 0 :=
    (ae_restrict_iff' (measurableSet_Icc.compl : MeasurableSet cubeᶜ)).mp
      (inH1ZeroCube_zero_on_set hf (compl_subset_compl.mpr openCube_subset_cube))
  have hgprod : (fun x => g i x * cubeCutoff x) =ᵐ[volume] g i := by
    filter_upwards [hgz] with x hx
    by_cases hc : x ∈ cube
    · rw [cubeCutoff_one x hc, mul_one]
    · rw [hx hc, zero_mul]
  have hfprod : (fun x => f x * fderiv ℝ (cubeCutoff : Space → ℝ) x (Pi.single i 1)) =ᵐ[volume]
      (0 : Space → ℝ) := by
    filter_upwards [hfz] with x hx
    by_cases hc : x ∈ cube
    · rw [cubeCutoff_fderiv_zero x hc]
      simp
    · rw [hx hc, zero_mul]
      rfl
  rw [integral_congr_ae hgprod, integral_congr_ae hfprod] at hw
  simpa only [Pi.zero_apply, integral_zero, neg_zero] using hw

end FreudenthalSVLean.WeakH1ZeroGradientSupport
