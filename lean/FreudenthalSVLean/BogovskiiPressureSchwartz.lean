import FreudenthalSVLean.BogovskiiSchwartzKernels
import FreudenthalSVLean.EuclideanCubeTransport

/-!
# Actual smooth pressure and moment data for the Fourier lifting

For the continuous lift in manuscript Lemma `means`, every genuine
smooth compactly supported cube input gives its actual complex
Euclidean Schwartz function and three coordinate moments. Their true
support is proved from cube geometry; the input's genuine L2 energy is
preserved exactly, and each moment has no larger actual L2 energy.
The fixed central bump and moment kernels satisfy the same cube-support
hypotheses required by the scalar estimate.
-/

open scoped ContDiff SchwartzMap
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.EuclideanCoordinateTransport
open FreudenthalSVLean.CubeSupportedMixtures
open FreudenthalSVLean.BogovskiiSchwartzKernels

noncomputable section

namespace FreudenthalSVLean.BogovskiiPressureSchwartz

set_option backward.isDefEq.respectTransparency false

abbrev E := EuclideanThree

def pressureComplex (q : Space → ℝ) : E → ℂ := fun x => (q (coordinates x) : ℂ)

theorem pressureComplex_contDiff {q : Space → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (pressureComplex q) := Complex.ofRealCLM.contDiff.comp (contDiff_pullback hq)

theorem pressureComplex_compact {q : Space → ℝ} (hq : HasCompactSupport q) :
    HasCompactSupport (pressureComplex q) :=
  (hq.comp_homeomorph (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph).comp_left
    (by simp : Complex.ofReal (0 : ℝ) = 0)

def pressureSchwartz (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) : 𝓢(E, ℂ) :=
  (pressureComplex_compact hc).toSchwartzMap (pressureComplex_contDiff hd)

theorem pressureSchwartz_apply (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) (x : E) :
    pressureSchwartz q hd hc x = (q (coordinates x) : ℂ) := rfl

theorem pressureSchwartz_support (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : Function.support q ⊆ cube) : Function.support (⇑(pressureSchwartz q hd hc)) ⊆ cubeE := by
  intro x hx
  by_contra hn
  have hz := Function.notMem_support.mp (fun h => hn (hs h))
  apply hx
  rw [pressureSchwartz_apply, hz]
  simp

def momentInput (q : Space → ℝ) (j : Fin 3) : E → ℂ :=
  fun x => ((coordinates x) j : ℂ) * pressureComplex q x

theorem momentInput_contDiff {q : Space → ℝ} (hd : ContDiff ℝ ∞ q) (j : Fin 3) :
    ContDiff ℝ ∞ (momentInput q j) :=
  (Complex.ofRealCLM.contDiff.comp
    ((ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).contDiff.comp coordinates.contDiff)).mul
    (pressureComplex_contDiff hd)

theorem momentInput_compact {q : Space → ℝ} (hc : HasCompactSupport q) (j : Fin 3) :
    HasCompactSupport (momentInput q j) := (pressureComplex_compact hc).mul_left

def momentInputSchwartz (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (j : Fin 3) : 𝓢(E, ℂ) := (momentInput_compact hc j).toSchwartzMap (momentInput_contDiff hd j)

theorem momentInputSchwartz_apply (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (j : Fin 3) (x : E) :
    momentInputSchwartz q hd hc j x = ((coordinates x) j * q (coordinates x) : ℝ) :=
  (Complex.ofReal_mul _ _).symm

theorem momentInputSchwartz_support (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : Function.support q ⊆ cube) (j : Fin 3) :
    Function.support (⇑(momentInputSchwartz q hd hc j)) ⊆ cubeE := by
  intro x hx
  by_contra hn
  apply hx
  rw [momentInputSchwartz_apply, Function.notMem_support.mp (fun h => hn (hs h)), mul_zero]
  simp

theorem pressureSchwartz_L2_energy (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q) :
    (∫ x : E, ‖pressureSchwartz q hd hc x‖ ^ 2) = ∫ x : Space, q x ^ 2 := by
  calc
    _ = ∫ x : E, q (coordinates x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [pressureSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = _ := integral_pullback (fun x => q x ^ 2)

theorem momentInputSchwartz_L2_energy (q : Space → ℝ) (hd : ContDiff ℝ ∞ q) (hc : HasCompactSupport q)
    (hs : Function.support q ⊆ cube) (j : Fin 3) :
    (∫ x : E, ‖momentInputSchwartz q hd hc j x‖ ^ 2) ≤ ∫ x : Space, q x ^ 2 := by
  have hpoint (x : E) : ‖momentInputSchwartz q hd hc j x‖ ≤ ‖pressureSchwartz q hd hc x‖ := by
    by_cases hx : coordinates x ∈ cube
    · rw [momentInputSchwartz_apply, pressureSchwartz_apply, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hx0 : 0 ≤ (coordinates x) j := hx.1 j
      have hx1 : (coordinates x) j ≤ 1 := hx.2 j
      have ha : |(coordinates x) j| ≤ 1 := abs_le.mpr ⟨by linarith, hx1⟩
      exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans_eq (one_mul _)
    · rw [momentInputSchwartz_apply, pressureSchwartz_apply,
        Function.notMem_support.mp (fun h => hx (hs h)), mul_zero]
  rw [← pressureSchwartz_L2_energy q hd hc]
  let hm := momentInputSchwartz q hd hc j
  let hp := pressureSchwartz q hd hc
  apply integral_mono
    ((memLp_two_iff_integrable_sq_norm hm.continuous.aestronglyMeasurable).mp (hm.memLp (μ := volume) 2))
    ((memLp_two_iff_integrable_sq_norm hp.continuous.aestronglyMeasurable).mp (hp.memLp (μ := volume) 2))
  intro x
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hpoint x)

theorem rhoSchwartz_support : Function.support (rhoSchwartz : E → ℂ) ⊆ cubeE := by
  intro x hx
  by_contra hn
  apply hx
  rw [rhoSchwartz_apply, Function.notMem_support.mp
    (fun h => hn ((rho_tsupport_interior.trans openCube_subset_cube) (subset_tsupport rho h)))]
  simp

theorem momentSchwartz_support (j : Fin 3) :
    Function.support (⇑(momentSchwartz j)) ⊆ cubeE := by
  intro x hx
  by_contra hn
  apply hx
  rw [momentSchwartz_apply, Function.notMem_support.mp
    (fun h => hn ((rho_tsupport_interior.trans openCube_subset_cube) (subset_tsupport rho h))), mul_zero]
  simp

end FreudenthalSVLean.BogovskiiPressureSchwartz
