import FreudenthalSVLean.CubePressureHilbert
import FreudenthalSVLean.BogovskiiCubeGeometry

/-!
# Actual smooth zero-mean cube pressure data

For the continuous lifting in manuscript Lemma `means`, this is the
actual linear space of smooth compactly supported cube L2 pressures,
and its genuine map into the closed mean-zero pressure Hilbert space.
Every smooth compactly supported interior test is projected into this
space by subtracting its true mean times the fixed normalized central
bump. All support, smoothness, L2 and mean identities are proved.
-/

open scoped ContDiff
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.BogovskiiCubeGeometry

noncomputable section

namespace FreudenthalSVLean.SmoothCubePressureSpace

set_option backward.isDefEq.respectTransparency false

def smoothPressureSpace : Submodule ℝ cubePressureFunctions where
  carrier := {q | ContDiff ℝ ∞ q.val ∧ HasCompactSupport q.val}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := by
    intro q r hq hr
    exact ⟨hq.1.add hr.1, hq.2.add hr.2⟩
  smul_mem' := by
    intro c q hq
    exact ⟨hq.1.const_smul c, hq.2.smul_left⟩

def smoothPressureClass : smoothPressureSpace →ₗ[ℝ] pressureHilbert :=
  pressureClass.comp smoothPressureSpace.subtype

def smoothPressureRange : Submodule ℝ pressureHilbert := LinearMap.range smoothPressureClass

def meanCorrectedTest (φ : Space → ℝ) (x : Space) : ℝ :=
  φ x - (∫ y : Space, φ y) * rho x

theorem meanCorrectedTest_contDiff {φ : Space → ℝ} (hd : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (meanCorrectedTest φ) := by
  simpa only [smul_eq_mul] using! hd.sub (rho_contDiff.const_smul (∫ y : Space, φ y))

theorem meanCorrectedTest_compact {φ : Space → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (meanCorrectedTest φ) := hc.sub rho_compact.mul_left

theorem meanCorrectedTest_zero {φ : Space → ℝ} (hs : tsupport φ ⊆ openCube)
    {x : Space} (hx : x ∉ cube) : meanCorrectedTest φ x = 0 := by
  rw [meanCorrectedTest, Function.notMem_support.mp
    (fun h => hx (openCube_subset_cube (hs (subset_tsupport φ h)))),
    Function.notMem_support.mp
      (fun h => hx (openCube_subset_cube (rho_tsupport_interior (subset_tsupport rho h))))]
  ring

theorem meanCorrectedTest_mean {φ : Space → ℝ} (hd : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x : Space, meanCorrectedTest φ x) = 0 := by
  have hi : Integrable φ := hd.continuous.integrable_of_hasCompactSupport hc
  have hr : Integrable rho := rho_contDiff.continuous.integrable_of_hasCompactSupport rho_compact
  change (∫ x : Space, φ x - (∫ y : Space, φ y) * rho x) = 0
  rw [integral_sub hi (hr.const_mul _), integral_const_mul, rho_integral]
  ring

def testPressure (φ : Space → ℝ) (hd : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ openCube) : cubePressureFunctions :=
  ⟨meanCorrectedTest φ,
    (meanCorrectedTest_contDiff hd).continuous.memLp_of_hasCompactSupport (meanCorrectedTest_compact hc),
    (fun _ hx => meanCorrectedTest_zero hs hx), meanCorrectedTest_mean hd hc⟩

def smoothTestPressure (φ : Space → ℝ) (hd : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ openCube) : smoothPressureSpace := by
  refine ⟨testPressure φ hd hc hs, ?_⟩
  change ContDiff ℝ ∞ (meanCorrectedTest φ) ∧ HasCompactSupport (meanCorrectedTest φ)
  exact ⟨meanCorrectedTest_contDiff hd, meanCorrectedTest_compact hc⟩

theorem smoothTestPressure_apply (φ : Space → ℝ) (hd : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ openCube) (x : Space) :
    (smoothTestPressure φ hd hc hs).val.val x = meanCorrectedTest φ x := rfl

end FreudenthalSVLean.SmoothCubePressureSpace
