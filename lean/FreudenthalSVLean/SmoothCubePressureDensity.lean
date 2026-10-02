import FreudenthalSVLean.SmoothCubePressureSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Genuine density of smooth mean-zero cube pressures

For the continuous lifting in manuscript Lemma `means`, the actual
smooth pressure class range is dense in the complete zero-mean cube L2
Hilbert space. Orthogonality to its explicit mean-corrected interior tests
makes an actual L2 representative constant on the open cube by the proved
fundamental lemma for smooth tests. The cube boundary has zero measure,
and the true zero mean forces that constant to vanish. Hilbert orthogonal
projection then proves density; no smooth-density axiom is assumed.
-/

open scoped ContDiff Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.BogovskiiCubeGeometry
open FreudenthalSVLean.SmoothCubePressureSpace

noncomputable section

namespace FreudenthalSVLean.SmoothCubePressureDensity

set_option backward.isDefEq.respectTransparency false

theorem pressureClass_pairing (q r : cubePressureFunctions) :
    inner ℝ (pressureClass q) (pressureClass r) = ∫ x : Space, q.val x * r.val x := by
  change inner ℝ (q.property.1.toLp q.val) (r.property.1.toLp r.val) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [q.property.1.coeFn_toLp, r.property.1.coeFn_toLp] with x hx hy
  rw [hx, hy, Real.inner_apply]

theorem openCube_ae_cube : openCube =ᵐ[(volume : Measure Space)] cube :=
  Measure.univ_pi_Ioo_ae_eq_Icc

theorem cube_volume : (volume : Measure Space) cube = 1 := by
  simp only [cube, Real.volume_Icc_pi, Pi.one_apply, Pi.zero_apply, sub_zero,
    ENNReal.ofReal_one, Finset.prod_const_one]

theorem smoothPressureRange_orthogonal_eq_bot : smoothPressureRangeᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  obtain ⟨q, rfl⟩ := pressureClass_surjective y
  let c : ℝ := ∫ x : Space, rho x * q.val x
  have hr2 : MemLp rho 2 volume := rho_contDiff.continuous.memLp_of_hasCompactSupport rho_compact
  have hiρ : Integrable (fun x : Space => rho x * q.val x) := hr2.integrable_mul q.property.1
  have ht (φ : Space → ℝ) (hd : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ openCube) : (∫ x : Space, φ x * (q.val x - c)) = 0 := by
    have hm : smoothPressureClass (smoothTestPressure φ hd hc hs) ∈ smoothPressureRange :=
      LinearMap.mem_range.mpr ⟨smoothTestPressure φ hd hc hs, rfl⟩
    have he := (smoothPressureRange.mem_orthogonal _).mp hy _ hm
    change inner ℝ (pressureClass (testPressure φ hd hc hs)) (pressureClass q) = 0 at he
    rw [pressureClass_pairing] at he
    have hφ2 : MemLp φ 2 volume := hd.continuous.memLp_of_hasCompactSupport hc
    have hiφ : Integrable φ := hd.continuous.integrable_of_hasCompactSupport hc
    have hip : Integrable (fun x : Space => φ x * q.val x) := hφ2.integrable_mul q.property.1
    have he' : (∫ x : Space, φ x * q.val x) - (∫ x : Space, φ x) * c = 0 := by
      calc
        _ = ∫ x : Space, φ x * q.val x - (∫ z : Space, φ z) * (rho x * q.val x) := by
          rw [integral_sub hip (hiρ.const_mul _), integral_const_mul]
        _ = ∫ x : Space, (testPressure φ hd hc hs).val x * q.val x := by
          apply integral_congr_ae
          filter_upwards with x
          change _ = (φ x - (∫ z : Space, φ z) * rho x) * q.val x
          ring
        _ = 0 := he
    calc
      _ = ∫ x : Space, φ x * q.val x - c * φ x :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = (∫ x : Space, φ x * q.val x) - c * ∫ x : Space, φ x := by
        rw [integral_sub hip (hiφ.const_mul _), integral_const_mul]
      _ = 0 := by rw [mul_comm c]; exact he'
  have hloc : LocallyIntegrable (fun x : Space => q.val x - c) volume :=
    (q.property.1.locallyIntegrable (by norm_num)).sub continuous_const.locallyIntegrable
  have ho : ∀ᵐ x : Space ∂volume, x ∈ openCube → q.val x = c := by
    have he := openCube_isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hloc.locallyIntegrableOn openCube)
      (fun φ hd hc hs => by simpa only [smul_eq_mul] using! ht φ hd hc hs)
    filter_upwards [he] with x hx
    exact fun h => sub_eq_zero.mp (hx h)
  have hae : q.val =ᵐ[volume] cube.indicator (fun _ : Space => c) := by
    filter_upwards [ho, openCube_ae_cube] with x hx hsets
    by_cases hc : x ∈ cube
    · rw [indicator_of_mem hc]
      exact hx (hsets.mpr hc)
    · rw [q.property.2.1 x hc, indicator_of_notMem hc]
  have hc0 : c = 0 := by
    have he := integral_congr_ae hae
    rw [q.property.2.2, integral_indicator (show MeasurableSet cube from measurableSet_Icc),
      integral_const, measureReal_def, Measure.restrict_apply_univ, cube_volume,
      ENNReal.toReal_one, smul_eq_mul, one_mul] at he
    exact he.symm
  apply Subtype.ext
  change q.property.1.toLp q.val = 0
  calc
    _ = (MemLp.zero : MemLp (0 : Space → ℝ) 2 volume).toLp 0 :=
      MemLp.toLp_congr _ _ (by simpa only [hc0, indicator_zero, Pi.zero_apply] using! hae)
    _ = 0 := MemLp.toLp_zero _

theorem smoothPressureRange_closure_eq_top : smoothPressureRange.topologicalClosure = ⊤ := by
  let : CompleteSpace smoothPressureRange.topologicalClosure :=
    smoothPressureRange.isClosed_topologicalClosure.completeSpace_coe
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, smoothPressureRange_orthogonal_eq_bot]

theorem smoothPressureClass_denseRange : DenseRange smoothPressureClass := by
  rw [DenseRange, ← LinearMap.coe_range, dense_iff_closure_eq,
    ← Submodule.topologicalClosure_coe]
  change (smoothPressureRange.topologicalClosure : Set pressureHilbert) = univ
  rw [smoothPressureRange_closure_eq_top]
  rfl

end FreudenthalSVLean.SmoothCubePressureDensity
