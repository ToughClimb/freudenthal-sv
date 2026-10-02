import FreudenthalSVLean.H1ApproximationL2

/-!
# Weak-H1 face bounds and genuine element flux identities

For manuscript Lemma `means`, the proved smooth face estimate and Gauss
identity pass to actual weak H1 functions through their genuine smooth
approximations.  L2 convergence and a proved continuous integral functional
give the true volume mean as the sum of face-trace fluxes.  The explicit
trace estimate retains the correct powers of h and the constant six.
For the H1_0 closure criterion, traces vanish on faces lying outside the
open cube.  No continuous divergence inverse or stable interpolant is
assumed or established by this module.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.ScaledSmoothCalculus
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.ConformingDivergenceMean
open FreudenthalSVLean.ConformingVelocityFunction

noncomputable section

namespace FreudenthalSVLean.WeakFaceGauss

set_option backward.isDefEq.respectTransparency false

def l2Integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (hμ : μ univ ≠ ⊤) :
    Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (indicatorConstLp 2 MeasurableSet.univ hμ (1 : ℝ))

theorem l2Integral_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (hμ : μ univ ≠ ⊤) (F : Lp ℝ 2 μ) : l2Integral μ hμ F = ∫ x, F x ∂μ := by
  rw [l2Integral, innerSL_apply_apply, L2.inner_indicatorConstLp_one, setIntegral_univ]

theorem l2Integral_toLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (hμ : μ univ ≠ ⊤) {f : α → ℝ} (hf : MemLp f 2 μ) :
    l2Integral μ hμ (hf.toLp f) = ∫ x, f x ∂μ := by
  rw [l2Integral_eq]
  exact integral_congr_ae (MemLp.coeFn_toLp hf)

theorem faceMeasure_finite : ((volume : Measure FacePoint).restrict (triangleSet 1)) univ ≠ ⊤ := by
  simpa only [Measure.restrict_apply_univ] using (triangleSet_isCompact 1).measure_ne_top

def faceMean : FaceL2 →L[ℝ] ℝ := l2Integral _ faceMeasure_finite

theorem faceMean_eq (T : FaceL2) : faceMean T = ∫ p in triangleSet 1, T p :=
  l2Integral_eq _ faceMeasure_finite T

theorem faceMean_smoothFaceL2 {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    faceMean (smoothFaceL2 hu σ o h r) = ∫ p in triangleSet 1, u (scaledFaceChart σ o h r p) :=
  l2Integral_toLp _ faceMeasure_finite (smooth_face_memLp hu σ o h r)

theorem weak_face_trace_bound {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (r : Fin 4) {T : FaceL2}
    (hT : HasH1FaceTrace f g σ o h r T) :
    h ^ 2 * ‖T‖ ^ 2 ≤
      6 * h⁻¹ * (∫ x in scaledChainSet σ o h, (f x) ^ 2) +
        h * ∑ j : Fin 3, ∫ x in scaledChainSet σ o h, (g j x) ^ 2 := by
  obtain ⟨u, hu⟩ := hf
  have hl := ((hT u hu).norm.pow 2).const_mul (h ^ 2)
  have hr := ((smooth_value_local_square_integral_tendsto hu (scaledChainSet σ o h)).const_mul
    (6 * h⁻¹)).add ((tendsto_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j _ => smooth_gradient_local_square_integral_tendsto hu (scaledChainSet σ o h) j)).const_mul h)
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [smoothFaceL2_norm_square]
  exact scaled_smooth_face_trace (hu.smooth n) σ o h hh r

theorem weak_gauss {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (T : Fin 4 → FaceL2)
    (hT : ∀ r, HasH1FaceTrace f g σ o h r (T r)) (j : Fin 3) :
    (∫ x in scaledChainSet σ o h, g j x) =
      ∑ r : Fin 4, outwardWeight σ h r j * faceMean (T r) := by
  obtain ⟨u, hu⟩ := hf
  have hμ : (volume.restrict (scaledChainSet σ o h)) univ ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ] using (scaledChainSet_isCompact σ o h hh.ne').measure_ne_top
  have hl : Tendsto (fun n => ∫ x in scaledChainSet σ o h,
      fderiv ℝ (u n) x (Pi.single j 1)) atTop (𝓝 (∫ x in scaledChainSet σ o h, g j x)) := by
    simpa only [Function.comp_def, l2Integral_toLp] using
      ((l2Integral _ hμ).continuous.tendsto _).comp
        (smooth_gradient_local_L2_tendsto hu (scaledChainSet σ o h) j)
  have hr : Tendsto (fun n => ∑ r : Fin 4, outwardWeight σ h r j *
      faceMean (smoothFaceL2 (hu.smooth n) σ o h r)) atTop
        (𝓝 (∑ r : Fin 4, outwardWeight σ h r j * faceMean (T r))) :=
    tendsto_finsetSum _ (fun r _ =>
      (((faceMean.continuous.tendsto (T r)).comp (hT r u hu)).const_mul (outwardWeight σ h r j)))
  have he (n : ℕ) : (∫ x in scaledChainSet σ o h,
      fderiv ℝ (u n) x (Pi.single j 1)) =
      ∑ r : Fin 4, outwardWeight σ h r j * faceMean (smoothFaceL2 (hu.smooth n) σ o h r) := by
    simp only [faceMean_smoothFaceL2]
    exact scaled_smooth_gauss (hu.smooth n) σ o h hh j
  exact tendsto_nhds_unique (hl.congr' (Eventually.of_forall he)) hr

theorem inH1ZeroCube_boundary_trace_zero {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) {T : FaceL2} (hT : HasH1FaceTrace f g σ o h r T)
    (hb : ∀ p ∈ triangleSet 1, scaledFaceChart σ o h r p ∉ openCube) : T = 0 := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hz (n : ℕ) : smoothFaceL2 (ha.smooth n) σ o h r = 0 := by
    have he : (fun p => u n (scaledFaceChart σ o h r p)) =ᵐ[
        (volume : Measure FacePoint).restrict (triangleSet 1)] (0 : FacePoint → ℝ) := by
      filter_upwards [ae_restrict_mem (triangleSet_isCompact 1).measurableSet] with p hp
      exact image_eq_zero_of_notMem_tsupport (fun hx => hb p hp ((hu n).2.2.1 hx))
    exact (MemLp.toLp_congr (smooth_face_memLp (ha.smooth n) σ o h r) MemLp.zero he).trans
      (MemLp.toLp_zero _)
  exact tendsto_nhds_unique (hT u ha) (by simpa only [hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : FaceL2)) atTop (𝓝 0)))

end FreudenthalSVLean.WeakFaceGauss
