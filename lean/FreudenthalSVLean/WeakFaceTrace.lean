import FreudenthalSVLean.ScaledSmoothCalculus
import FreudenthalSVLean.ConformingH1Zero
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Face traces determined by actual H1 approximation

For the trace step of manuscript Lemma `means`, restrictions of genuine
smooth H1 approximants to an actual Freudenthal face form a Cauchy sequence
in the actual L2 space of its triangle chart.  The limit is unique and
independent of the smooth approximation.  The proof uses the explicit
physical trace estimate, true L2 integrals, and completeness of L2; it
does not assume a Sobolev trace operator.  The hypotheses spell out actual
weak gradients and actual H1 convergence.  The uniform initial mean lift
is not inferred from existence of these traces alone.
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

noncomputable section

namespace FreudenthalSVLean.WeakFaceTrace

set_option backward.isDefEq.respectTransparency false

abbrev FaceL2 := Lp ℝ 2 ((volume : Measure FacePoint).restrict (triangleSet 1))

theorem smooth_face_memLp {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    MemLp (fun p => u (scaledFaceChart σ o h r p)) 2
      ((volume : Measure FacePoint).restrict (triangleSet 1)) := by
  have hc := hu.continuous.comp (scaledFaceChart_continuous σ o h r)
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).mpr
  exact (hc.pow 2).continuousOn.integrableOn_compact (μ := volume) (triangleSet_isCompact 1)

def smoothFaceL2 {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) : FaceL2 :=
  (smooth_face_memLp hu σ o h r).toLp (fun p => u (scaledFaceChart σ o h r p))

theorem toLp_norm_square {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  simp [hx, pow_two]

theorem smoothFaceL2_norm_square {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    ‖smoothFaceL2 hu σ o h r‖ ^ 2 =
      ∫ p in triangleSet 1, (u (scaledFaceChart σ o h r p)) ^ 2 :=
  toLp_norm_square (smooth_face_memLp hu σ o h r)

theorem smoothFaceL2_sub {u v : Space → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    smoothFaceL2 (hu.sub hv) σ o h r = smoothFaceL2 hu σ o h r - smoothFaceL2 hv σ o h r := by
  exact (smooth_face_memLp hu σ o h r).toLp_sub (smooth_face_memLp hv σ o h r)

def traceConstant (h : ℝ) : ℝ := 6 * h⁻¹ ^ 3 + h⁻¹

theorem traceConstant_pos {h : ℝ} (hh : 0 < h) : 0 < traceConstant h := by
  unfold traceConstant
  positivity

theorem smoothFaceL2_global_bound {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (iu : MemLp u 2 volume)
    (id : ∀ j : Fin 3, MemLp (fun x => fderiv ℝ u x (Pi.single j 1)) 2 volume)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    ‖smoothFaceL2 hu σ o h r‖ ^ 2 ≤ traceConstant h *
      ((∫ x, (u x) ^ 2) + ∑ j : Fin 3, ∫ x, (fderiv ℝ u x (Pi.single j 1)) ^ 2) := by
  have ht := scaled_smooth_face_trace hu σ o h hh r
  have hv : (∫ x in scaledChainSet σ o h, (u x) ^ 2) ≤ ∫ x, (u x) ^ 2 :=
    setIntegral_le_integral iu.integrable_sq (Eventually.of_forall (fun _ => sq_nonneg _))
  have hg : (∑ j : Fin 3, ∫ x in scaledChainSet σ o h,
      (fderiv ℝ u x (Pi.single j 1)) ^ 2) ≤
      ∑ j : Fin 3, ∫ x, (fderiv ℝ u x (Pi.single j 1)) ^ 2 :=
    Finset.sum_le_sum (fun j _ =>
      setIntegral_le_integral (id j).integrable_sq (Eventually.of_forall (fun _ => sq_nonneg _)))
  have hlocal := ht.trans (add_le_add
    (mul_le_mul_of_nonneg_left hv (by positivity)) (mul_le_mul_of_nonneg_left hg hh.le))
  have hn : 0 ≤ (∫ x, (u x) ^ 2) := integral_nonneg (fun _ => sq_nonneg _)
  have hgn : 0 ≤ ∑ j : Fin 3, ∫ x, (fderiv ℝ u x (Pi.single j 1)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  rw [smoothFaceL2_norm_square]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hh)).mp
  calc
    _ ≤ _ := hlocal
    _ ≤ h ^ 2 * (traceConstant h * ((∫ x, (u x) ^ 2) +
        ∑ j : Fin 3, ∫ x, (fderiv ℝ u x (Pi.single j 1)) ^ 2)) := by
      have he : h ^ 2 * traceConstant h = 6 * h⁻¹ + h := by
        unfold traceConstant
        field_simp [hh.ne']
      rw [← mul_assoc, he]
      nlinarith [mul_nonneg hn hh.le, mul_nonneg hgn (show 0 ≤ 6 * h⁻¹ by positivity)]

def h1Error (f : Space → ℝ) (g : Fin 3 → Space → ℝ) (u : Space → ℝ) : ℝ :=
  (∫ x, (u x - f x) ^ 2) + ∑ j : Fin 3,
    ∫ x, (fderiv ℝ u x (Pi.single j 1) - g j x) ^ 2

theorem h1Error_nonneg (f : Space → ℝ) (g : Fin 3 → Space → ℝ) (u : Space → ℝ) :
    0 ≤ h1Error f g u :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

structure SmoothH1Approximation (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (u : ℕ → Space → ℝ) : Prop where
  weak_gradient : HasL2WeakGradient f g
  smooth : ∀ n, ContDiff ℝ 1 (u n)
  memLp : ∀ n, MemLp (u n) 2 volume
  partial_memLp : ∀ n j, MemLp (fun x => fderiv ℝ (u n) x (Pi.single j 1)) 2 volume
  convergence : Tendsto (fun n => h1Error f g (u n)) atTop (𝓝 0)

theorem inH1ZeroCube_has_smoothApproximation {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) : ∃ u, SmoothH1Approximation f g u := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  refine ⟨u, hw, fun n => (hu n).1.of_le (by simp),
    fun n => (hu n).2.2.2.1, fun n => (hu n).2.2.2.2, hc⟩

theorem integral_square_sub_triangle {a b c : Space → ℝ}
    (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) (hc : MemLp c 2 volume) :
    (∫ x, (a x - b x) ^ 2) ≤
      2 * ((∫ x, (a x - c x) ^ 2) + ∫ x, (b x - c x) ^ 2) := by
  have ht := integral_mono (ha.sub hb).integrable_sq
    (((ha.sub hc).integrable_sq.add (hb.sub hc).integrable_sq).const_mul 2)
    (fun x => by
      change (a x - b x) ^ 2 ≤ 2 * ((a x - c x) ^ 2 + (b x - c x) ^ 2)
      nlinarith [sq_nonneg (a x - c x + (b x - c x))])
  change (∫ x, (a x - b x) ^ 2) ≤
    ∫ x, 2 * ((a x - c x) ^ 2 + (b x - c x) ^ 2) at ht
  have he : (∫ x, (a x - c x) ^ 2 + (b x - c x) ^ 2) =
      (∫ x, (a x - c x) ^ 2) + ∫ x, (b x - c x) ^ 2 := by
    simpa only [Pi.sub_apply] using!
      integral_add (ha.sub hc).integrable_sq (hb.sub hc).integrable_sq
  rw [integral_const_mul, he] at ht
  exact ht

theorem smooth_partial_sub {u v : Space → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (x : Space) (j : Fin 3) :
    fderiv ℝ (fun y => u y - v y) x (Pi.single j 1) =
      fderiv ℝ u x (Pi.single j 1) - fderiv ℝ v x (Pi.single j 1) := by
  have hd : HasFDerivAt (fun y => u y - v y) (fderiv ℝ u x - fderiv ℝ v x) x := by
    simpa only [Pi.sub_apply] using!
      (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.sub
        (hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  rfl

theorem smoothFaceL2_approximation_difference {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u v : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u) (hv : SmoothH1Approximation f g v)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) (m n : ℕ) :
    ‖smoothFaceL2 (hu.smooth m) σ o h r - smoothFaceL2 (hv.smooth n) σ o h r‖ ^ 2 ≤
      2 * traceConstant h * (h1Error f g (u m) + h1Error f g (v n)) := by
  have id (j : Fin 3) : MemLp
      (fun x => fderiv ℝ (fun y => u m y - v n y) x (Pi.single j 1)) 2 volume := by
    simpa only [smooth_partial_sub (hu.smooth m) (hv.smooth n), Pi.sub_apply] using!
      (hu.partial_memLp m j).sub (hv.partial_memLp n j)
  have ht := smoothFaceL2_global_bound ((hu.smooth m).sub (hv.smooth n))
    ((hu.memLp m).sub (hv.memLp n)) id σ o h hh r
  rw [smoothFaceL2_sub (hu.smooth m) (hv.smooth n)] at ht
  simp only [smooth_partial_sub (hu.smooth m) (hv.smooth n)] at ht
  have hvbound := integral_square_sub_triangle (hu.memLp m) (hv.memLp n) hu.weak_gradient.1
  have hgbound := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    integral_square_sub_triangle (hu.partial_memLp m j) (hv.partial_memLp n j)
      (hu.weak_gradient.2 j).1)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hgbound
  have he : ((∫ x, (u m x - v n x) ^ 2) + ∑ j : Fin 3,
      ∫ x, (fderiv ℝ (u m) x (Pi.single j 1) - fderiv ℝ (v n) x (Pi.single j 1)) ^ 2) ≤
      2 * (h1Error f g (u m) + h1Error f g (v n)) := by
    unfold h1Error
    linarith
  calc
    _ ≤ _ := ht
    _ ≤ traceConstant h * (2 * (h1Error f g (u m) + h1Error f g (v n))) :=
      mul_le_mul_of_nonneg_left he (traceConstant_pos hh).le
    _ = _ := by ring

theorem smoothFaceL2_cauchy {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    {u : ℕ → Space → ℝ} (hu : SmoothH1Approximation f g u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    CauchySeq (fun n => smoothFaceL2 (hu.smooth n) σ o h r) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ : ℝ := ε ^ 2 / (4 * traceConstant h)
  have hc := traceConstant_pos hh
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hu.convergence.eventually (gt_mem_nhds hδ))
  refine ⟨K, fun m hm n hn => ?_⟩
  have ht := smoothFaceL2_approximation_difference hu hu σ o h hh r m n
  have he : 2 * traceConstant h * (δ + δ) = ε ^ 2 := by
    dsimp [δ]
    field_simp [hc.ne']
    norm_num
  have hs : ‖smoothFaceL2 (hu.smooth m) σ o h r - smoothFaceL2 (hu.smooth n) σ o h r‖ ^ 2 <
      ε ^ 2 :=
    ht.trans_lt ((mul_lt_mul_of_pos_left (add_lt_add (hK m hm) (hK n hn))
      (by positivity : 0 < 2 * traceConstant h)).trans_eq he)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (smoothFaceL2 (hu.smooth m) σ o h r - smoothFaceL2 (hu.smooth n) σ o h r)]

theorem smoothFaceL2_approximations_distance_tendsto {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} {u v : ℕ → Space → ℝ}
    (hu : SmoothH1Approximation f g u) (hv : SmoothH1Approximation f g v)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    Tendsto (fun n => dist (smoothFaceL2 (hu.smooth n) σ o h r)
      (smoothFaceL2 (hv.smooth n) σ o h r)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n =>
      ‖smoothFaceL2 (hu.smooth n) σ o h r - smoothFaceL2 (hv.smooth n) σ o h r‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun n => smoothFaceL2_approximation_difference hu hv σ o h hh r n n)
      (by simpa only [zero_add, mul_zero] using
        ((hu.convergence.add hv.convergence).const_mul (2 * traceConstant h)))
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, dist_eq_norm] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

/-- Every genuine smooth H1 approximation has the same actual L2 face
limit.  This definition quantifies over all approximations, not a selected
sequence or a coefficient-defined surrogate trace. -/
def HasH1FaceTrace (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) (T : FaceL2) : Prop :=
  ∀ (u : ℕ → Space → ℝ) (hu : SmoothH1Approximation f g u),
    Tendsto (fun n => smoothFaceL2 (hu.smooth n) σ o h r) atTop (𝓝 T)

theorem hasH1FaceTrace_exists_unique {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : ∃ u, SmoothH1Approximation f g u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    ∃! T : FaceL2, HasH1FaceTrace f g σ o h r T := by
  obtain ⟨u, hu⟩ := hf
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete (smoothFaceL2_cauchy hu σ o h hh r)
  refine ⟨T, ?_, ?_⟩
  · intro v hv
    exact hT.congr_dist (smoothFaceL2_approximations_distance_tendsto hu hv σ o h hh r)
  · intro S hS
    exact tendsto_nhds_unique (hS u hu) hT

theorem inH1ZeroCube_has_faceTrace {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    ∃! T : FaceL2, HasH1FaceTrace f g σ o h r T :=
  hasH1FaceTrace_exists_unique (inH1ZeroCube_has_smoothApproximation hf) σ o h hh r

end FreudenthalSVLean.WeakFaceTrace
