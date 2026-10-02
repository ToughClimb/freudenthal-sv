import FreudenthalSVLean.WeakLinearFaceTrace
import FreudenthalSVLean.H1ApproximationL2

/-!
# Weak face traces agree with actual finite-element restrictions

For the face fluxes in manuscript Lemma `means`, the weak-H1 trace of
every actual conforming finite-element velocity is its genuine polynomial
face restriction.  The explicit interior smooth approximation converges
at every point of the continuous zero extension.  A bounded dominated
convergence argument on the genuine triangle gives convergence in face
L2, and uniqueness of the proved weak trace identifies the two objects.
This is a codimension-one convergence proof, not an inference from
volume almost-everywhere equality or volume L2 convergence.
-/

open scoped BigOperators ContDiff Topology
open MeasureTheory MvPolynomial Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.BoundedMeshFunctions
open FreudenthalSVLean.InteriorMollification
open FreudenthalSVLean.InteriorMollificationL2
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2

noncomputable section

namespace FreudenthalSVLean.ConformingWeakFaceTrace

set_option backward.isDefEq.respectTransparency false

theorem continuous_face_memLp {f : Space → ℝ} (hf : Continuous f)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    MemLp (fun p => f (scaledFaceChart σ o h r p)) 2
      ((volume : Measure FacePoint).restrict (triangleSet 1)) := by
  have hc := hf.comp (scaledFaceChart_continuous σ o h r)
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable.restrict).mpr
  exact (hc.pow 2).continuousOn.integrableOn_compact (μ := volume) (triangleSet_isCompact 1)

def continuousFaceL2 {f : Space → ℝ} (hf : Continuous f)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) : FaceL2 :=
  (continuous_face_memLp hf σ o h r).toLp (fun p => f (scaledFaceChart σ o h r p))

theorem interiorMollify_face_square_error_tendsto {f : Space → ℝ} (hc : Continuous f)
    (hf : LocallyIntegrable f volume) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    Tendsto (fun n => ∫ p in triangleSet 1,
      (interiorMollify n f (scaledFaceChart σ o h r p) - f (scaledFaceChart σ o h r p)) ^ 2)
      atTop (𝓝 0) := by
  have hz : (∫ _p in triangleSet 1, (0 : ℝ)) = 0 := by simp
  rw [← hz]
  apply tendsto_integral_of_dominated_convergence (fun _ : FacePoint => 4 * M ^ 2)
  · intro n
    exact ((((interiorMollify_contDiff n hf).continuous.comp (scaledFaceChart_continuous σ o h r)).sub
      (hc.comp (scaledFaceChart_continuous σ o h r))).pow 2).aestronglyMeasurable.restrict
  · exact integrableOn_const (triangleSet_isCompact 1).measure_ne_top
  · intro n
    filter_upwards with p
    have hn := (norm_sub_le (interiorMollify n f (scaledFaceChart σ o h r p))
      (f (scaledFaceChart σ o h r p))).trans
      (add_le_add (interiorMollify_norm_le hf.aestronglyMeasurable hM hb n _) (hb _))
    rw [norm_pow]
    nlinarith [norm_nonneg (interiorMollify n f (scaledFaceChart σ o h r p) -
      f (scaledFaceChart σ o h r p))]
  · filter_upwards with p
    simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      ((interiorMollify_tendsto hf.aestronglyMeasurable (scaledFaceChart σ o h r p)
        hc.continuousAt).sub_const (f (scaledFaceChart σ o h r p))).pow 2

theorem velocityFunction_interiorApproximation {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    SmoothH1Approximation (velocityFunction hN v j)
      (fun i => piecewisePressure (fun t => pderiv i (v.val t j)))
      (fun n => interiorMollify n (velocityFunction hN v j)) := by
  have hf := (velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)
  have hs : Function.support (velocityFunction hN v j) ⊆ cube := by
    intro x hx
    by_contra hn
    exact hx (velocityFunction_zero_off_cube hN v j x hn)
  refine ⟨velocityFunction_hasL2WeakGradient hN v j,
    fun n => (interiorMollify_contDiff n hf).of_le (by simp), ?_, ?_, ?_⟩
  · intro n
    exact (interiorMollify_contDiff n hf).continuous.memLp_of_hasCompactSupport
      (interiorMollify_hasCompactSupport n hs)
  · intro n i
    have hc := interiorMollify_hasCompactSupport n hs
    have hd := interiorMollify_contDiff n hf
    have hdi : Continuous (fun x => fderiv ℝ (interiorMollify n (velocityFunction hN v j))
        x (Pi.single i 1)) := (hd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hci : HasCompactSupport (fun x => fderiv ℝ (interiorMollify n (velocityFunction hN v j))
        x (Pi.single i 1)) := by
      simpa only [Function.comp_def] using (hc.fderiv ℝ).comp_left
        (g := fun L : Space →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)
    exact hdi.memLp_of_hasCompactSupport hci
  · have hgrad := tendsto_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ => velocityFunction_smooth_gradient_error hN v j i)
    simpa only [h1Error, Finset.sum_const_zero, add_zero] using
      (velocityFunction_smooth_value_error hN v j).add hgrad

theorem velocityFunction_has_continuous_faceTrace {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    HasH1FaceTrace (velocityFunction hN v j)
      (fun i => piecewisePressure (fun t => pderiv i (v.val t j))) σ o h r
      (continuousFaceL2 (velocityFunction_continuous hN v j) σ o h r) := by
  have ha := velocityFunction_interiorApproximation hN v j
  obtain ⟨M, hM, hb⟩ := velocityFunction_uniform_bound hN v j
  have he := interiorMollify_face_square_error_tendsto (velocityFunction_continuous hN v j)
    ((velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)) hM.le hb σ o h r
  have hl : Tendsto (fun n => smoothFaceL2 (ha.smooth n) σ o h r) atTop
      (𝓝 (continuousFaceL2 (velocityFunction_continuous hN v j) σ o h r)) :=
    toLp_tendsto_of_square_error (fun n => smooth_face_memLp (ha.smooth n) σ o h r)
      (continuous_face_memLp (velocityFunction_continuous hN v j) σ o h r) he
  intro u hu
  exact hl.congr_dist (smoothFaceL2_approximations_distance_tendsto ha hu σ o h hh r)

theorem velocityFunction_weak_trace_polynomial {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (r : Fin 4) (j : Fin 3) {T : FaceL2}
    (hT : HasH1FaceTrace (velocityFunction hN v j)
      (fun i => piecewisePressure (fun w => pderiv i (v.val w j)))
      t.2 (cellOrigin t.1) (meshScale N) r T) :
    T = continuousFaceL2 (continuous_eval (v.val t j))
      t.2 (cellOrigin t.1) (meshScale N) r := by
  have ha := velocityFunction_interiorApproximation hN v j
  have ht := velocityFunction_has_continuous_faceTrace hN v j t.2 (cellOrigin t.1)
    (meshScale N) (meshScale_pos N hN) r
  have he := tendsto_nhds_unique (hT _ ha) (ht _ ha)
  rw [he]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem (triangleSet_isCompact 1).measurableSet] with p hp
  exact velocityFunction_on_element hN v t _
    (scaledFaceChart_mem t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN).ne' r p hp) j

end FreudenthalSVLean.ConformingWeakFaceTrace
