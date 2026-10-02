import FreudenthalSVLean.H1ApproximationLinearity
import FreudenthalSVLean.WeakFaceGauss

/-!
# A fixed linear face-trace operator on genuine H1 data

For the quantifiers and linearity in manuscript Lemma `means`, actual
functions together with their actual weak gradients and smooth H1
approximations form a proved real vector space.  A single face-trace map
is chosen before its input and is proved linear by unique L2 limits.
Its physical bound and genuine element Gauss identity are inherited from
the established actual-function theorems.  This is an actual trace map,
not an input-dependent selection of geometry or a postulated trace rule.
No stable interpolant or continuous divergence inverse is constructed.
-/

open scoped BigOperators Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakFaceGauss
open FreudenthalSVLean.H1ApproximationLinearity

noncomputable section

namespace FreudenthalSVLean.WeakLinearFaceTrace

set_option backward.isDefEq.respectTransparency false

abbrev H1Data := (Space → ℝ) × (Fin 3 → Space → ℝ)

def smoothH1Space : Submodule ℝ H1Data where
  carrier := {v | ∃ u, SmoothH1Approximation v.1 v.2 u}
  zero_mem' := ⟨fun (_ : ℕ) (_ : Space) => 0, smoothH1Approximation_zero⟩
  add_mem' := by
    rintro v w ⟨u, hu⟩ ⟨z, hz⟩
    exact ⟨fun n x => u n x + z n x, smoothH1Approximation_add hu hz⟩
  smul_mem' := by
    rintro c v ⟨u, hu⟩
    exact ⟨fun n x => c * u n x, smoothH1Approximation_const_mul hu c⟩

def trace (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4)
    (v : smoothH1Space) : FaceL2 :=
  Classical.choose (hasH1FaceTrace_exists_unique v.property σ o h hh r).exists

theorem trace_spec (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4)
    (v : smoothH1Space) : HasH1FaceTrace v.val.1 v.val.2 σ o h r (trace σ o h hh r v) :=
  Classical.choose_spec (hasH1FaceTrace_exists_unique v.property σ o h hh r).exists

theorem smoothFaceL2_add {u v : Space → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hw : ContDiff ℝ 1 (fun x => u x + v x)) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) : smoothFaceL2 hw σ o h r =
      smoothFaceL2 hu σ o h r + smoothFaceL2 hv σ o h r := by
  exact (smooth_face_memLp hu σ o h r).toLp_add (smooth_face_memLp hv σ o h r)

theorem smoothFaceL2_const_mul {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ)
    (hw : ContDiff ℝ 1 (fun x => c * u x)) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) : smoothFaceL2 hw σ o h r = c • smoothFaceL2 hu σ o h r := by
  simpa only [smoothFaceL2, Pi.smul_apply, smul_eq_mul] using!
    MemLp.toLp_const_smul c (smooth_face_memLp hu σ o h r)

theorem trace_add (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4)
    (v w : smoothH1Space) :
    trace σ o h hh r (v + w) = trace σ o h hh r v + trace σ o h hh r w := by
  obtain ⟨u, hu⟩ := v.property
  obtain ⟨z, hz⟩ := w.property
  have ha : SmoothH1Approximation (v + w).val.1 (v + w).val.2 (fun n x => u n x + z n x) :=
    smoothH1Approximation_add hu hz
  have ht := ((trace_spec σ o h hh r v) u hu).add ((trace_spec σ o h hh r w) z hz)
  have he (n : ℕ) : smoothFaceL2 (ha.smooth n) σ o h r =
      smoothFaceL2 (hu.smooth n) σ o h r + smoothFaceL2 (hz.smooth n) σ o h r :=
    smoothFaceL2_add (hu.smooth n) (hz.smooth n) (ha.smooth n) σ o h r
  exact tendsto_nhds_unique ((trace_spec σ o h hh r (v + w)) _ ha)
    (ht.congr' (Eventually.of_forall (fun n => (he n).symm)))

theorem trace_smul (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4)
    (c : ℝ) (v : smoothH1Space) : trace σ o h hh r (c • v) = c • trace σ o h hh r v := by
  obtain ⟨u, hu⟩ := v.property
  have ha : SmoothH1Approximation (c • v).val.1 (c • v).val.2 (fun n x => c * u n x) :=
    smoothH1Approximation_const_mul hu c
  have ht := ((trace_spec σ o h hh r v) u hu).const_smul c
  have he (n : ℕ) : smoothFaceL2 (ha.smooth n) σ o h r = c • smoothFaceL2 (hu.smooth n) σ o h r :=
    smoothFaceL2_const_mul (hu.smooth n) c (ha.smooth n) σ o h r
  exact tendsto_nhds_unique ((trace_spec σ o h hh r (c • v)) _ ha)
    (ht.congr' (Eventually.of_forall (fun n => (he n).symm)))

def traceMap (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    smoothH1Space →ₗ[ℝ] FaceL2 where
  toFun := trace σ o h hh r
  map_add' := trace_add σ o h hh r
  map_smul' c v := trace_smul σ o h hh r c v

theorem traceMap_physical_bound (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (hh : 0 < h) (r : Fin 4) (v : smoothH1Space) :
    h ^ 2 * ‖traceMap σ o h hh r v‖ ^ 2 ≤
      6 * h⁻¹ * (∫ x in scaledChainSet σ o h, (v.val.1 x) ^ 2) +
        h * ∑ j : Fin 3, ∫ x in scaledChainSet σ o h, (v.val.2 j x) ^ 2 :=
  weak_face_trace_bound v.property σ o h hh r (trace_spec σ o h hh r v)

theorem traceMap_gauss (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h)
    (v : smoothH1Space) (j : Fin 3) :
    (∫ x in scaledChainSet σ o h, v.val.2 j x) =
      ∑ r : Fin 4, outwardWeight σ h r j * faceMean (traceMap σ o h hh r v) :=
  weak_gauss v.property σ o h hh (fun r => traceMap σ o h hh r v)
    (fun r => trace_spec σ o h hh r v) j

end FreudenthalSVLean.WeakLinearFaceTrace
