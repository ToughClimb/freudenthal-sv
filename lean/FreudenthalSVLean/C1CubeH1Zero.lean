import FreudenthalSVLean.ConformingH1Zero

/-!
# Actual H1_0 membership for C1 cube-supported functions

For the truncated continuous lifting in manuscript Lemma `means`, a
genuine C1 function with compact support in the closed cube belongs to
the actual smooth-closure H1_0 space. Classical derivatives are true
weak derivatives by Lipschitz integration by parts, and the existing
normalized mollification/compression sequence converges in actual H1.
Thus C1 compact support, rather than an assumed Sobolev identification
or an unproved assertion of infinite differentiability, suffices.
-/

open scoped BigOperators ContDiff Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.InteriorMollification
open FreudenthalSVLean.InteriorMollificationL2
open FreudenthalSVLean.ConformingH1Zero

noncomputable section

namespace FreudenthalSVLean.C1CubeH1Zero

set_option backward.isDefEq.respectTransparency false

def classicalPartial (f : Space → ℝ) (i : Fin 3) : Space → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

theorem classicalPartial_continuous {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (classicalPartial f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem classicalPartial_compact {f : Space → ℝ} (hc : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (classicalPartial f i) := by
  exact (hc.fderiv ℝ).comp_left
    (g := fun L : Space →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)

theorem classicalPartial_support_cube {f : Space → ℝ}
    (hs : Function.support f ⊆ cube) (i : Fin 3) : Function.support (classicalPartial f i) ⊆ cube := by
  intro x hx
  by_contra hn
  have ht : x ∉ tsupport f := fun h => hn (closure_minimal hs isClosed_Icc h)
  apply hx
  change fderiv ℝ f x (Pi.single i 1) = 0
  rw [fderiv_of_notMem_tsupport ℝ ht]
  rfl

theorem C1_hasL2WeakGradient {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : HasL2WeakGradient f (classicalPartial f) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by norm_num)
  refine ⟨hf.continuous.memLp_of_hasCompactSupport hc, fun i => ⟨?_, ?_⟩⟩
  · exact (classicalPartial_continuous hf i).memLp_of_hasCompactSupport
      (classicalPartial_compact hc i)
  · exact lipschitz_hasWeakPartial hC i (Eventually.of_forall (fun _ => rfl))

theorem C1_cube_inH1ZeroCube {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hs : Function.support f ⊆ cube) :
    InH1ZeroCube f (classicalPartial f) := by
  have hw := C1_hasL2WeakGradient hf hc
  have hloc := hw.1.locallyIntegrable (by norm_num)
  have hvalue : Tendsto (fun n => ∫ x, (interiorMollify n f x - f x) ^ 2) atTop (𝓝 0) := by
    obtain ⟨M, hb⟩ := hc.exists_bound_of_continuous hf.continuous
    exact interiorMollify_square_error_tendsto hloc ((norm_nonneg (f 0)).trans (hb 0)) hb hs
      (Eventually.of_forall (fun x => hf.continuous.continuousAt))
  have hgradient (i : Fin 3) : Tendsto (fun n => ∫ x,
      (fderiv ℝ (interiorMollify n f) x (Pi.single i 1) - classicalPartial f i x) ^ 2)
      atTop (𝓝 0) := by
    have hci := classicalPartial_continuous hf i
    obtain ⟨M, hb⟩ := (classicalPartial_compact hc i).exists_bound_of_continuous hci
    simp only [interiorMollify_partial _ hloc i (hw.2 i).2]
    exact interior_scaled_square_error_tendsto
      ((hw.2 i).1.locallyIntegrable (by norm_num))
      ((norm_nonneg (classicalPartial f i 0)).trans (hb 0)) hb
      (classicalPartial_support_cube hs i) (Eventually.of_forall (fun x => hci.continuousAt))
      factor factor_tendsto (fun n => ⟨(factor_pos n).le, factor_le_five n⟩)
  refine ⟨hw, (fun n => interiorMollify n f), ?_, ?_⟩
  · intro n
    have hd := interiorMollify_contDiff n hloc
    have hcn := interiorMollify_hasCompactSupport n hs
    refine ⟨hd, hcn, interiorMollify_tsupport_subset_openCube n hs,
      hd.continuous.memLp_of_hasCompactSupport hcn, fun i => ?_⟩
    exact (classicalPartial_continuous (hd.of_le (by simp)) i).memLp_of_hasCompactSupport
      (classicalPartial_compact hcn i)
  · have hd := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hgradient i)
    simpa only [Finset.sum_const_zero, add_zero] using hvalue.add hd

end FreudenthalSVLean.C1CubeH1Zero
