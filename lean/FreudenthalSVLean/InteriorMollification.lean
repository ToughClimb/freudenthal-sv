import FreudenthalSVLean.MollificationL2
import FreudenthalSVLean.BoundedMeshFunctions

/-!
# Smooth approximation with support strictly inside the physical cube

For the manuscript's H1_0 identification, normalized smooth convolution
is composed with the homothety x ↦ (1+4 epsilon)(x-c)+c, c=(1/2,1/2,1/2).
The convolution expands support by at most epsilon, while this homothety
compresses it into a closed box a positive distance inside the open cube.
The true classical derivatives follow from the weak-gradient convolution
identity and the chain rule.  The maps converge to the original values
at every continuity point, including almost every polynomial-gradient
point; no boundary trace or density theorem is assumed.
-/

open scoped BigOperators ContDiff Convolution Pointwise Topology
open Set Filter MeasureTheory ContinuousLinearMap Metric
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.WeakGradientMollification
open FreudenthalSVLean.MollificationL2

noncomputable section

namespace FreudenthalSVLean.InteriorMollification

set_option backward.isDefEq.respectTransparency false

def center : Space := fun _ => 1 / 2
def factor (n : ℕ) : ℝ := 1 + 4 * (mollifier n).rOut
def margin (n : ℕ) : ℝ := (mollifier n).rOut / factor n
def expand (n : ℕ) (x : Space) : Space := factor n • (x - center) + center
def innerBox (n : ℕ) : Set Space := Icc (fun _ => margin n) (fun _ => 1 - margin n)
def interiorMollify (n : ℕ) (f : Space → ℝ) (x : Space) : ℝ :=
  mollify (mollifier n) f (expand n x)

theorem factor_pos (n : ℕ) : 0 < factor n := by
  have hp := (mollifier n).rOut_pos
  dsimp [factor]
  linarith

theorem factor_le_five (n : ℕ) : factor n ≤ 5 := by
  dsimp [factor]
  linarith [mollifier_rOut_le_one n]

theorem margin_pos (n : ℕ) : 0 < margin n := div_pos (mollifier n).rOut_pos (factor_pos n)

theorem expand_apply (n : ℕ) (x : Space) (j : Fin 3) :
    expand n x j = factor n * (x j - 1 / 2) + 1 / 2 := rfl

theorem expand_contDiff (n : ℕ) : ContDiff ℝ ∞ (expand n) := by
  change ContDiff ℝ ∞ (fun x : Space => factor n • (x - center) + center)
  fun_prop

theorem expand_hasFDerivAt (n : ℕ) (x : Space) :
    HasFDerivAt (expand n) (factor n • ContinuousLinearMap.id ℝ Space) x := by
  simpa only [expand, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, id_eq, sub_zero, add_zero] using!
    (((hasFDerivAt_id x).sub (hasFDerivAt_const center x)).const_smul (factor n)).add
      (hasFDerivAt_const center x)

theorem interiorMollify_contDiff (n : ℕ) {f : Space → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (interiorMollify n f) := (mollify_contDiff (mollifier n) hf).comp (expand_contDiff n)

theorem interiorMollify_partial (n : ℕ) {f g : Space → ℝ}
    (hf : LocallyIntegrable f volume) (i : Fin 3) (hw : HasWeakPartial f g i) (x : Space) :
    fderiv ℝ (interiorMollify n f) x (Pi.single i 1) = factor n * interiorMollify n g x := by
  have hm : DifferentiableAt ℝ (mollify (mollifier n) f) (expand n x) :=
    ((mollify_contDiff (mollifier n) hf).differentiable (by simp)).differentiableAt
  have hd : HasFDerivAt (interiorMollify n f)
      ((fderiv ℝ (mollify (mollifier n) f) (expand n x)).comp
        (factor n • ContinuousLinearMap.id ℝ Space)) x := by
    simpa only [interiorMollify, Function.comp_def] using!
      hm.hasFDerivAt.comp x (expand_hasFDerivAt n x)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, mollify_partial (mollifier n) hf i hw]
  rfl

theorem innerBox_subset_openCube (n : ℕ) : innerBox n ⊆ openCube := by
  intro x hx
  apply (mem_openCube x).mpr
  intro j
  exact ⟨(margin_pos n).trans_le (hx.1 j), lt_of_le_of_lt (hx.2 j) (by linarith [margin_pos n])⟩

theorem interiorMollify_support_box (n : ℕ) {f : Space → ℝ}
    (hs : Function.support f ⊆ cube) : Function.support (interiorMollify n f) ⊆ innerBox n := by
  intro x hx
  have ht : expand n x ∈ Function.support (mollify (mollifier n) f) := hx
  have hp := support_convolution_subset (lsmul ℝ ℝ) ht
  rw [(mollifier n).support_normed_eq] at hp
  obtain ⟨y, hy, z, hz, he⟩ := Set.mem_add.mp hp
  have hY := hs hy
  have hZ : ‖z‖ < (mollifier n).rOut := by simpa only [mem_ball, dist_zero_right] using hz
  have he' (j : Fin 3) : factor n * (x j - 1 / 2) + 1 / 2 = y j + z j := by
    simpa only [expand_apply, Pi.add_apply] using (congrFun he j).symm
  have hcoord (j : Fin 3) : -(mollifier n).rOut < z j ∧ z j < (mollifier n).rOut := by
    have ha : |z j| < (mollifier n).rOut :=
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j : |z j| ≤ ‖z‖).trans_lt hZ
    exact abs_lt.mp ha
  constructor
  · intro j
    change margin n ≤ x j
    apply (div_le_iff₀ (factor_pos n)).mpr
    have h := (hcoord j).1
    have hy0 := hY.1 j
    change 0 ≤ y j at hy0
    have hF : factor n = 1 + 4 * (mollifier n).rOut := rfl
    nlinarith [he' j]
  · intro j
    change x j ≤ 1 - margin n
    have h := (hcoord j).2
    have hy1 := hY.2 j
    change y j ≤ 1 at hy1
    have hF : factor n = 1 + 4 * (mollifier n).rOut := rfl
    have heq : factor n * margin n = (mollifier n).rOut := by
      dsimp [margin]
      field_simp [(factor_pos n).ne']
    apply (mul_le_mul_iff_right₀ (factor_pos n)).mp
    nlinarith [he' j, heq]

theorem interiorMollify_hasCompactSupport (n : ℕ) {f : Space → ℝ}
    (hs : Function.support f ⊆ cube) : HasCompactSupport (interiorMollify n f) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (innerBox n))
    (interiorMollify_support_box n hs)

theorem interiorMollify_tsupport_subset_openCube (n : ℕ) {f : Space → ℝ}
    (hs : Function.support f ⊆ cube) : tsupport (interiorMollify n f) ⊆ openCube :=
  (closure_minimal (interiorMollify_support_box n hs) (isClosed_Icc : IsClosed (innerBox n))).trans
    (innerBox_subset_openCube n)

theorem factor_tendsto : Tendsto factor atTop (𝓝 1) := by
  change Tendsto (fun n => 1 + 4 * (mollifier n).rOut) atTop (𝓝 1)
  simpa only [mul_zero, add_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (mollifier_rOut_tendsto.const_mul 4)

theorem expand_tendsto (x : Space) : Tendsto (fun n => expand n x) atTop (𝓝 x) := by
  simpa only [expand, one_smul, sub_add_cancel] using
    (factor_tendsto.smul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x - center) atTop (𝓝 (x - center)))).add_const center

theorem interiorMollify_tendsto {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (x : Space) (hc : ContinuousAt f x) :
    Tendsto (fun n => interiorMollify n f x) atTop (𝓝 (f x)) := by
  simpa only [interiorMollify, mollify_comm] using
    ContDiffBump.convolution_tendsto_right mollifier_rOut_tendsto (Eventually.of_forall (fun _ => hf))
      ((show Tendsto f (𝓝 x) (𝓝 (f x)) from hc).comp tendsto_snd) (expand_tendsto x)

end FreudenthalSVLean.InteriorMollification
