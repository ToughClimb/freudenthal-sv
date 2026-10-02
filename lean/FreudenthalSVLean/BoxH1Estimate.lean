import FreudenthalSVLean.IntervalH1Estimate
import FreudenthalSVLean.SmoothChainGauss
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local Cartesian-box estimates for stable interpolation

The local estimate needed in manuscript Lemma `means` and equation `SZ`
is derived from genuine coordinate averages on Cartesian boxes.  The
coordinate splitting preserves Lebesgue measure, and every integral
below is the actual restricted-volume integral.  Coordinate averaging
is an L2 contraction; the interval Poincare estimate bounds the error
in one coordinate by its derivative energy.  These are analytic inputs
to a stable interpolant, not a postulated interpolant or mean lift.
-/

open scoped BigOperators Topology
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ChainFiberIntegration
open FreudenthalSVLean.SmoothChainGauss
open FreudenthalSVLean.IntervalH1Estimate

noncomputable section

namespace FreudenthalSVLean.BoxH1Estimate

set_option backward.isDefEq.respectTransparency false

def boxSet (a b : ℝ) : Set Space := Icc (fun _ => a) (fun _ => b)

def transverseBox (a b : ℝ) : Set FacePoint := Icc (a, a) (b, b)

theorem coordinateFiber_box_mem (j : Fin 3) (p : FacePoint) (s a b : ℝ) :
    coordinateFiber j p s ∈ boxSet a b ↔
      s ∈ Icc a b ∧ p ∈ transverseBox a b := by
  simp only [boxSet, transverseBox, mem_Icc, Pi.le_def, coordinateFiber,
    Fin.forall_iff_succAbove j, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Fin.forall_fin_two, Prod.le_def,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

theorem boxSet_split_preimage (j : Fin 3) (a b : ℝ) :
    boxSet a b = (splitCoordinate j) ⁻¹' (Icc a b ×ˢ transverseBox a b) := by
  ext x
  have ht := coordinateFiber_box_mem j ((splitCoordinate j x).2)
    ((splitCoordinate j x).1) a b
  rw [← splitCoordinate_symm, Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at ht
  exact ht

theorem box_integral_fiber (j : Fin 3) (a b : ℝ) {f : Space → ℝ}
    (hf : Continuous f) :
    (∫ x in boxSet a b, f x) =
      ∫ p in transverseBox a b, ∫ s in Icc a b, f (coordinateFiber j p s) := by
  have hc : Continuous (fun z : Point => f ((splitCoordinate j).symm z)) :=
    hf.comp (coordinateFiber_joint_continuous j)
  have hi : Integrable (fun z : Point => f ((splitCoordinate j).symm z))
      ((volume.restrict (Icc a b)).prod (volume.restrict (transverseBox a b))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have he := (splitCoordinate_preserving j).setIntegral_preimage_emb
    (splitCoordinate j).measurableEmbedding (fun z => f ((splitCoordinate j).symm z))
    (Icc a b ×ˢ transverseBox a b)
  simp only [MeasurableEquiv.symm_apply_apply] at he
  rw [boxSet_split_preimage j, he]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm _ hi

theorem fiberIntegral_continuous (j : Fin 3) (a b : ℝ) {f : Space → ℝ}
    (hf : Continuous f) :
    Continuous (fun p : FacePoint => ∫ s in Icc a b, f (coordinateFiber j p s)) := by
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hf.comp ((coordinateFiber_joint_continuous j).comp continuous_swap)

def coordinateAverage (a b : ℝ) (j : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  intervalMean a b (fun s => f (Function.update x j s))

theorem coordinateAverage_continuous (a b : ℝ) (j : Fin 3) {f : Space → ℝ}
    (hf : Continuous f) : Continuous (coordinateAverage a b j f) := by
  have hc : Continuous (fun z : Space × ℝ => f (Function.update z.1 j z.2)) :=
    hf.comp (continuous_fst.update j continuous_snd)
  exact (continuous_parametric_integral_of_continuous hc isCompact_Icc).const_mul _

theorem coordinateAverage_fiber (a b : ℝ) (j : Fin 3) (f : Space → ℝ)
    (p : FacePoint) (s : ℝ) :
    coordinateAverage a b j f (coordinateFiber j p s) =
      intervalMean a b (fun t => f (coordinateFiber j p t)) := by
  simp only [coordinateAverage, coordinateFiber, Fin.update_insertNth]

theorem coordinateAverage_sub (a b : ℝ) (j : Fin 3) {f g : Space → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    coordinateAverage a b j (fun x => f x - g x) =
      fun x => coordinateAverage a b j f x - coordinateAverage a b j g x := by
  funext x
  exact interval_mean_sub
    (hf.comp (continuous_const.update j continuous_id))
    (hg.comp (continuous_const.update j continuous_id)) a b

theorem coordinateAverage_contract {a b : ℝ} (hab : a < b)
    (j : Fin 3) {f : Space → ℝ} (hf : Continuous f) :
    (∫ x in boxSet a b, (coordinateAverage a b j f x) ^ 2) ≤
      ∫ x in boxSet a b, (f x) ^ 2 := by
  rw [box_integral_fiber j a b (f := fun x => (coordinateAverage a b j f x) ^ 2)
      ((coordinateAverage_continuous a b j hf).pow 2),
    box_integral_fiber j a b (f := fun x => (f x) ^ 2) (hf.pow 2)]
  simp_rw [coordinateAverage_fiber, setIntegral_const,
    Real.volume_real_Icc_of_le hab.le, smul_eq_mul]
  have hm : Continuous (fun p : FacePoint =>
      intervalMean a b (fun t => f (coordinateFiber j p t))) :=
    (fiberIntegral_continuous j a b hf).const_mul _
  apply setIntegral_mono_on
    ((hm.pow 2).const_mul (b - a)).continuousOn.integrableOn_Icc
    (fiberIntegral_continuous j a b (hf.pow 2)).continuousOn.integrableOn_Icc
    measurableSet_Icc
  intro p _
  exact interval_mean_square_bound (hf.comp (coordinateFiber_continuous j p)) hab

theorem fiber_contDiff {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (j : Fin 3) (p : FacePoint) :
    ContDiff ℝ 1 (fun s => f (coordinateFiber j p s)) := by
  have he : coordinateFiber j p = Function.update (coordinateFiber j p 0) j := by
    funext s
    simp only [coordinateFiber, Fin.update_insertNth]
  rw [he]
  exact hf.comp (contDiff_update 1 (coordinateFiber j p 0) j)

theorem deriv_fiber {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (j : Fin 3) (p : FacePoint) (s : ℝ) :
    deriv (fun t => f (coordinateFiber j p t)) s =
      fderiv ℝ f (coordinateFiber j p s) (Pi.single j 1) := by
  have hd : HasDerivAt (fun t => f (coordinateFiber j p t))
      (fderiv ℝ f (coordinateFiber j p s) (Pi.single j 1)) s :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt s
      (coordinateFiber_hasDerivAt j p s)
  exact hd.deriv

theorem coordinate_error_bound {a b : ℝ} (hab : a < b)
    {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    (∫ x in boxSet a b, (f x - coordinateAverage a b j f x) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single j 1)) ^ 2 := by
  have he : Continuous (fun x => (f x - coordinateAverage a b j f x) ^ 2) :=
    (hf.continuous.sub (coordinateAverage_continuous a b j hf.continuous)).pow 2
  have hg : Continuous (fun x => (fderiv ℝ f x (Pi.single j 1)) ^ 2) :=
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  rw [box_integral_fiber j a b he, box_integral_fiber j a b hg,
    ← integral_const_mul]
  apply setIntegral_mono_on
    (fiberIntegral_continuous j a b he).continuousOn.integrableOn_Icc
    ((fiberIntegral_continuous j a b hg).const_mul ((b - a) ^ 2)).continuousOn.integrableOn_Icc
    measurableSet_Icc
  intro p _
  simpa only [coordinateAverage_fiber, deriv_fiber hf] using
    interval_mean_poincare (fiber_contDiff hf j p) hab

theorem transverseBox_product (a b : ℝ) :
    transverseBox a b = Icc a b ×ˢ Icc a b := by
  ext p
  simp only [transverseBox, mem_Icc, Prod.le_def, mem_prod]
  tauto

theorem box_integral_coordinates (a b : ℝ) {f : Space → ℝ} (hf : Continuous f) :
    (∫ x in boxSet a b, f x) =
      ∫ s₀ in Icc a b, ∫ s₁ in Icc a b, ∫ s₂ in Icc a b, f ![s₀, s₁, s₂] := by
  have he := (splitCoordinate_preserving 0).setIntegral_preimage_emb
    (splitCoordinate 0).measurableEmbedding (fun z => f ((splitCoordinate 0).symm z))
    (Icc a b ×ˢ transverseBox a b)
  simp only [MeasurableEquiv.symm_apply_apply] at he
  rw [boxSet_split_preimage 0, he, Measure.volume_eq_prod]
  have hc : Continuous (fun z : Point => f ((splitCoordinate 0).symm z)) :=
    hf.comp (coordinateFiber_joint_continuous 0)
  have hi : IntegrableOn (fun z : Point => f ((splitCoordinate 0).symm z))
      (Icc a b ×ˢ transverseBox a b) (volume.prod volume) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s₀ _
  simp only [splitCoordinate_symm, coordinateFiber_zero]
  rw [transverseBox_product, Measure.volume_eq_prod]
  apply setIntegral_prod
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact (hf.comp (by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop)).continuousOn

/-- The actual volume average on a nondegenerate Cartesian cube. -/
def boxMean (a b : ℝ) (f : Space → ℝ) : ℝ :=
  ((b - a)⁻¹) ^ 3 * ∫ x in boxSet a b, f x

theorem update_coordinates (x : Space) (s₀ s₁ s₂ : ℝ) :
    Function.update (Function.update (Function.update x 0 s₀) 1 s₁) 2 s₂ =
      ![s₀, s₁, s₂] := by
  ext i
  fin_cases i <;> norm_num [Function.update_apply, Fin.ext_iff, -Fin.val_eq_zero_iff]

theorem three_coordinate_average {f : Space → ℝ} (hf : Continuous f) (a b : ℝ)
    (x : Space) :
    coordinateAverage a b 0 (coordinateAverage a b 1 (coordinateAverage a b 2 f)) x =
      boxMean a b f := by
  simp only [coordinateAverage, intervalMean, update_coordinates, integral_const_mul]
  rw [boxMean, box_integral_coordinates a b hf]
  ring

theorem three_square_bound (r s t : ℝ) :
    (r + s + t) ^ 2 ≤ 3 * (r ^ 2 + s ^ 2 + t ^ 2) := by
  nlinarith [sq_nonneg (r - s), sq_nonneg (r - t), sq_nonneg (s - t)]

/-- A local Poincare estimate with the square of the actual box side length. -/
theorem box_mean_poincare {a b : ℝ} (hab : a < b) {f : Space → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (∫ x in boxSet a b, (f x - boxMean a b f) ^ 2) ≤
      3 * (b - a) ^ 2 *
        ∑ j : Fin 3, ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single j 1)) ^ 2 := by
  let d₀ : Space → ℝ := fun x => f x - coordinateAverage a b 0 f x
  let d₁ : Space → ℝ := fun x => f x - coordinateAverage a b 1 f x
  let d₂ : Space → ℝ := fun x => f x - coordinateAverage a b 2 f x
  let e₁ := coordinateAverage a b 0 d₁
  let e₂ := coordinateAverage a b 0 (coordinateAverage a b 1 d₂)
  have hA (j : Fin 3) : Continuous (coordinateAverage a b j f) :=
    coordinateAverage_continuous a b j hf.continuous
  have hd₀ : Continuous d₀ := hf.continuous.sub (hA 0)
  have hd₁ : Continuous d₁ := hf.continuous.sub (hA 1)
  have hd₂ : Continuous d₂ := hf.continuous.sub (hA 2)
  have he₁ : Continuous e₁ := coordinateAverage_continuous a b 0 hd₁
  have he₂ : Continuous e₂ :=
    coordinateAverage_continuous a b 0 (coordinateAverage_continuous a b 1 hd₂)
  have he₁_eq : e₁ = fun x => coordinateAverage a b 0 f x -
      coordinateAverage a b 0 (coordinateAverage a b 1 f) x := by
    exact coordinateAverage_sub a b 0 hf.continuous (hA 1)
  have he₂_eq : e₂ = fun x =>
      coordinateAverage a b 0 (coordinateAverage a b 1 f) x - boxMean a b f := by
    dsimp only [e₂, d₂]
    rw [coordinateAverage_sub a b 1 hf.continuous (hA 2),
      coordinateAverage_sub a b 0 (hA 1)
        (coordinateAverage_continuous a b 1 (hA 2))]
    funext x
    rw [three_coordinate_average hf.continuous]
  have hs (x : Space) : f x - boxMean a b f = d₀ x + e₁ x + e₂ x := by
    rw [he₁_eq, he₂_eq]
    dsimp only [d₀]
    ring
  have h₀ : (∫ x in boxSet a b, (d₀ x) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 0 1)) ^ 2 :=
    coordinate_error_bound hab hf 0
  have h₁ : (∫ x in boxSet a b, (e₁ x) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 1 1)) ^ 2 :=
    (coordinateAverage_contract hab 0 hd₁).trans (coordinate_error_bound hab hf 1)
  have h₂ : (∫ x in boxSet a b, (e₂ x) ^ 2) ≤
      (b - a) ^ 2 * ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 2 1)) ^ 2 :=
    (coordinateAverage_contract hab 0 (coordinateAverage_continuous a b 1 hd₂)).trans
      ((coordinateAverage_contract hab 1 hd₂).trans (coordinate_error_bound hab hf 2))
  have hi₀ : IntegrableOn (fun x => (d₀ x) ^ 2) (boxSet a b) :=
    (hd₀.pow 2).continuousOn.integrableOn_Icc
  have hi₁ : IntegrableOn (fun x => (e₁ x) ^ 2) (boxSet a b) :=
    (he₁.pow 2).continuousOn.integrableOn_Icc
  have hi₂ : IntegrableOn (fun x => (e₂ x) ^ 2) (boxSet a b) :=
    (he₂.pow 2).continuousOn.integrableOn_Icc
  have hiSum : IntegrableOn (fun x => (d₀ x) ^ 2 + (e₁ x) ^ 2 + (e₂ x) ^ 2)
      (boxSet a b) := by
    simpa only [Pi.add_apply] using! (hi₀.add hi₁).add hi₂
  have hiErr : IntegrableOn (fun x => (f x - boxMean a b f) ^ 2) (boxSet a b) :=
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc
  have hI : (∫ x in boxSet a b, (f x - boxMean a b f) ^ 2) ≤
      3 * ((∫ x in boxSet a b, (d₀ x) ^ 2) +
        (∫ x in boxSet a b, (e₁ x) ^ 2) + ∫ x in boxSet a b, (e₂ x) ^ 2) := by
    calc
      _ ≤ ∫ x in boxSet a b, 3 * ((d₀ x) ^ 2 + (e₁ x) ^ 2 + (e₂ x) ^ 2) :=
        setIntegral_mono_on hiErr (hiSum.const_mul 3) measurableSet_Icc
          (fun x _ => by rw [hs]; exact three_square_bound _ _ _)
      _ = _ := by
        have h01 : (∫ x in boxSet a b, (d₀ x) ^ 2 + (e₁ x) ^ 2) =
            (∫ x in boxSet a b, (d₀ x) ^ 2) + ∫ x in boxSet a b, (e₁ x) ^ 2 := by
          simpa only [Pi.add_apply] using! integral_add hi₀ hi₁
        have h012 : (∫ x in boxSet a b, (d₀ x) ^ 2 + (e₁ x) ^ 2 + (e₂ x) ^ 2) =
            (∫ x in boxSet a b, (d₀ x) ^ 2 + (e₁ x) ^ 2) +
              ∫ x in boxSet a b, (e₂ x) ^ 2 := by
          simpa only [Pi.add_apply] using! integral_add (hi₀.add hi₁) hi₂
        rw [integral_const_mul, h012, h01]
  have hsum : (∑ j : Fin 3, ∫ x in boxSet a b,
      (fderiv ℝ f x (Pi.single j 1)) ^ 2) =
      (∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 0 1)) ^ 2) +
      (∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 1 1)) ^ 2) +
      ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 2 1)) ^ 2 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 0 1)) ^ 2) +
      ((∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 1 1)) ^ 2) +
        ∫ x in boxSet a b, (fderiv ℝ f x (Pi.single 2 1)) ^ 2) = _
    ring
  rw [hsum]
  nlinarith

end FreudenthalSVLean.BoxH1Estimate
