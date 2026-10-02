import FreudenthalSVLean.WeakVelocityGradient
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth convolution and its genuine weak-gradient formula

For the manuscript's H1_0 interface, convolution with a normalized smooth
bump is infinitely differentiable, and its actual classical partial
derivative equals convolution with the supplied genuine weak derivative.
The latter identity is proved by testing integration by parts against
the translated reflected bump, not by assuming a formal differentiation
rule for nonsmooth functions.  Support and L2 approximation estimates are
separate results; no density or boundary assertion is inferred here.
-/

open scoped ContDiff Convolution NNReal
open MeasureTheory ContinuousLinearMap
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakVelocityGradient

noncomputable section

namespace FreudenthalSVLean.WeakGradientMollification

set_option backward.isDefEq.respectTransparency false

def mollify (b : ContDiffBump (0 : Space)) (f : Space → ℝ) : Space → ℝ :=
  f ⋆[lsmul ℝ ℝ, volume] b.normed volume

theorem mollify_comm (b : ContDiffBump (0 : Space)) (f : Space → ℝ) :
    mollify b f = b.normed volume ⋆[lsmul ℝ ℝ, volume] f := by
  funext x
  rw [mollify, convolution_eq_swap]
  simp only [convolution_def, lsmul_apply, smul_eq_mul, mul_comm]

theorem mollify_contDiff (b : ContDiffBump (0 : Space)) {f : Space → ℝ}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (mollify b f) :=
  b.hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ) hf b.contDiff_normed

theorem reflected_bump_contDiff (b : ContDiffBump (0 : Space)) (x : Space) :
    ContDiff ℝ ∞ (fun y : Space => b.normed volume (x - y)) :=
  b.contDiff_normed.comp (contDiff_const.sub contDiff_id)

theorem reflected_bump_hasCompactSupport (b : ContDiffBump (0 : Space)) (x : Space) :
    HasCompactSupport (fun y : Space => b.normed volume (x - y)) := by
  exact b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)

theorem reflected_bump_partial (b : ContDiffBump (0 : Space)) (x y : Space) (i : Fin 3) :
    fderiv ℝ (fun z : Space => b.normed volume (x - z)) y (Pi.single i 1) =
      -fderiv ℝ (b.normed volume) (x - y) (Pi.single i 1) := by
  have ht : HasFDerivAt (fun z : Space => x - z) (-ContinuousLinearMap.id ℝ Space) y := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using!
      (hasFDerivAt_const x y).sub (hasFDerivAt_id y)
  have hb : DifferentiableAt ℝ (b.normed volume) (x - y) :=
    ((b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable
      (by simp)).differentiableAt
  have hd : HasFDerivAt (fun z : Space => b.normed volume (x - z))
      ((fderiv ℝ (b.normed volume) (x - y)).comp (-ContinuousLinearMap.id ℝ Space)) y := by
    simpa only [Function.comp_def] using! hb.hasFDerivAt.comp y ht
  rw [hd.fderiv]
  simp

theorem mollify_partial (b : ContDiffBump (0 : Space)) {f g : Space → ℝ}
    (hf : LocallyIntegrable f volume) (i : Fin 3) (hw : HasWeakPartial f g i) (x : Space) :
    fderiv ℝ (mollify b f) x (Pi.single i 1) = mollify b g x := by
  have hd := b.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (lsmul ℝ ℝ) hf ((b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).of_le (by simp)) x
  change fderiv ℝ (f ⋆[lsmul ℝ ℝ, volume] b.normed volume) x (Pi.single i 1) = _
  rw [hd.fderiv, convolution_precompR_apply (lsmul ℝ ℝ) hf
    (b.hasCompactSupport_normed.fderiv ℝ)
    ((b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).continuous_fderiv (by simp))]
  have ht := hw (fun y : Space => b.normed volume (x - y))
    (reflected_bump_contDiff b x) (reflected_bump_hasCompactSupport b x)
  simp only [reflected_bump_partial b x, mul_neg, integral_neg, neg_neg] at ht
  simpa only [mollify, convolution_def, lsmul_apply, smul_eq_mul] using ht.symm

end FreudenthalSVLean.WeakGradientMollification
