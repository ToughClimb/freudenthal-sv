import FreudenthalSVLean.ConformingH1Zero

/-!
# Linearity of the actual L2 weak-gradient interface

For the fixed linear mean-lift operator in manuscript Lemma `means`,
weak derivatives are closed under addition and real scalar multiplication.
The proof expands the actual distributional test integrals, with all
integrability supplied by the genuine L2 hypotheses.  This connects
linear constructions on Sobolev data to the established actual-function
weak-gradient definition and uses no assumed weak-derivative rules.
-/

open scoped ContDiff
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakVelocityGradient

noncomputable section

namespace FreudenthalSVLean.WeakGradientLinearity

set_option backward.isDefEq.respectTransparency false

theorem test_partial_memLp {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (i : Fin 3) :
    MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2 volume := by
  have hd : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun x => fderiv ℝ φ x (Pi.single i 1)) := by
    simpa only [Function.comp_def] using (hc.fderiv ℝ).comp_left
      (g := fun L : Space →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)
  exact hd.memLp_of_hasCompactSupport hs

theorem hasWeakPartial_add {f F g G : Space → ℝ} {i : Fin 3}
    (hf : MemLp f 2 volume) (hF : MemLp F 2 volume)
    (hg : MemLp g 2 volume) (hG : MemLp G 2 volume)
    (hw : HasWeakPartial f g i) (hW : HasWeakPartial F G i) :
    HasWeakPartial (fun x => f x + F x) (fun x => g x + G x) i := by
  intro φ hφ hc
  have hφ₂ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hφd := test_partial_memLp hφ hc i
  have ig : Integrable (fun x => g x * φ x) := by
    simpa only [Pi.mul_apply] using! hg.integrable_mul hφ₂
  have iG : Integrable (fun x => G x * φ x) := by
    simpa only [Pi.mul_apply] using! hG.integrable_mul hφ₂
  have ifd : Integrable (fun x => f x * fderiv ℝ φ x (Pi.single i 1)) := by
    simpa only [Pi.mul_apply] using! hf.integrable_mul hφd
  have iFd : Integrable (fun x => F x * fderiv ℝ φ x (Pi.single i 1)) := by
    simpa only [Pi.mul_apply] using! hF.integrable_mul hφd
  simp only [add_mul]
  rw [integral_add ig iG, integral_add ifd iFd, hw φ hφ hc, hW φ hφ hc]
  ring

theorem hasWeakPartial_const_mul {f g : Space → ℝ} {i : Fin 3}
    (hw : HasWeakPartial f g i) (c : ℝ) :
    HasWeakPartial (fun x => c * f x) (fun x => c * g x) i := by
  intro φ hφ hc
  simp only [mul_assoc, integral_const_mul, hw φ hφ hc]
  ring

theorem hasL2WeakGradient_zero :
    HasL2WeakGradient (fun _ : Space => 0) (fun (_ : Fin 3) (_ : Space) => 0) := by
  refine ⟨MemLp.zero', fun _ => ⟨MemLp.zero', ?_⟩⟩
  intro φ _ _
  simp

theorem hasL2WeakGradient_add {f F : Space → ℝ} {g G : Fin 3 → Space → ℝ}
    (hf : HasL2WeakGradient f g) (hF : HasL2WeakGradient F G) :
    HasL2WeakGradient (fun x => f x + F x) (fun j x => g j x + G j x) := by
  refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
  · simpa only [Pi.add_apply] using! hf.1.add hF.1
  · simpa only [Pi.add_apply] using! (hf.2 j).1.add (hF.2 j).1
  · exact hasWeakPartial_add hf.1 hF.1 (hf.2 j).1 (hF.2 j).1 (hf.2 j).2 (hF.2 j).2

theorem hasL2WeakGradient_const_mul {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : HasL2WeakGradient f g) (c : ℝ) :
    HasL2WeakGradient (fun x => c * f x) (fun j x => c * g j x) := by
  refine ⟨?_, fun j => ⟨?_, hasWeakPartial_const_mul (hf.2 j).2 c⟩⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using! hf.1.const_smul c
  · simpa only [Pi.smul_apply, smul_eq_mul] using! (hf.2 j).1.const_smul c

end FreudenthalSVLean.WeakGradientLinearity
