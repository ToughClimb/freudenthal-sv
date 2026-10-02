import FreudenthalSVLean.WeakH1ZeroCubeEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Genuine Hilbert L2 jets of weak H1_0 data

For the continuous divergence step in manuscript Lemma `means`, actual
weak H1_0 data have a fixed linear map into the Hilbert product of four
actual L2 classes: the value and its three weak derivatives. The squared
Hilbert norm is exactly the genuine full H1 energy, and the proved cube
Poincare estimate bounds it by five times actual gradient energy. The
kernel is characterized by actual almost-everywhere equality to zero;
pointwise injectivity of arbitrary function representatives is not claimed.
This supplies a genuine normed interface, not a coefficient seminorm or
an assumed Sobolev-space identification.
-/

open scoped BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.WeakH1ZeroCubeEnergy

noncomputable section

namespace FreudenthalSVLean.H1ZeroL2Jet

set_option backward.isDefEq.respectTransparency false

abbrev ScalarL2 := Lp ℝ 2 (volume : Measure Space)
abbrev H1JetHilbert := PiLp 2 (fun _ : Fin 4 => ScalarL2)

def jetFunction (v : h1ZeroSpace) : Fin 4 → Space → ℝ := Fin.cases v.val.1 v.val.2

theorem jetFunction_memLp (v : h1ZeroSpace) (a : Fin 4) : MemLp (jetFunction v a) 2 volume := by
  induction a using Fin.cases
  · exact v.property.1.1
  · exact (v.property.1.2 _).1

def jetFunctionLinear : h1ZeroSpace →ₗ[ℝ] (Fin 4 → Space → ℝ) where
  toFun := jetFunction
  map_add' v w := by
    funext a
    induction a using Fin.cases <;> rfl
  map_smul' c v := by
    funext a
    induction a using Fin.cases <;> rfl

def jetComponentLinear (a : Fin 4) : h1ZeroSpace →ₗ[ℝ] ScalarL2 where
  toFun v := (jetFunction_memLp v a).toLp (jetFunction v a)
  map_add' v w := by
    have he := congrFun (jetFunctionLinear.map_add v w) a
    exact (MemLp.toLp_congr (jetFunction_memLp (v + w) a)
      ((jetFunction_memLp v a).add (jetFunction_memLp w a))
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add (jetFunction_memLp v a) (jetFunction_memLp w a))
  map_smul' c v := by
    have he := congrFun (jetFunctionLinear.map_smul c v) a
    exact (MemLp.toLp_congr (jetFunction_memLp (c • v) a)
      ((jetFunction_memLp v a).const_smul c)
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul c (jetFunction_memLp v a))

def jetLinear : h1ZeroSpace →ₗ[ℝ] H1JetHilbert where
  toFun v := WithLp.toLp 2 (fun a => jetComponentLinear a v)
  map_add' v w := by
    apply PiLp.ext
    intro a
    exact (jetComponentLinear a).map_add v w
  map_smul' c v := by
    apply PiLp.ext
    intro a
    exact (jetComponentLinear a).map_smul c v

theorem jetLinear_apply (v : h1ZeroSpace) (a : Fin 4) :
    jetLinear v a = (jetFunction_memLp v a).toLp (jetFunction v a) := rfl

theorem jetLinear_norm_square (v : h1ZeroSpace) : ‖jetLinear v‖ ^ 2 =
    (∫ x, (v.val.1 x) ^ 2) + ∑ i : Fin 3, ∫ x, (v.val.2 i x) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [jetLinear_apply, toLp_norm_square]
  rw [Fin.sum_univ_succ]
  rfl

theorem jetLinear_gradient_bound (v : h1ZeroSpace) :
    ‖jetLinear v‖ ^ 2 ≤ 5 * ∑ i : Fin 3, ∫ x, (v.val.2 i x) ^ 2 := by
  rw [jetLinear_norm_square]
  exact weak_full_h1_energy_bound v.property

theorem jetComponent_eq_zero_iff (v : h1ZeroSpace) (a : Fin 4) :
    jetComponentLinear a v = 0 ↔ jetFunction v a =ᵐ[volume] (0 : Space → ℝ) := by
  constructor
  · intro he
    exact (MemLp.coeFn_toLp (jetFunction_memLp v a)).symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp he)
  · intro he
    have hzero : MemLp (0 : Space → ℝ) 2 volume := MemLp.zero
    exact (MemLp.toLp_congr (jetFunction_memLp v a) hzero he).trans (MemLp.toLp_zero hzero)

theorem jetLinear_eq_zero_iff (v : h1ZeroSpace) : jetLinear v = 0 ↔
    v.val.1 =ᵐ[volume] (0 : Space → ℝ) ∧
      ∀ i : Fin 3, v.val.2 i =ᵐ[volume] (0 : Space → ℝ) := by
  constructor
  · intro he
    have hc (a : Fin 4) : jetComponentLinear a v = 0 := by
      have ht := congrArg (fun z : H1JetHilbert => z a) he
      exact ht
    exact ⟨(jetComponent_eq_zero_iff v 0).mp (hc 0),
      fun i => (jetComponent_eq_zero_iff v i.succ).mp (hc i.succ)⟩
  · rintro ⟨hf, hg⟩
    apply PiLp.ext
    intro a
    apply (jetComponent_eq_zero_iff v a).mpr
    induction a using Fin.cases
    · exact hf
    · exact hg _

end FreudenthalSVLean.H1ZeroL2Jet
