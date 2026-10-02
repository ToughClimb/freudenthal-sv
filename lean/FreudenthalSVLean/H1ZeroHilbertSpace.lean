import FreudenthalSVLean.H1ZeroL2Closed
import Mathlib.Topology.Sequences

/-!
# The genuine closed Hilbert space of cube H1_0 jets

For manuscript Lemma `means`, the range of the actual value-and-gradient
map is a closed subspace of four genuine L2 classes. Its closedness is
proved from strong L2 closure of weak derivatives and of the interior
smooth-approximation criterion, not assumed as a Sobolev-space axiom.
The resulting Hilbert space removes only almost-everywhere-zero data.
-/

open scoped BigOperators Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.H1ZeroL2Closed
open FreudenthalSVLean.WeakFaceTrace

noncomputable section

namespace FreudenthalSVLean.H1ZeroHilbertSpace

set_option backward.isDefEq.respectTransparency false

def jetSpace : Submodule ℝ H1JetHilbert := LinearMap.range jetLinear

theorem dataError_eq_jet_norm_square (v : h1ZeroSpace) (W : H1JetHilbert) :
    dataError v.val.1 v.val.2 (W 0) (fun i => W i.succ) = ‖jetLinear v - W‖ ^ 2 := by
  have hc (a : Fin 4) : ‖(jetLinear v - W) a‖ ^ 2 =
      ∫ x, (jetFunction v a x - W a x) ^ 2 := by
    have he : ((jetFunction_memLp v a).sub (Lp.memLp (W a))).toLp
        (jetFunction v a - (W a : Space → ℝ)) = jetComponentLinear a v - W a := by
      rw [MemLp.toLp_sub (jetFunction_memLp v a) (Lp.memLp (W a)),
        Lp.toLp_coeFn (W a) (Lp.memLp (W a))]
      rfl
    change ‖jetComponentLinear a v - W a‖ ^ 2 = _
    rw [← he, toLp_norm_square]
    rfl
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [hc]
  rw [Fin.sum_univ_succ]
  rfl

theorem jetSpace_isClosed : IsClosed (jetSpace : Set H1JetHilbert) := by
  apply IsSeqClosed.isClosed
  intro U W hU ht
  have hchoose (n : ℕ) : ∃ v : h1ZeroSpace, jetLinear v = U n := hU n
  choose v hv using hchoose
  have he : Tendsto (fun n => dataError (v n).val.1 (v n).val.2
      (W 0) (fun i => W i.succ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => ‖U n - W‖ ^ 2) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (ht.sub_const W).norm.pow 2
    simpa only [dataError_eq_jet_norm_square, hv] using hl
  have hm := inH1ZeroCube_dataError_closed (fun n => (v n).property)
    (Lp.memLp (W 0)) (fun i => Lp.memLp (W i.succ)) he
  let w : h1ZeroSpace := ⟨((W 0 : Space → ℝ), fun i => (W i.succ : Space → ℝ)), hm⟩
  refine ⟨w, ?_⟩
  apply PiLp.ext
  intro a
  change (jetFunction_memLp w a).toLp (jetFunction w a) = W a
  induction a using Fin.cases
  · exact Lp.toLp_coeFn _ _
  · exact Lp.toLp_coeFn _ _

instance : CompleteSpace jetSpace := jetSpace_isClosed.completeSpace_coe

theorem jetSpace_norm_square (v : h1ZeroSpace) :
    ‖(⟨jetLinear v, ⟨v, rfl⟩⟩ : jetSpace)‖ ^ 2 =
      (∫ x, (v.val.1 x) ^ 2) + ∑ i : Fin 3, ∫ x, (v.val.2 i x) ^ 2 :=
  jetLinear_norm_square v

end FreudenthalSVLean.H1ZeroHilbertSpace
