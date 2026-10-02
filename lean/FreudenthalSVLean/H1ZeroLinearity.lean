import FreudenthalSVLean.H1ApproximationLinearity
import FreudenthalSVLean.WeakLinearFaceTrace

/-!
# A proved real vector space of genuine H1_0 cube data

For the continuous divergence step of manuscript Lemma `means`, the
actual weak-gradient and smooth compact-support closure criterion is
closed under addition and scalar multiplication. One common sequence
of genuine infinitely smooth interior-supported functions supplies each
linear combination. These statements establish the actual H1_0 vector
space, not merely an assumed algebra on polynomial or coefficient data.
-/

open scoped BigOperators ContDiff Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.H1ApproximationLinearity
open FreudenthalSVLean.WeakGradientLinearity

noncomputable section

namespace FreudenthalSVLean.H1ZeroLinearity

set_option backward.isDefEq.respectTransparency false

theorem inH1ZeroCube_add {f F : Space → ℝ} {g G : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (hF : InH1ZeroCube F G) :
    InH1ZeroCube (fun x => f x + F x) (fun j x => g j x + G j x) := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  obtain ⟨hW, v, hv, hd⟩ := hF
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hb : SmoothH1Approximation F G v :=
    ⟨hW, fun n => (hv n).1.of_le (by simp), fun n => (hv n).2.2.2.1,
      fun n => (hv n).2.2.2.2, hd⟩
  have hab := smoothH1Approximation_add ha hb
  refine ⟨hab.weak_gradient, fun n x => u n x + v n x, ?_, hab.convergence⟩
  intro n
  refine ⟨(hu n).1.add (hv n).1, ?_, ?_, hab.memLp n, hab.partial_memLp n⟩
  · simpa only [Pi.add_apply] using! (hu n).2.1.add (hv n).2.1
  · exact (tsupport_add (u n) (v n)).trans
      (Set.union_subset (hu n).2.2.1 (hv n).2.2.1)

theorem inH1ZeroCube_const_mul {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) (c : ℝ) :
    InH1ZeroCube (fun x => c * f x) (fun j x => c * g j x) := by
  obtain ⟨hw, u, hu, hc⟩ := hf
  have ha : SmoothH1Approximation f g u :=
    ⟨hw, fun n => (hu n).1.of_le (by simp), fun n => (hu n).2.2.2.1,
      fun n => (hu n).2.2.2.2, hc⟩
  have hab := smoothH1Approximation_const_mul ha c
  refine ⟨hab.weak_gradient, fun n x => c * u n x, ?_, hab.convergence⟩
  intro n
  refine ⟨by simpa only [Pi.smul_apply, smul_eq_mul] using! (hu n).1.const_smul c,
    (hu n).2.1.mul_left, ?_, hab.memLp n, hab.partial_memLp n⟩
  exact tsupport_mul_subset_right.trans (hu n).2.2.1

theorem inH1ZeroCube_zero :
    InH1ZeroCube (fun _ : Space => 0) (fun (_ : Fin 3) (_ : Space) => 0) := by
  refine ⟨hasL2WeakGradient_zero, fun (_ : ℕ) (_ : Space) => 0, ?_, ?_⟩
  · intro n
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_, MemLp.zero, ?_⟩
    · simp
    · intro j
      simp
  · simp

def h1ZeroSpace : Submodule ℝ H1Data where
  carrier := {v | InH1ZeroCube v.1 v.2}
  zero_mem' := inH1ZeroCube_zero
  add_mem' := by
    intro v w hv hw
    exact inH1ZeroCube_add hv hw
  smul_mem' := by
    intro c v hv
    exact inH1ZeroCube_const_mul hv c

theorem h1ZeroSpace_le_smoothH1Space : h1ZeroSpace ≤ smoothH1Space := by
  intro v hv
  exact inH1ZeroCube_has_smoothApproximation hv

def smoothInclusion : h1ZeroSpace →ₗ[ℝ] smoothH1Space :=
  h1ZeroSpace.inclusion h1ZeroSpace_le_smoothH1Space

end FreudenthalSVLean.H1ZeroLinearity
