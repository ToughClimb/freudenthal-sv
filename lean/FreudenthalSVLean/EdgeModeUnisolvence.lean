import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Structural recovery of edge-mode coefficient vectors

For the pressure trace decomposition in manuscript Lemma `edge-star`,
the two cubic or three quartic Bernstein edge modes admit explicit
coefficient recovery from two or three interior values.  The identities
hold in an arbitrary real vector space.  Hence a trace lies pointwise in
any linear compatibility subspace if and only if all its coefficient
vectors lie in that subspace.  This transfers the equal-pair and
checkerboard identities from traces to endpoint and middle coefficients
without any rank computation or additional compatibility assumption.
-/

open Set

namespace FreudenthalSVLean.EdgeModeUnisolvence

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def cubicTrace (α β : E) (s : ℝ) : E :=
  ((1 - s) ^ 2 * s) • α + ((1 - s) * s ^ 2) • β

def quarticTrace (α μ β : E) (s : ℝ) : E :=
  ((1 - s) ^ 3 * s) • α + ((1 - s) ^ 2 * s ^ 2) • μ + ((1 - s) * s ^ 3) • β

theorem cubic_first_recovery (α β : E) :
    α = (9 / 2 : ℝ) • ((2 : ℝ) • cubicTrace α β (1 / 3) - cubicTrace α β (2 / 3)) := by
  unfold cubicTrace
  module

theorem cubic_second_recovery (α β : E) :
    β = (9 / 2 : ℝ) • ((2 : ℝ) • cubicTrace α β (2 / 3) - cubicTrace α β (1 / 3)) := by
  unfold cubicTrace
  module

theorem quartic_first_recovery (α μ β : E) :
    α = (16 : ℝ) • quarticTrace α μ β (1 / 4) -
      (12 : ℝ) • quarticTrace α μ β (1 / 2) +
      (16 / 3 : ℝ) • quarticTrace α μ β (3 / 4) := by
  unfold quarticTrace
  module

theorem quartic_middle_recovery (α μ β : E) :
    μ = (40 : ℝ) • quarticTrace α μ β (1 / 2) -
      (64 / 3 : ℝ) • (quarticTrace α μ β (1 / 4) + quarticTrace α μ β (3 / 4)) := by
  unfold quarticTrace
  module

theorem quartic_last_recovery (α μ β : E) :
    β = (16 / 3 : ℝ) • quarticTrace α μ β (1 / 4) -
      (12 : ℝ) • quarticTrace α μ β (1 / 2) +
      (16 : ℝ) • quarticTrace α μ β (3 / 4) := by
  unfold quarticTrace
  module

theorem cubic_coefficients_mem (C : Submodule ℝ E) (α β : E)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, cubicTrace α β s ∈ C) : α ∈ C ∧ β ∈ C := by
  have h₁ := h (1 / 3) (by constructor <;> norm_num)
  have h₂ := h (2 / 3) (by constructor <;> norm_num)
  constructor
  · rw [cubic_first_recovery α β]
    exact C.smul_mem _ (C.sub_mem (C.smul_mem _ h₁) h₂)
  · rw [cubic_second_recovery α β]
    exact C.smul_mem _ (C.sub_mem (C.smul_mem _ h₂) h₁)

theorem quartic_coefficients_mem (C : Submodule ℝ E) (α μ β : E)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, quarticTrace α μ β s ∈ C) : α ∈ C ∧ μ ∈ C ∧ β ∈ C := by
  have h₁ := h (1 / 4) (by constructor <;> norm_num)
  have h₂ := h (1 / 2) (by constructor <;> norm_num)
  have h₃ := h (3 / 4) (by constructor <;> norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [quartic_first_recovery α μ β]
    exact C.add_mem (C.sub_mem (C.smul_mem _ h₁) (C.smul_mem _ h₂)) (C.smul_mem _ h₃)
  · rw [quartic_middle_recovery α μ β]
    exact C.sub_mem (C.smul_mem _ h₂) (C.smul_mem _ (C.add_mem h₁ h₃))
  · rw [quartic_last_recovery α μ β]
    exact C.add_mem (C.sub_mem (C.smul_mem _ h₁) (C.smul_mem _ h₂)) (C.smul_mem _ h₃)

theorem cubic_trace_mem_iff (C : Submodule ℝ E) (α β : E) :
    (∀ s ∈ Icc (0 : ℝ) 1, cubicTrace α β s ∈ C) ↔ α ∈ C ∧ β ∈ C := by
  refine ⟨cubic_coefficients_mem C α β, ?_⟩
  rintro ⟨hα, hβ⟩ s _
  exact C.add_mem (C.smul_mem _ hα) (C.smul_mem _ hβ)

theorem quartic_trace_mem_iff (C : Submodule ℝ E) (α μ β : E) :
    (∀ s ∈ Icc (0 : ℝ) 1, quarticTrace α μ β s ∈ C) ↔ α ∈ C ∧ μ ∈ C ∧ β ∈ C := by
  refine ⟨quartic_coefficients_mem C α μ β, ?_⟩
  rintro ⟨hα, hμ, hβ⟩ s _
  exact C.add_mem (C.add_mem (C.smul_mem _ hα) (C.smul_mem _ hμ)) (C.smul_mem _ hβ)

end FreudenthalSVLean.EdgeModeUnisolvence
