import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.DenselyOrdered

/-!
# One-sided calculus on a finite closed interval cover

For the manuscript's piecewise-polynomial Sobolev interface, a finite
closed order-connected cover of a real interval supplies, at each
nonterminal point, one owner of a full right subinterval.  A continuous
function agreeing there with differentiable local functions consequently
inherits their right derivatives and derivative norm bound.  The fencing
theorem gives the global difference estimate without differentiability at
the joining points.  No almost-everywhere differentiability implication
is used here.
-/

open scoped Topology
open Set

noncomputable section

namespace FreudenthalSVLean.FiniteClosedIntervalGluing

theorem right_owner {I : Type*} [Finite I] (s : I → Set ℝ)
    (hclosed : ∀ i, IsClosed (s i)) (hord : ∀ i, OrdConnected (s i))
    (a b : ℝ) (hcover : Icc a b ⊆ ⋃ i, s i) (x : ℝ) (hx : x ∈ Ico a b) :
    ∃ (i : I) (y : ℝ), x < y ∧ x ∈ s i ∧ Icc x y ⊆ s i := by
  classical
  have hsub : Ioc x b ⊆ ⋃ i, s i ∩ Ioc x b := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hx.1.trans hz.1.le, hz.2⟩)
    exact mem_iUnion.mpr ⟨i, hi, hz⟩
  have hxc : x ∈ closure (Ioc x b) := by
    rw [closure_Ioc hx.2.ne]
    exact ⟨le_rfl, hx.2.le⟩
  have hc := closure_mono hsub hxc
  rw [closure_iUnion_of_finite] at hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  have hxi : x ∈ s i := by
    have hm := closure_mono (inter_subset_left : s i ∩ Ioc x b ⊆ s i) hi
    simpa only [(hclosed i).closure_eq] using hm
  obtain ⟨y, hys, hxy, hyb⟩ := (closure_nonempty_iff.mp ⟨x, hi⟩)
  exact ⟨i, y, hxy, hxi, (hord i).out hxi hys⟩

/-- Continuous finite piecewise-smooth functions inherit a global
derivative norm estimate even at nondifferentiable joining points. -/
theorem norm_difference_bound {I : Type*} [Finite I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : I → Set ℝ) (hclosed : ∀ i, IsClosed (s i))
    (hord : ∀ i, OrdConnected (s i)) (a b : ℝ) (hab : a ≤ b)
    (hcover : Icc a b ⊆ ⋃ i, s i) (f : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (g dg : I → ℝ → E)
    (hmatch : ∀ i, EqOn f (g i) (s i))
    (hd : ∀ i x, x ∈ s i → x ∈ Ico a b → HasDerivAt (g i) (dg i x) x)
    (C : ℝ) (hbound : ∀ i x, x ∈ s i → x ∈ Ico a b → ‖dg i x‖ ≤ C) :
    ‖f b - f a‖ ≤ C * (b - a) := by
  classical
  have hex (x : ℝ) : ∃ d : E, x ∈ Ico a b →
      HasDerivWithinAt f d (Ici x) x ∧ ‖d‖ ≤ C := by
    by_cases hx : x ∈ Ico a b
    · obtain ⟨i, y, hxy, hxi, hsub⟩ := right_owner s hclosed hord a b hcover x hx
      have he : f =ᶠ[𝓝[Ici x] x] g i := by
        filter_upwards [Icc_mem_nhdsGE hxy] with z hz
        exact hmatch i (hsub hz)
      refine ⟨dg i x, ?_⟩
      intro _
      exact ⟨((hd i x hxi hx).hasDerivWithinAt).congr_of_eventuallyEq he (hmatch i hxi),
        hbound i x hxi hx⟩
    · exact ⟨0, fun h => False.elim (hx h)⟩
  choose d hd' using hex
  exact norm_image_sub_le_of_norm_deriv_right_le_segment hf
    (fun x hx => (hd' x hx).1) (fun x hx => (hd' x hx).2) b ⟨hab, le_rfl⟩

end FreudenthalSVLean.FiniteClosedIntervalGluing
