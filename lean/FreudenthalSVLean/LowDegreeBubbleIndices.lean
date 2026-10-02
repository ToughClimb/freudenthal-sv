import FreudenthalSVLean.FaceBubbleMean

/-!
# Structural classification of low-degree interior and face indices

The dimension calculation in manuscript Lemma `bubble` uses four cubic
face monomials and twelve quartic face monomials together with the quartic
interior bubble.  This module proves the multi-index classification
analytically.  Subtracting the indicator of the support leaves degree zero
or one, and a nonnegative multi-index of degree one is a single variable.
No degree-specific table enumeration is used in these proofs.
-/

open scoped BigOperators
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FaceBubbleMean

noncomputable section

namespace FreudenthalSVLean.LowDegreeBubbleIndices

set_option backward.isDefEq.respectTransparency false

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def indicatorExponent (s : Finset σ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if i ∈ s then 1 else 0)

theorem indicatorExponent_apply (s : Finset σ) (i : σ) :
    indicatorExponent s i = if i ∈ s then 1 else 0 := by
  simp [indicatorExponent]

theorem indicatorExponent_degree (s : Finset σ) :
    (indicatorExponent s).degree = s.card := by
  rw [Finsupp.degree_eq_sum]
  simp only [indicatorExponent_apply]
  simp

theorem indicator_support_le (α : σ →₀ ℕ) : indicatorExponent α.support ≤ α := by
  intro i
  rw [indicatorExponent_apply]
  split_ifs with hi
  · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  · exact Nat.zero_le _

theorem support_card_le_degree (α : σ →₀ ℕ) : α.support.card ≤ α.degree := by
  rw [← indicatorExponent_degree α.support, Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum (fun i _ => indicator_support_le α i)

theorem support_remainder_degree (α : σ →₀ ℕ) :
    (α - indicatorExponent α.support).degree + α.support.card = α.degree := by
  have he := congrArg Finsupp.degree (tsub_add_cancel_of_le (indicator_support_le α))
  simpa only [map_add, indicatorExponent_degree] using he

omit [DecidableEq σ] in
/-- A degree-one nonnegative multi-index is a single exponent of one. -/
theorem degree_one_single (α : σ →₀ ℕ) (hα : α.degree = 1) :
    ∃ a : σ, α = Finsupp.single a 1 := by
  have hne : α ≠ 0 := by intro hz; simp [hz] at hα
  have hex : ∃ a : σ, α a ≠ 0 := by
    by_contra hn
    apply hne
    ext a
    exact not_not.mp (not_exists.mp hn a)
  obtain ⟨a, ha⟩ := hex
  have hval : α a = 1 := by
    have hle := Finsupp.le_degree a α
    omega
  have hle : Finsupp.single a 1 ≤ α := Finsupp.single_le_iff.mpr (by omega)
  have he := tsub_add_cancel_of_le hle
  have hd := congrArg Finsupp.degree he
  have hz : α - Finsupp.single a 1 = 0 := by
    apply (Finsupp.degree_eq_zero_iff _).mp
    rw [map_add, Finsupp.degree_single, hα] at hd
    omega
  exact ⟨a, by simpa only [hz, zero_add] using he.symm⟩

end General

def bubbleExponent : Vertex →₀ ℕ := indicatorExponent Finset.univ

theorem bubbleExponent_apply (i : Vertex) : bubbleExponent i = 1 := by
  simp [bubbleExponent, indicatorExponent_apply]

theorem bubbleExponent_degree : bubbleExponent.degree = 4 := by
  simp [bubbleExponent, indicatorExponent_degree]

theorem indicator_three_face (s : Finset Vertex) (hs : s.card = 3) :
    ∃ i : Vertex, indicatorExponent s = faceExponent i := by
  have hlt : s.card < (Finset.univ : Finset Vertex).card := by simp [hs]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hsub : s ⊆ Finset.univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun hji => hi (hji ▸ hj), Finset.mem_univ j⟩
  have he : s = Finset.univ.erase i :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hs])
  refine ⟨i, ?_⟩
  ext j
  simp only [indicatorExponent_apply, he, Finset.mem_erase, Finset.mem_univ,
    and_true, faceExponent_apply]
  split_ifs <;> simp_all

/-- Exactly the four cubic face monomials remain after edge-carried indices
are removed. -/
theorem cubic_classification (α : Vertex →₀ ℕ) (hd : α.degree = 3)
    (hs : 3 ≤ α.support.card) : ∃ i : Vertex, α = faceExponent i := by
  have hc : α.support.card = 3 := by
    have hle := support_card_le_degree α
    omega
  have hrem := support_remainder_degree α
  have hz : α - indicatorExponent α.support = 0 := by
    apply (Finsupp.degree_eq_zero_iff _).mp
    omega
  obtain ⟨i, hi⟩ := indicator_three_face α.support hc
  refine ⟨i, ?_⟩
  have he := tsub_add_cancel_of_le (indicator_support_le α)
  rw [hz, zero_add] at he
  exact he.symm.trans hi

/-- The twelve quartic face indices and the unique interior index are
exhaustive.  The doubled variable is different from the omitted variable. -/
theorem quartic_classification (α : Vertex →₀ ℕ) (hd : α.degree = 4)
    (hs : 3 ≤ α.support.card) :
    α = bubbleExponent ∨ ∃ i a : Vertex, i ≠ a ∧ α = faceExponent i + Finsupp.single a 1 := by
  have hcard : α.support.card ≤ 4 :=
    (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  rcases (by omega : α.support.card = 4 ∨ α.support.card = 3) with hc | hc
  · left
    have he : α.support = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hc])
    have hrem := support_remainder_degree α
    have hz : α - indicatorExponent α.support = 0 := by
      apply (Finsupp.degree_eq_zero_iff _).mp
      omega
    have hh := tsub_add_cancel_of_le (indicator_support_le α)
    rw [hz, zero_add] at hh
    rw [← hh, he]
    rfl
  · right
    obtain ⟨i, hi⟩ := indicator_three_face α.support hc
    have hrem := support_remainder_degree α
    have hone : (α - indicatorExponent α.support).degree = 1 := by omega
    obtain ⟨a, ha⟩ := degree_one_single _ hone
    have hia : i ≠ a := by
      intro he
      subst a
      have hzero : α i = 0 := by
        have hv := congrArg (fun β : Vertex →₀ ℕ => β i) hi
        simp only [indicatorExponent_apply, faceExponent_apply, if_true] at hv
        have hn : i ∉ α.support := by simpa only [ite_eq_right_iff, one_ne_zero] using hv
        exact Finsupp.notMem_support_iff.mp hn
      have hv := congrArg (fun β : Vertex →₀ ℕ => β i) ha
      simp [hzero] at hv
    refine ⟨i, a, hia, ?_⟩
    have hh := tsub_add_cancel_of_le (indicator_support_le α)
    rw [ha, hi] at hh
    exact hh.symm.trans (add_comm _ _)

end FreudenthalSVLean.LowDegreeBubbleIndices
