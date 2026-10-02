import FreudenthalSVLean.MeshSegments
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# A global representation of Freudenthal nodal hats

The manuscript's equation `vertex-raw-bubble` uses the continuous nodal
functions `φ_a`.  For their formal implementation, an augmented-coordinate
range gives a global scalar function
`max(0,1+min(0,x-a)-max(0,x-a))`.  This module proves its continuity and
local identities against actual Freudenthal barycentric coordinates.
No mesh intersection compatibility is inserted as an axiom.
-/

open Set MvPolynomial
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.GridNodal

def augmented (u : Space) : Fin 4 → ℝ := Fin.cons 0 u

def lower (u : Space) : ℝ := Finset.univ.inf' Finset.univ_nonempty (augmented u)
def upper (u : Space) : ℝ := Finset.univ.sup' Finset.univ_nonempty (augmented u)
def hat (u : Space) : ℝ := max 0 (1 + lower u - upper u)
def nodal (a x : Space) : ℝ := hat (x - a)

theorem lower_le_zero (u : Space) : lower u ≤ 0 :=
  Finset.inf'_le (augmented u) (Finset.mem_univ 0)

theorem lower_le_coordinate (u : Space) (j : Fin 3) : lower u ≤ u j :=
  Finset.inf'_le (augmented u) (Finset.mem_univ j.succ)

theorem zero_le_upper (u : Space) : 0 ≤ upper u :=
  Finset.le_sup' (augmented u) (Finset.mem_univ 0)

theorem coordinate_le_upper (u : Space) (j : Fin 3) : u j ≤ upper u :=
  Finset.le_sup' (augmented u) (Finset.mem_univ j.succ)

theorem lower_eq (u : Space) (m : ℝ) (hm0 : m ≤ 0) (hmu : ∀ j, m ≤ u j)
    (he : m = 0 ∨ ∃ j, u j = m) : lower u = m := by
  apply le_antisymm
  · rcases he with rfl | ⟨j, hj⟩
    · exact lower_le_zero u
    · exact hj ▸ lower_le_coordinate u j
  · apply Finset.le_inf'
    intro i _
    refine Fin.cases hm0 (fun j => hmu j) i

theorem upper_eq (u : Space) (m : ℝ) (hm0 : 0 ≤ m) (hmu : ∀ j, u j ≤ m)
    (he : m = 0 ∨ ∃ j, u j = m) : upper u = m := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    refine Fin.cases hm0 (fun j => hmu j) i
  · rcases he with rfl | ⟨j, hj⟩
    · exact zero_le_upper u
    · exact hj ▸ coordinate_le_upper u j

theorem lower_continuous : Continuous lower := by
  apply Continuous.finset_inf'_apply
  intro i _
  refine Fin.cases continuous_const (fun j => continuous_apply j) i

theorem upper_continuous : Continuous upper := by
  apply Continuous.finset_sup'_apply
  intro i _
  refine Fin.cases continuous_const (fun j => continuous_apply j) i

theorem hat_continuous : Continuous hat :=
  continuous_const.max ((continuous_const.add lower_continuous).sub upper_continuous)

theorem nodal_continuous (a : Space) : Continuous (nodal a) :=
  hat_continuous.comp (continuous_id.sub continuous_const)

theorem hat_nonneg (u : Space) : 0 ≤ hat u := le_max_left _ _

theorem hat_zero_of_difference (u : Space) (i j : Fin 3) (h : 1 ≤ u i - u j) :
    hat u = 0 := by
  apply max_eq_left
  have hlo := lower_le_coordinate u j
  have hhi := coordinate_le_upper u i
  linarith

theorem hat_zero_of_ge_one (u : Space) (j : Fin 3) (h : 1 ≤ u j) : hat u = 0 := by
  apply max_eq_left
  have hlo := lower_le_zero u
  have hhi := coordinate_le_upper u j
  linarith

theorem hat_zero_of_le_neg_one (u : Space) (j : Fin 3) (h : u j ≤ -1) : hat u = 0 := by
  apply max_eq_left
  have hlo := lower_le_coordinate u j
  have hhi := zero_le_upper u
  linarith

/-- At every incident node, the global hat is exactly the actual local
barycentric coordinate, including all closed faces and tie cases. -/
theorem nodal_eq_barycentric (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hx : x ∈ unitChainSet σ o) (a : Fin 4) :
    nodal (ChainGeometry.chainVertex σ o a) x =
      eval x (ChainGeometry.barycentric σ o a) := by
  let t := unitNormalize σ o x
  let u := x - ChainGeometry.chainVertex σ o a
  have hp := (coordinateChainSet_mem t).mp hx
  have hu (r : Fin 3) : u (σ r) = t r - if r.val < a.val then 1 else 0 := by
    simp [u, t, unitNormalize_apply, ChainGeometry.chainVertex, sub_add_eq_sub_sub]
  fin_cases a
  · have hlo : lower u = 0 := lower_eq u 0 le_rfl (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;> linarith! [hp.1, hp.2.2.1, hp.2.2.2.2.1]) (Or.inl rfl)
    have hhi : upper u = t 0 := upper_eq u (t 0) hp.1 (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;> linarith! [hp.2.2.2.1, hp.2.2.2.2.2])
      (Or.inr ⟨σ 0, by rw [hu]; norm_num⟩)
    change max 0 (1 + lower u - upper u) = _
    rw [hlo, hhi, unitBarycentric_normalize]
    simpa [ChainGeometry.barycentric, ChainGeometry.chainCoordinate, t] using
      max_eq_right (by linarith [hp.2.1] : 0 ≤ 1 - t 0)
  · have hlo : lower u = t 0 - 1 := lower_eq u (t 0 - 1) (by linarith [hp.2.1]) (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;> linarith! [hp.2.1, hp.2.2.1, hp.2.2.2.2.1])
      (Or.inr ⟨σ 0, by rw [hu]; norm_num⟩)
    have hhi : upper u = t 1 := upper_eq u (t 1) hp.2.2.1 (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;> linarith! [hp.2.1, hp.2.2.1, hp.2.2.2.2.2])
      (Or.inr ⟨σ 1, by rw [hu]; norm_num⟩)
    change max 0 (1 + lower u - upper u) = _
    rw [hlo, hhi, unitBarycentric_normalize]
    have he : 1 + (t 0 - 1) - t 1 = t 0 - t 1 := by ring
    rw [he]
    simpa [ChainGeometry.barycentric, ChainGeometry.chainCoordinate, t] using
      max_eq_right (sub_nonneg.mpr hp.2.2.2.1)
  · have hlo : lower u = t 1 - 1 := lower_eq u (t 1 - 1) (by
      linarith [hp.2.1, hp.2.2.2.1]) (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;>
        linarith! [hp.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
      (Or.inr ⟨σ 1, by rw [hu]; norm_num⟩)
    have hhi : upper u = t 2 := upper_eq u (t 2) hp.2.2.2.2.1 (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;>
        linarith! [hp.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
      (Or.inr ⟨σ 2, by rw [hu]; norm_num⟩)
    change max 0 (1 + lower u - upper u) = _
    rw [hlo, hhi, unitBarycentric_normalize]
    have he : 1 + (t 1 - 1) - t 2 = t 1 - t 2 := by ring
    rw [he]
    simpa [ChainGeometry.barycentric, ChainGeometry.chainCoordinate, t] using
      max_eq_right (sub_nonneg.mpr hp.2.2.2.2.2)
  · have hlo : lower u = t 2 - 1 := lower_eq u (t 2 - 1) (by
      linarith [hp.2.1, hp.2.2.2.1, hp.2.2.2.2.2]) (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;> linarith! [hp.2.2.2.1, hp.2.2.2.2.2])
      (Or.inr ⟨σ 2, by rw [hu]; norm_num⟩)
    have hhi : upper u = 0 := upper_eq u 0 le_rfl (by
      intro j
      obtain ⟨r, rfl⟩ := σ.surjective j
      rw [hu]
      fin_cases r <;> norm_num <;>
        linarith! [hp.2.1, hp.2.2.2.1, hp.2.2.2.2.2]) (Or.inl rfl)
    change max 0 (1 + lower u - upper u) = _
    rw [hlo, hhi, unitBarycentric_normalize]
    have he : 1 + (t 2 - 1) - 0 = t 2 := by ring
    rw [he]
    simpa [ChainGeometry.barycentric, ChainGeometry.chainCoordinate, t] using
      max_eq_right hp.2.2.2.2.1

end FreudenthalSVLean.GridNodal
