import FreudenthalSVLean.BoundaryBoxH1Estimate

/-!
# Explicit half-box geometry at every cube boundary point

For the boundary part of manuscript Lemma `means` and equation `SZ`,
an actual symmetric box centered on any lower or upper cube coordinate
plane has a half-box outside the open cube.  Its exact Lebesgue volume
is half the full box volume, without enumeration of boundary vertices.
The proved weak-H1 zero-extension estimate therefore has the explicit
scale-independent coefficient 72 times the squared mesh-neighborhood
radius.  The same argument covers face, edge and corner boundary points.
It is an interpolation input, not the completed initial mean lift.
-/

open scoped BigOperators Topology
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.TranslatedBoxH1Estimate
open FreudenthalSVLean.BoundaryBoxH1Estimate

noncomputable section

namespace FreudenthalSVLean.BoundaryHalfBoxGeometry

set_option backward.isDefEq.respectTransparency false

def halfLower (upper : Bool) (h : ℝ) (o : Space) (j : Fin 3) : Space :=
  fun i => if upper then (if i = j then o i else -h + o i) else -h + o i

def halfUpper (upper : Bool) (h : ℝ) (o : Space) (j : Fin 3) : Space :=
  fun i => if upper then h + o i else (if i = j then o i else h + o i)

def halfBox (upper : Bool) (h : ℝ) (o : Space) (j : Fin 3) : Set Space :=
  Icc (halfLower upper h o j) (halfUpper upper h o j)

theorem halfLower_le_halfUpper (upper : Bool) {h : ℝ} (hh : 0 ≤ h)
    (o : Space) (j : Fin 3) : halfLower upper h o j ≤ halfUpper upper h o j := by
  intro i
  cases upper <;> by_cases hi : i = j <;>
    simp only [halfLower, halfUpper, Bool.false_eq_true,
      ite_false, ite_true, hi] <;> linarith

theorem halfBox_subset (upper : Bool) {h : ℝ} (hh : 0 ≤ h) (o : Space) (j : Fin 3) :
    halfBox upper h o j ⊆ translatedBox (-h) h o := by
  rintro x ⟨hlo, hup⟩
  constructor
  · intro i
    have ht := hlo i
    cases upper <;> by_cases hi : i = j <;>
      simp only [halfLower, Bool.false_eq_true,
        ite_false, ite_true, hi] at ht ⊢ <;> linarith
  · intro i
    have ht := hup i
    cases upper <;> by_cases hi : i = j <;>
      simp only [halfUpper, Bool.false_eq_true,
        ite_false, ite_true, hi] at ht ⊢ <;> linarith

theorem halfBox_volume (upper : Bool) {h : ℝ} (hh : 0 ≤ h) (o : Space) (j : Fin 3) :
    volume.real (halfBox upper h o j) = 4 * h ^ 3 := by
  change (volume (Icc (halfLower upper h o j) (halfUpper upper h o j))).toReal = _
  rw [Real.volume_Icc_pi_toReal (halfLower_le_halfUpper upper hh o j)]
  have hs (i : Fin 3) : halfUpper upper h o j i - halfLower upper h o j i =
      if i = j then h else 2 * h := by
    cases upper <;> by_cases hi : i = j <;>
      simp only [halfLower, halfUpper, Bool.false_eq_true,
        ite_false, ite_true, hi] <;> ring
  simp only [hs]
  rw [Fin.prod_univ_succAbove _ j]
  simp only [ite_true, Fin.succAbove_ne, ite_false, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

theorem halfBox_half_volume (upper : Bool) {h : ℝ} (hh : 0 ≤ h) (o : Space) (j : Fin 3) :
    volume.real (translatedBox (-h) h o) = 2 * volume.real (halfBox upper h o j) := by
  rw [translatedBox_volume (by linarith), halfBox_volume upper hh]
  ring

theorem lower_halfBox_outside (h : ℝ) (o : Space) (j : Fin 3) (ho : o j = 0) :
    halfBox false h o j ⊆ openCubeᶜ := by
  intro x hx hc
  have ht := hx.2 j
  simp only [halfUpper, Bool.false_eq_true, ite_false, ite_true, ho] at ht
  have hp := ((mem_openCube x).mp hc j).1
  linarith

theorem upper_halfBox_outside (h : ℝ) (o : Space) (j : Fin 3) (ho : o j = 1) :
    halfBox true h o j ⊆ openCubeᶜ := by
  intro x hx hc
  have ht := hx.1 j
  simp only [halfLower, ite_true, ho] at ht
  have hp := ((mem_openCube x).mp hc j).2
  linarith

/-- Every boundary-centered physical box, including edge/corner centers. -/
theorem boundary_centered_box_poincare {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hf : InH1ZeroCube f g) {h : ℝ} (hh : 0 < h) (o : Space)
    (hb : ∃ j : Fin 3, o j = 0 ∨ o j = 1) :
    (∫ x in translatedBox (-h) h o, (f x) ^ 2) ≤
      72 * h ^ 2 * ∑ j : Fin 3, ∫ x in translatedBox (-h) h o, (g j x) ^ 2 := by
  obtain ⟨j, hj⟩ := hb
  have hlen : -h < h := by linarith
  have ht : (∫ x in translatedBox (-h) h o, (f x) ^ 2) ≤
      18 * (h - -h) ^ 2 * ∑ i : Fin 3, ∫ x in translatedBox (-h) h o, (g i x) ^ 2 := by
    rcases hj with hlow | hupp
    · exact weak_boundary_box_poincare hf hlen o
        (halfBox_subset false hh.le o j) (lower_halfBox_outside h o j hlow)
        (halfBox_half_volume false hh.le o j).le
    · exact weak_boundary_box_poincare hf hlen o
        (halfBox_subset true hh.le o j) (upper_halfBox_outside h o j hupp)
        (halfBox_half_volume true hh.le o j).le
  calc
    _ ≤ _ := ht
    _ = _ := by ring

end FreudenthalSVLean.BoundaryHalfBoxGeometry
