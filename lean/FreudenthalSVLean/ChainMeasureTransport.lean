import FreudenthalSVLean.BernsteinVolumeIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue-volume transport to the Freudenthal coordinate representation

The manuscript's equation `bernstein-mean` is formulated on tetrahedra in
three-dimensional Cartesian coordinates.  This module transports the
proved reference volume integral from nested product coordinates to
`Fin 3 → ℝ`.  All changes of coordinates are measurable equivalences with
proved preservation of Lebesgue measure.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BernsteinVolumeIntegral

noncomputable section

namespace FreudenthalSVLean.ChainMeasureTransport

abbrev Space := Fin 3 → ℝ

def coordinateEquiv : Space ≃ᵐ Point :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

theorem coordinateEquiv_apply (x : Space) :
    coordinateEquiv x = (x 0, x 1, x 2) := rfl

theorem coordinateEquiv_preserving : MeasurePreserving coordinateEquiv := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

def coordinateChainSet : Set Space := coordinateEquiv ⁻¹' chainSet

theorem coordinateChainSet_mem (x : Space) :
    x ∈ coordinateChainSet ↔
      0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ x 0 ∧ 0 ≤ x 2 ∧ x 2 ≤ x 1 := by
  simp [coordinateChainSet, coordinateEquiv_apply, chainSet]
  tauto

theorem coordinateEquiv_symm_apply (p : Point) :
    coordinateEquiv.symm p = ![p.1, p.2.1, p.2.2] := by
  apply coordinateEquiv.injective
  simp [coordinateEquiv_apply]

theorem coordinateEquiv_symm_continuous : Continuous coordinateEquiv.symm := by
  apply continuous_pi
  intro i
  simp only [coordinateEquiv_symm_apply]
  fin_cases i <;> dsimp <;> fun_prop

theorem coordinateChainSet_isCompact : IsCompact coordinateChainSet := by
  have hs : coordinateChainSet = coordinateEquiv.symm '' chainSet := by
    ext x
    constructor
    · intro hx
      exact ⟨coordinateEquiv x, hx, coordinateEquiv.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [coordinateChainSet, Set.mem_preimage,
        MeasurableEquiv.apply_symm_apply] using hy
  rw [hs]
  exact chainSet_isCompact.image coordinateEquiv_symm_continuous

theorem chainBarycentric_eq_reference (x : Space) (i : Fin 4) :
    eval x (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) i) =
      referenceBarycentric (coordinateEquiv x) i := by
  fin_cases i <;>
    simp [ChainGeometry.barycentric, ChainGeometry.chainCoordinate,
      referenceBarycentric, coordinateEquiv_apply]

/-- The reference integral now uses the same spatial polynomial and
Cartesian volume measure as the manuscript. -/
theorem coordinate_bernstein_integral (d : ℕ) (α : Fin 4 →₀ ℕ) :
    (∫ x in coordinateChainSet,
      eval (fun i => eval x
        (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) i))
        (bernstein (R := ℝ) d α)) =
      (Nat.factorial d : ℝ) / (Nat.factorial (α.degree + 3) : ℝ) := by
  calc
    _ = ∫ x in coordinateChainSet,
        eval (referenceBarycentric (coordinateEquiv x)) (bernstein (R := ℝ) d α) := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg (fun z : Fin 4 → ℝ => eval z (bernstein (R := ℝ) d α))
        (funext (chainBarycentric_eq_reference x))
    _ = _ := by
      rw [coordinateChainSet, coordinateEquiv_preserving.setIntegral_preimage_emb
        coordinateEquiv.measurableEmbedding
        (fun p => eval (referenceBarycentric p) (bernstein (R := ℝ) d α)) chainSet]
      exact bernstein_volume_integral d α

/-- Translate to the cube origin and put the Cartesian coordinates in chain
order.  The same equivalence applies to all six permutations. -/
def unitNormalize (σ : Equiv.Perm (Fin 3)) (o : Space) : Space ≃ᵐ Space :=
  (MeasurableEquiv.subRight o).trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) σ.symm)

theorem unitNormalize_apply (σ : Equiv.Perm (Fin 3)) (o x : Space) (j : Fin 3) :
    unitNormalize σ o x j = x (σ j) - o (σ j) := by
  simp [unitNormalize, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.subRight]
  rfl

theorem unitNormalize_preserving (σ : Equiv.Perm (Fin 3)) (o : Space) :
    MeasurePreserving (unitNormalize σ o) := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) σ.symm).comp
    (measurePreserving_sub_right volume o)

def unitChainSet (σ : Equiv.Perm (Fin 3)) (o : Space) : Set Space :=
  (unitNormalize σ o) ⁻¹' coordinateChainSet

theorem unitNormalize_symm_apply (σ : Equiv.Perm (Fin 3)) (o x : Space) (j : Fin 3) :
    (unitNormalize σ o).symm x j = x (σ.symm j) + o j := by
  have h := unitNormalize_apply σ o ((unitNormalize σ o).symm x) (σ.symm j)
  simp only [MeasurableEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  linarith

theorem unitNormalize_symm_continuous (σ : Equiv.Perm (Fin 3)) (o : Space) :
    Continuous (unitNormalize σ o).symm := by
  apply continuous_pi
  intro j
  simp only [unitNormalize_symm_apply]
  fun_prop

theorem unitChainSet_isCompact (σ : Equiv.Perm (Fin 3)) (o : Space) :
    IsCompact (unitChainSet σ o) := by
  have hs : unitChainSet σ o = (unitNormalize σ o).symm '' coordinateChainSet := by
    ext x
    constructor
    · intro hx
      exact ⟨unitNormalize σ o x, hx, (unitNormalize σ o).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [unitChainSet, Set.mem_preimage,
        MeasurableEquiv.apply_symm_apply] using hy
  rw [hs]
  exact coordinateChainSet_isCompact.image (unitNormalize_symm_continuous σ o)

theorem unitBarycentric_normalize (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (i : Fin 4) :
    eval x (ChainGeometry.barycentric σ o i) =
      eval (unitNormalize σ o x)
        (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) i) := by
  fin_cases i <;>
    simp [ChainGeometry.barycentric, ChainGeometry.chainCoordinate,
      unitNormalize_apply]

/-- The common Bernstein integral on every translated unit Freudenthal
tetrahedron; no list of the six coordinate orders is needed. -/
theorem unit_bernstein_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (d : ℕ) (α : Fin 4 →₀ ℕ) :
    (∫ x in unitChainSet σ o,
      eval (fun i => eval x (ChainGeometry.barycentric σ o i))
        (bernstein (R := ℝ) d α)) =
      (Nat.factorial d : ℝ) / (Nat.factorial (α.degree + 3) : ℝ) := by
  calc
    _ = ∫ x in unitChainSet σ o,
        eval (fun i => eval (unitNormalize σ o x)
          (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) i))
            (bernstein (R := ℝ) d α) := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg (fun z : Fin 4 → ℝ => eval z (bernstein (R := ℝ) d α))
        (funext (unitBarycentric_normalize σ o x))
    _ = _ := by
      rw [unitChainSet, (unitNormalize_preserving σ o).setIntegral_preimage_emb
        (unitNormalize σ o).measurableEmbedding
        (fun x => eval (fun i => eval x
          (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) i))
            (bernstein (R := ℝ) d α)) coordinateChainSet]
      exact coordinate_bernstein_integral d α

end FreudenthalSVLean.ChainMeasureTransport
