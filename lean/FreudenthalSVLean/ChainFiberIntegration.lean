import FreudenthalSVLean.BarycentricFaceGeometry

/-!
# Coordinate fibers of the genuine Freudenthal tetrahedron integral

For the smooth-function flux identity needed in manuscript Lemma `means`,
every coordinate of the reference tetrahedron can be integrated last.
The remaining two coordinates always range over the same actual triangle;
the fiber endpoints are explicit.  The result follows from a proved
measure-preserving coordinate splitting and Fubini, with all integrability
hypotheses discharged by compactness.  No smooth Gauss or trace theorem
is an input to this module.
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral

noncomputable section

namespace FreudenthalSVLean.ChainFiberIntegration

set_option backward.isDefEq.respectTransparency false

def splitCoordinate (j : Fin 3) : Space ≃ᵐ Point :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

theorem splitCoordinate_preserving (j : Fin 3) : MeasurePreserving (splitCoordinate j) :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) j)

def coordinateFiber (j : Fin 3) (p : FacePoint) (s : ℝ) : Space :=
  j.insertNth s ![p.1, p.2]

theorem coordinateFiber_zero (p : FacePoint) (s : ℝ) :
    coordinateFiber 0 p s = ![s, p.1, p.2] := by
  ext a
  fin_cases a <;> norm_num [coordinateFiber, Fin.insertNth, Fin.succAboveCases,
    Fin.lt_def, Fin.ext_iff]

theorem coordinateFiber_one (p : FacePoint) (s : ℝ) :
    coordinateFiber 1 p s = ![p.1, s, p.2] := by
  ext a
  fin_cases a <;> norm_num [coordinateFiber, Fin.insertNth, Fin.succAboveCases,
    Fin.lt_def, Fin.ext_iff]

theorem coordinateFiber_two (p : FacePoint) (s : ℝ) :
    coordinateFiber 2 p s = ![p.1, p.2, s] := by
  ext a
  fin_cases a <;> norm_num [coordinateFiber, Fin.insertNth, Fin.succAboveCases,
    Fin.lt_def, Fin.ext_iff]

theorem splitCoordinate_symm (j : Fin 3) (s : ℝ) (p : FacePoint) :
    (splitCoordinate j).symm (s, p) = coordinateFiber j p s := rfl

theorem coordinateFiber_joint_continuous (j : Fin 3) :
    Continuous (fun z : Point => coordinateFiber j z.2 z.1) := by
  change Continuous (fun z : Point =>
    j.insertNth (α := fun _ : Fin 3 => ℝ) z.1 (![z.2.1, z.2.2] : Fin 2 → ℝ))
  apply Continuous.finInsertNth (A := fun _ : Fin 3 => ℝ) j continuous_fst
  apply continuous_pi
  intro a
  fin_cases a <;> fun_prop

theorem coordinateFiber_continuous (j : Fin 3) (p : FacePoint) :
    Continuous (coordinateFiber j p) := by
  change Continuous (fun s : ℝ =>
    j.insertNth (α := fun _ : Fin 3 => ℝ) s (![p.1, p.2] : Fin 2 → ℝ))
  exact Continuous.finInsertNth (A := fun _ : Fin 3 => ℝ) j continuous_id continuous_const

def fiberLower (j : Fin 3) (p : FacePoint) : ℝ := ![p.1, p.2, 0] j

def fiberUpper (j : Fin 3) (p : FacePoint) : ℝ := ![1, p.1, p.2] j

theorem coordinateFiber_mem (j : Fin 3) (p : FacePoint) (s : ℝ) :
    coordinateFiber j p s ∈ coordinateChainSet ↔
      p ∈ triangleSet 1 ∧ s ∈ Icc (fiberLower j p) (fiberUpper j p) := by
  fin_cases j
  · have he := coordinateFiber_zero p s
    change coordinateFiber 0 p s ∈ coordinateChainSet ↔
      p ∈ triangleSet 1 ∧ s ∈ Icc (fiberLower 0 p) (fiberUpper 0 p)
    rw [he, coordinateChainSet_mem]
    dsimp [fiberLower, fiberUpper, triangleSet]
    simp only [mem_Icc, and_assoc]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h3, h4.trans h2, h5, h6, h4, h2⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1.trans h5, h6, h1, h5, h3, h4⟩
  · have he := coordinateFiber_one p s
    change coordinateFiber 1 p s ∈ coordinateChainSet ↔
      p ∈ triangleSet 1 ∧ s ∈ Icc (fiberLower 1 p) (fiberUpper 1 p)
    rw [he, coordinateChainSet_mem]
    dsimp [fiberLower, fiberUpper, triangleSet]
    simp only [mem_Icc, and_assoc]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h5, h6.trans h4, h6, h4⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h3.trans h5, h6, h3, h5⟩
  · have he := coordinateFiber_two p s
    change coordinateFiber 2 p s ∈ coordinateChainSet ↔
      p ∈ triangleSet 1 ∧ s ∈ Icc (fiberLower 2 p) (fiberUpper 2 p)
    rw [he, coordinateChainSet_mem]
    dsimp [fiberLower, fiberUpper, triangleSet]
    simp only [mem_Icc, and_assoc]

theorem fiberLower_le_upper (j : Fin 3) (p : FacePoint) (hp : p ∈ triangleSet 1) :
    fiberLower j p ≤ fiberUpper j p := by
  fin_cases j <;> dsimp [fiberLower, fiberUpper] <;>
    linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

theorem coordinateChain_integral_fiber (j : Fin 3) (f : Space → ℝ) (hf : Continuous f) :
    (∫ x in coordinateChainSet, f x) =
      ∫ p in triangleSet 1, ∫ s in Icc (fiberLower j p) (fiberUpper j p),
        f (coordinateFiber j p s) := by
  classical
  let g : Point → ℝ := fun z => coordinateChainSet.indicator f ((splitCoordinate j).symm z)
  have hi : Integrable (coordinateChainSet.indicator f) :=
    (hf.continuousOn.integrableOn_compact (μ := volume) coordinateChainSet_isCompact).integrable_indicator
      coordinateChainSet_isCompact.measurableSet
  have hg : Integrable g := by
    apply ((splitCoordinate_preserving j).integrable_comp_emb
      (splitCoordinate j).measurableEmbedding).mp
    simpa only [Function.comp_def, g, MeasurableEquiv.symm_apply_apply] using hi
  rw [← integral_indicator coordinateChainSet_isCompact.measurableSet]
  have he := (splitCoordinate_preserving j).integral_comp
    (splitCoordinate j).measurableEmbedding g
  have hfun : (fun x : Space => g (splitCoordinate j x)) = coordinateChainSet.indicator f := by
    funext x
    simp only [g, MeasurableEquiv.symm_apply_apply]
  rw [hfun] at he
  rw [he]
  rw [Measure.volume_eq_prod] at hg ⊢
  rw [integral_prod_symm g hg, ← integral_indicator (triangleSet_isCompact 1).measurableSet]
  apply integral_congr_ae
  filter_upwards with p
  by_cases hp : p ∈ triangleSet 1
  · have hfiber : (fun s => g (s, p)) =
        (Icc (fiberLower j p) (fiberUpper j p)).indicator
          (fun s => f (coordinateFiber j p s)) := by
      funext s
      simp only [g, splitCoordinate_symm]
      simp [indicator, coordinateFiber_mem, hp]
    rw [hfiber, integral_indicator measurableSet_Icc]
    simp [hp]
  · have hzero : (fun s => g (s, p)) = 0 := by
      funext s
      simp only [g, splitCoordinate_symm]
      simp [indicator, coordinateFiber_mem, hp]
    rw [hzero]
    simp [hp]

end FreudenthalSVLean.ChainFiberIntegration
