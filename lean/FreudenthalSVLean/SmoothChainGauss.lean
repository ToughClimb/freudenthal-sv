import FreudenthalSVLean.ChainFiberIntegration
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth Gauss identity on the reference Freudenthal tetrahedron

For manuscript Lemma `means`, the volume integral of each partial
derivative of a genuine C1 function is expressed by its actual face
integrals.  Coordinate fibers reduce the proof to the one-dimensional
fundamental theorem of calculus.  The endpoints are the actual affine
face charts, and the two contributing faces give exactly the proved
barycentric-gradient flux weights.  Neither polynomial approximation
nor an assumed smooth divergence theorem is used.  H1 trace continuity
and a stable initial mean lift are separate obligations.
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.ChainFiberIntegration

noncomputable section

namespace FreudenthalSVLean.SmoothChainGauss

set_option backward.isDefEq.respectTransparency false

theorem coordinateFiber_hasDerivAt (j : Fin 3) (p : FacePoint) (s : ℝ) :
    HasDerivAt (coordinateFiber j p) (Pi.single j 1) s := by
  apply hasDerivAt_pi.mpr
  rw [Fin.forall_iff_succAbove j]
  constructor
  · simpa only [coordinateFiber, Fin.insertNth_apply_same, Pi.single_eq_same] using! hasDerivAt_id s
  · intro a
    simpa [coordinateFiber, Pi.single_apply, Fin.succAbove_ne] using!
      hasDerivAt_const s (![p.1, p.2] a)

theorem fiber_partial_integral {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (j : Fin 3) (p : FacePoint) (hp : p ∈ triangleSet 1) :
    (∫ s in Icc (fiberLower j p) (fiberUpper j p),
      fderiv ℝ f (coordinateFiber j p s) (Pi.single j 1)) =
        f (coordinateFiber j p (fiberUpper j p)) - f (coordinateFiber j p (fiberLower j p)) := by
  have hc : Continuous (fun s => fderiv ℝ f (coordinateFiber j p s) (Pi.single j 1)) :=
    ((hf.continuous_fderiv (by norm_num)).comp
      (coordinateFiber_continuous j p)).clm_apply continuous_const
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (fiberLower_le_upper j p hp)]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => f (coordinateFiber j p s))
    (f' := fun s => fderiv ℝ f (coordinateFiber j p s) (Pi.single j 1))
  · intro s _
    exact (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt s
      (coordinateFiber_hasDerivAt j p s)
  · exact hc.intervalIntegrable _ _

theorem smooth_gauss_endpoints {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    (∫ x in coordinateChainSet, fderiv ℝ f x (Pi.single j 1)) =
      ∫ p in triangleSet 1, f (coordinateFiber j p (fiberUpper j p)) -
        f (coordinateFiber j p (fiberLower j p)) := by
  rw [coordinateChain_integral_fiber j _
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)]
  apply setIntegral_congr_fun (triangleSet_isCompact 1).measurableSet
  intro p hp
  exact fiber_partial_integral hf j p hp

theorem reference_faceChart_formula (r : Fin 4) (p : FacePoint) :
    faceChart (Equiv.refl (Fin 3)) (0 : Space) r p =
      ![![1, p.1, p.2], ![p.1, p.1, p.2], ![p.1, p.2, p.2], ![p.1, p.2, 0]] r := by
  have hc (w : Fin 4 → ℝ) : AffineBarycentric.affinePoint (Equiv.refl (Fin 3)) 0 w =
      ![w 1 + w 2 + w 3, w 2 + w 3, w 3] := by
    ext j
    fin_cases j
    · simp only [AffineBarycentric.affinePoint, Fin.sum_univ_four]
      change w 0 * (0 + 0) + w 1 * (0 + 1) + w 2 * (0 + 1) + w 3 * (0 + 1) = _
      change _ = w 1 + w 2 + w 3
      ring
    · simp only [AffineBarycentric.affinePoint, Fin.sum_univ_four]
      change w 0 * (0 + 0) + w 1 * (0 + 0) + w 2 * (0 + 1) + w 3 * (0 + 1) = _
      change _ = w 2 + w 3
      ring
    · simp only [AffineBarycentric.affinePoint, Fin.sum_univ_four]
      change w 0 * (0 + 0) + w 1 * (0 + 0) + w 2 * (0 + 0) + w 3 * (0 + 1) = _
      change _ = w 3
      ring
  rw [faceChart, hc]
  fin_cases r
  · change ![(1 - p.1) + (p.1 - p.2) + p.2, (p.1 - p.2) + p.2, p.2] = ![1, p.1, p.2]
    apply funext
    rw [Fin.forall_iff_succ, Fin.forall_fin_two]
    refine ⟨?_, ?_, ?_⟩
    · change (1 - p.1) + (p.1 - p.2) + p.2 = 1
      ring
    · change (p.1 - p.2) + p.2 = p.1
      ring
    · rfl
  · change ![0 + (p.1 - p.2) + p.2, (p.1 - p.2) + p.2, p.2] = ![p.1, p.1, p.2]
    apply funext
    rw [Fin.forall_iff_succ, Fin.forall_fin_two]
    refine ⟨?_, ?_, ?_⟩
    · change 0 + (p.1 - p.2) + p.2 = p.1
      ring
    · change (p.1 - p.2) + p.2 = p.1
      ring
    · rfl
  · change ![(p.1 - p.2) + 0 + p.2, 0 + p.2, p.2] = ![p.1, p.2, p.2]
    apply funext
    rw [Fin.forall_iff_succ, Fin.forall_fin_two]
    refine ⟨?_, ?_, ?_⟩
    · change (p.1 - p.2) + 0 + p.2 = p.1
      ring
    · change 0 + p.2 = p.2
      ring
    · rfl
  · change ![(p.1 - p.2) + p.2 + 0, p.2 + 0, 0] = ![p.1, p.2, 0]
    apply funext
    rw [Fin.forall_iff_succ, Fin.forall_fin_two]
    refine ⟨?_, ?_, ?_⟩
    · change (p.1 - p.2) + p.2 + 0 = p.1
      ring
    · change p.2 + 0 = p.2
      ring
    · rfl

theorem reference_upper_chart (j : Fin 3) (p : FacePoint) :
    coordinateFiber j p (fiberUpper j p) =
      faceChart (Equiv.refl (Fin 3)) (0 : Space) j.castSucc p := by
  rw [reference_faceChart_formula]
  fin_cases j
  · change coordinateFiber 0 p 1 = ![1, p.1, p.2]
    exact coordinateFiber_zero p 1
  · change coordinateFiber 1 p p.1 = ![p.1, p.1, p.2]
    exact coordinateFiber_one p p.1
  · change coordinateFiber 2 p p.2 = ![p.1, p.2, p.2]
    exact coordinateFiber_two p p.2

theorem reference_lower_chart (j : Fin 3) (p : FacePoint) :
    coordinateFiber j p (fiberLower j p) =
      faceChart (Equiv.refl (Fin 3)) (0 : Space) j.succ p := by
  rw [reference_faceChart_formula]
  fin_cases j
  · change coordinateFiber 0 p p.1 = ![p.1, p.1, p.2]
    exact coordinateFiber_zero p p.1
  · change coordinateFiber 1 p p.2 = ![p.1, p.2, p.2]
    exact coordinateFiber_one p p.2
  · change coordinateFiber 2 p 0 = ![p.1, p.2, 0]
    exact coordinateFiber_two p 0

theorem reference_smooth_gauss {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    (∫ x in coordinateChainSet, fderiv ℝ f x (Pi.single j 1)) =
      ∑ r : Fin 4, -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) r j *
        ∫ p in triangleSet 1, f (faceChart (Equiv.refl (Fin 3)) (0 : Space) r p) := by
  have hi (r : Fin 4) : IntegrableOn (fun p => f (faceChart (Equiv.refl (Fin 3)) (0 : Space) r p))
      (triangleSet 1) :=
    (hf.continuous.comp (faceChart_continuous _ _ _)).continuousOn.integrableOn_compact
      (μ := volume) (triangleSet_isCompact 1)
  rw [smooth_gauss_endpoints hf j]
  simp only [reference_upper_chart, reference_lower_chart]
  rw [integral_sub (hi j.castSucc) (hi j.succ)]
  rw [Fin.sum_univ_four]
  fin_cases j <;>
    norm_num [-Matrix.cons_val, -Fin.val_eq_zero_iff, -Fin.val_pos_iff,
      barycentricGradient, coordinateUnit, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      sub_eq_add_neg]
  all_goals rfl

theorem reference_smooth_vector_gauss (v : Fin 3 → Space → ℝ)
    (hv : ∀ j, ContDiff ℝ 1 (v j)) :
    (∫ x in coordinateChainSet, ∑ j : Fin 3, fderiv ℝ (v j) x (Pi.single j 1)) =
      ∑ r : Fin 4, ∫ p in triangleSet 1, ∑ j : Fin 3,
        -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) r j *
          v j (faceChart (Equiv.refl (Fin 3)) (0 : Space) r p) := by
  rw [integral_finsetSum]
  · simp only [reference_smooth_gauss (hv _) _]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro j _
      exact ((hv j).continuous.comp (faceChart_continuous _ _ r)).const_mul _
        |>.continuousOn.integrableOn_compact (μ := volume) (triangleSet_isCompact 1)
  · intro j _
    exact ((hv j).continuous_fderiv (by norm_num)).clm_apply continuous_const
      |>.continuousOn.integrableOn_compact (μ := volume) coordinateChainSet_isCompact

end FreudenthalSVLean.SmoothChainGauss
