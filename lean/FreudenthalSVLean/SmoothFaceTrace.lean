import FreudenthalSVLean.SmoothChainGauss
import FreudenthalSVLean.MeshSegments
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# An explicit genuine smooth face-trace estimate

For the trace estimate in manuscript Lemma `means`, the reference face
parameter-square integral is bounded by six times the volume-square
integral plus the true gradient-square integral.  The proof applies the
proved smooth Gauss identity to `(x-a_r) u^2`, where `a_r` is the omitted
vertex.  Its normal component vanishes on the other three faces and is
one on the designated face.  Actual coordinate bounds and completed
squares give the estimate.  Neither an imported Sobolev trace theorem
nor a stipulated surface integral is used.  Physical scale transport
and completion to general weak-H1 functions are separate obligations.
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.SmoothChainGauss

noncomputable section

namespace FreudenthalSVLean.SmoothFaceTrace

set_option backward.isDefEq.respectTransparency false

def referenceVertex (r : Fin 4) : Space := chainVertex (Equiv.refl (Fin 3)) 0 r

def traceVector (u : Space → ℝ) (r : Fin 4) (j : Fin 3) (x : Space) : ℝ :=
  (x j - referenceVertex r j) * u x * u x

theorem traceVector_contDiff {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (r : Fin 4) (j : Fin 3) :
    ContDiff ℝ 1 (traceVector u r j) := by
  exact (((ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).contDiff.sub contDiff_const).mul hu).mul hu

theorem traceVector_partial {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (r : Fin 4) (j : Fin 3) (x : Space) :
    fderiv ℝ (traceVector u r j) x (Pi.single j 1) =
      (u x) ^ 2 + 2 * (x j - referenceVertex r j) * u x * fderiv ℝ u x (Pi.single j 1) := by
  have hl : HasFDerivAt (fun y : Space => y j - referenceVertex r j)
      (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ) x := by
    simpa only using! (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).hasFDerivAt.sub_const
      (referenceVertex r j)
  have hd : HasFDerivAt u (fderiv ℝ u x) x :=
    (hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hφ : HasFDerivAt (traceVector u r j) _ x := (hl.mul hd).mul hd
  rw [hφ.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, Pi.mul_apply]
  ring

theorem reference_face_displacement_weight (r s : Fin 4) (p : FacePoint) :
    (∑ j : Fin 3, -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) s j *
      (faceChart (Equiv.refl (Fin 3)) 0 s p j - referenceVertex r j)) =
        if s = r then 1 else 0 := by
  have he := VertexJetAlgebra.gradient_dot_displacement (Equiv.refl (Fin 3))
    (0 : Space) (referenceVertex r) (faceChart (Equiv.refl (Fin 3)) 0 s p) s
  have hv : MvPolynomial.eval (referenceVertex r)
      (ChainGeometry.barycentric (Equiv.refl (Fin 3)) 0 s) = if s = r then 1 else 0 :=
    ChainGeometry.barycentric_vertex (Equiv.refl (Fin 3)) (0 : Space) s r
  rw [faceChart_missing_zero, hv] at he
  simp only [neg_mul] at ⊢
  rw [Finset.sum_neg_distrib, he]
  simp

theorem traceVector_face_flux (u : Space → ℝ) (r s : Fin 4) (p : FacePoint) :
    (∑ j : Fin 3, -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) s j *
      traceVector u r j (faceChart (Equiv.refl (Fin 3)) 0 s p)) =
        if s = r then (u (faceChart (Equiv.refl (Fin 3)) 0 s p)) ^ 2 else 0 := by
  classical
  have he : (∑ j : Fin 3, -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) s j *
      traceVector u r j (faceChart (Equiv.refl (Fin 3)) 0 s p)) =
      (∑ j : Fin 3, -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) s j *
        (faceChart (Equiv.refl (Fin 3)) 0 s p j - referenceVertex r j)) *
          (u (faceChart (Equiv.refl (Fin 3)) 0 s p)) ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [traceVector]
    ring
  rw [he, reference_face_displacement_weight]
  split_ifs <;> simp

theorem face_square_eq_traceVector_divergence {u : Space → ℝ}
    (hu : ContDiff ℝ 1 u) (r : Fin 4) :
    (∫ p in triangleSet 1, (u (faceChart (Equiv.refl (Fin 3)) 0 r p)) ^ 2) =
      ∫ x in coordinateChainSet, ∑ j : Fin 3,
        fderiv ℝ (traceVector u r j) x (Pi.single j 1) := by
  classical
  rw [reference_smooth_vector_gauss (traceVector u r) (traceVector_contDiff hu r)]
  simp only [traceVector_face_flux]
  have hi (s : Fin 4) : (∫ p in triangleSet 1,
      if s = r then (u (faceChart (Equiv.refl (Fin 3)) 0 s p)) ^ 2 else 0) =
      if s = r then (∫ p in triangleSet 1,
        (u (faceChart (Equiv.refl (Fin 3)) 0 s p)) ^ 2) else 0 := by
    by_cases hs : s = r <;> simp [hs]
  simp only [hi]
  simp

theorem reference_coord_bounds (x : Space) (hx : x ∈ coordinateChainSet) (j : Fin 3) :
    0 ≤ x j ∧ x j ≤ 1 := by
  have h := (coordinateChainSet_mem x).mp hx
  fin_cases j
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.2.1, h.2.2.2.1.trans h.2.1⟩
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.trans (h.2.2.2.1.trans h.2.1)⟩

theorem reference_vertex_bounds (r : Fin 4) (j : Fin 3) :
    0 ≤ referenceVertex r j ∧ referenceVertex r j ≤ 1 := by
  simp only [referenceVertex, chainVertex, Pi.zero_apply, zero_add]
  split_ifs <;> norm_num

theorem traceVector_partial_bound {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (r : Fin 4) (j : Fin 3) (x : Space) (hx : x ∈ coordinateChainSet) :
    fderiv ℝ (traceVector u r j) x (Pi.single j 1) ≤
      2 * (u x) ^ 2 + (fderiv ℝ u x (Pi.single j 1)) ^ 2 := by
  rw [traceVector_partial hu]
  obtain ⟨hx0, hx1⟩ := reference_coord_bounds x hx j
  obtain ⟨hv0, hv1⟩ := reference_vertex_bounds r j
  have hd : (x j - referenceVertex r j) ^ 2 ≤ 1 := by nlinarith
  have hm : ((x j - referenceVertex r j) * u x) ^ 2 ≤ (u x) ^ 2 := by
    nlinarith [sq_nonneg (u x),
      mul_nonneg (sq_nonneg (u x)) (show 0 ≤ 1 - (x j - referenceVertex r j) ^ 2 by linarith)]
  nlinarith [sq_nonneg ((x j - referenceVertex r j) * u x - fderiv ℝ u x (Pi.single j 1))]

theorem reference_smooth_face_trace {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (r : Fin 4) :
    (∫ p in triangleSet 1, (u (faceChart (Equiv.refl (Fin 3)) 0 r p)) ^ 2) ≤
      6 * (∫ x in coordinateChainSet, (u x) ^ 2) + ∑ j : Fin 3,
        ∫ x in coordinateChainSet, (fderiv ℝ u x (Pi.single j 1)) ^ 2 := by
  have iv (j : Fin 3) : IntegrableOn (fun x => fderiv ℝ (traceVector u r j) x (Pi.single j 1))
      coordinateChainSet :=
    ((traceVector_contDiff hu r j).continuous_fderiv (by norm_num)).clm_apply continuous_const
      |>.continuousOn.integrableOn_compact (μ := volume) coordinateChainSet_isCompact
  have iu : IntegrableOn (fun x => (u x) ^ 2) coordinateChainSet :=
    (hu.continuous.pow 2).continuousOn.integrableOn_compact (μ := volume) coordinateChainSet_isCompact
  have id (j : Fin 3) : IntegrableOn (fun x => (fderiv ℝ u x (Pi.single j 1)) ^ 2)
      coordinateChainSet :=
    (((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn.integrableOn_compact
      (μ := volume) coordinateChainSet_isCompact
  rw [face_square_eq_traceVector_divergence hu r]
  have hpoint (x : Space) (hx : x ∈ coordinateChainSet) :
      (∑ j : Fin 3, fderiv ℝ (traceVector u r j) x (Pi.single j 1)) ≤
        6 * (u x) ^ 2 + ∑ j : Fin 3, (fderiv ℝ u x (Pi.single j 1)) ^ 2 := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun j _ => traceVector_partial_bound hu r j x hx)
    simpa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      show (3 : ℝ) * 2 = 6 by norm_num] using hs
  have he := setIntegral_mono_on (integrable_finsetSum _ (fun j _ => iv j))
    ((iu.const_mul 6).add (integrable_finsetSum _ (fun j _ => id j)))
    coordinateChainSet_isCompact.measurableSet hpoint
  change (∫ x in coordinateChainSet, ∑ j : Fin 3,
      fderiv ℝ (traceVector u r j) x (Pi.single j 1)) ≤
    ∫ x in coordinateChainSet, 6 * (u x) ^ 2 + ∑ j : Fin 3,
      (fderiv ℝ u x (Pi.single j 1)) ^ 2 at he
  rw [integral_add (iu.const_mul 6) (integrable_finsetSum _ (fun j _ => id j)),
    integral_const_mul, integral_finsetSum _ (fun j _ => id j)] at he
  exact he

end FreudenthalSVLean.SmoothFaceTrace
