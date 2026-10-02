import FreudenthalSVLean.SmoothFaceTrace
import FreudenthalSVLean.SmoothChainTransport

/-!
# Smooth Gauss and face-trace estimates on the actual mesh

For the initial element-mean lift in manuscript Lemma `means`, the genuine
reference C1 Gauss and face-trace formulas are transported to every
positive-scale Freudenthal tetrahedron.  The flux weights are the actual
outward cofactor vectors already identified in `ScaledFaceGauss`.  The
trace estimate has explicit constant six and the powers h^{-1} and h;
both the volume and the parameter-face integrals are Lebesgue integrals.
The proof uses a single affine transport for every orientation, rather
than a finite list of scale-specific identities.  Extension to weak H1
traces and the uniform initial element-mean lift remain separate claims.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.SmoothChainGauss
open FreudenthalSVLean.SmoothFaceTrace
open FreudenthalSVLean.SmoothChainTransport
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.ScaledSmoothCalculus

set_option backward.isDefEq.respectTransparency false

theorem barycentricGradient_permutation (σ : Equiv.Perm (Fin 3))
    (r : Fin 4) (j : Fin 3) :
    barycentricGradient (R := ℝ) σ r j =
      barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) r (σ.symm j) := by
  have he := pderiv_forward σ (0 : Space)
    (ChainGeometry.barycentric (Equiv.refl (Fin 3)) (0 : Space) r) j
  rw [forward_barycentric, pderiv_barycentric, pderiv_barycentric] at he
  have hval := congrArg (MvPolynomial.eval (0 : Space)) he
  simpa only [forward, eval₂Hom_C, RingHom.id_apply, eval_C] using hval

theorem scaled_smooth_gauss {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (j : Fin 3) :
    (∫ x in scaledChainSet σ o h, fderiv ℝ f x (Pi.single j 1)) =
      ∑ r : Fin 4, outwardWeight σ h r j *
        ∫ p in triangleSet 1, f (scaledFaceChart σ o h r p) := by
  have hp : ContDiff ℝ 1 (fun x => f (physicalPoint σ o h x)) :=
    hf.comp (physicalPoint_contDiff σ o h)
  have ht := reference_smooth_gauss hp (σ.symm j)
  simp only [physicalPoint_partial hf, Equiv.apply_symm_apply, integral_const_mul,
    physicalPoint_faceChart] at ht
  rw [physical_integral σ o h hh]
  calc
    _ = h ^ 2 * (h * ∫ x in coordinateChainSet,
        fderiv ℝ f (physicalPoint σ o h x) (Pi.single j 1)) := by ring
    _ = h ^ 2 * ∑ r : Fin 4,
        -barycentricGradient (R := ℝ) (Equiv.refl (Fin 3)) r (σ.symm j) *
          ∫ p in triangleSet 1, f (scaledFaceChart σ o h r p) := by rw [ht]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [outwardWeight, barycentricGradient_permutation σ]
      ring

theorem scaled_smooth_vector_gauss (v : Fin 3 → Space → ℝ)
    (hv : ∀ j, ContDiff ℝ 1 (v j)) (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) :
    (∫ x in scaledChainSet σ o h, ∑ j : Fin 3,
      fderiv ℝ (v j) x (Pi.single j 1)) =
        ∑ r : Fin 4, ∫ p in triangleSet 1, ∑ j : Fin 3,
          outwardWeight σ h r j * v j (scaledFaceChart σ o h r p) := by
  have iv (j : Fin 3) : IntegrableOn
      (fun x => fderiv ℝ (v j) x (Pi.single j 1)) (scaledChainSet σ o h) :=
    (((hv j).continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn
      |>.integrableOn_compact (μ := volume) (scaledChainSet_isCompact σ o h hh.ne')
  have ifc (r : Fin 4) (j : Fin 3) : IntegrableOn
      (fun p => outwardWeight σ h r j * v j (scaledFaceChart σ o h r p)) (triangleSet 1) :=
    (((hv j).continuous.comp (scaledFaceChart_continuous σ o h r)).const_mul
      (outwardWeight σ h r j)).continuousOn.integrableOn_compact
        (μ := volume) (triangleSet_isCompact 1)
  rw [integral_finsetSum _ (fun j _ => iv j)]
  calc
    _ = ∑ j : Fin 3, ∑ r : Fin 4, outwardWeight σ h r j *
        ∫ p in triangleSet 1, v j (scaledFaceChart σ o h r p) := by
      apply Finset.sum_congr rfl
      intro j _
      exact scaled_smooth_gauss (hv j) σ o h hh j
    _ = ∑ r : Fin 4, ∑ j : Fin 3, outwardWeight σ h r j *
        ∫ p in triangleSet 1, v j (scaledFaceChart σ o h r p) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [integral_finsetSum _ (fun j _ => ifc r j)]
      simp only [integral_const_mul]

theorem scaled_smooth_face_trace {u : Space → ℝ} (hu : ContDiff ℝ 1 u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4) :
    h ^ 2 * (∫ p in triangleSet 1, (u (scaledFaceChart σ o h r p)) ^ 2) ≤
      6 * h⁻¹ * (∫ x in scaledChainSet σ o h, (u x) ^ 2) +
        h * ∑ j : Fin 3, ∫ x in scaledChainSet σ o h,
          (fderiv ℝ u x (Pi.single j 1)) ^ 2 := by
  have hp : ContDiff ℝ 1 (fun x => u (physicalPoint σ o h x)) :=
    hu.comp (physicalPoint_contDiff σ o h)
  have ht := reference_smooth_face_trace hp r
  simp only [physicalPoint_faceChart] at ht
  rw [pullback_gradient_square_integral hu] at ht
  have hv := physical_integral σ o h hh (fun x => (u x) ^ 2)
  have hg : (∑ j : Fin 3, ∫ x in scaledChainSet σ o h,
      (fderiv ℝ u x (Pi.single j 1)) ^ 2) =
      h ^ 3 * ∑ j : Fin 3, ∫ x in coordinateChainSet,
        (fderiv ℝ u (physicalPoint σ o h x) (Pi.single j 1)) ^ 2 := by
    simp only [physical_integral σ o h hh, ← Finset.mul_sum]
  calc
    _ ≤ h ^ 2 * (6 * (∫ x in coordinateChainSet, (u (physicalPoint σ o h x)) ^ 2) +
        h ^ 2 * ∑ j : Fin 3, ∫ x in coordinateChainSet,
          (fderiv ℝ u (physicalPoint σ o h x) (Pi.single j 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg h)
    _ = _ := by
      rw [hv, hg]
      field_simp [hh.ne']

theorem mesh_smooth_gauss {N : ℕ} (hN : 0 < N) (t : Tet N)
    {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    (∫ x in tetrahedron t, fderiv ℝ f x (Pi.single j 1)) =
      ∑ r : Fin 4, outwardWeight t.2 (meshScale N) r j *
        ∫ p in triangleSet 1, f (scaledFaceChart t.2 (cellOrigin t.1) (meshScale N) r p) :=
  scaled_smooth_gauss hf t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) j

theorem mesh_smooth_face_trace {N : ℕ} (hN : 0 < N) (t : Tet N)
    {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (r : Fin 4) :
    (meshScale N) ^ 2 * (∫ p in triangleSet 1,
      (u (scaledFaceChart t.2 (cellOrigin t.1) (meshScale N) r p)) ^ 2) ≤
      6 * (meshScale N)⁻¹ * (∫ x in tetrahedron t, (u x) ^ 2) +
        meshScale N * ∑ j : Fin 3, ∫ x in tetrahedron t,
          (fderiv ℝ u x (Pi.single j 1)) ^ 2 :=
  scaled_smooth_face_trace hu t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) r

end FreudenthalSVLean.ScaledSmoothCalculus
