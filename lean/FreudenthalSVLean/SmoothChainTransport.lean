import FreudenthalSVLean.SmoothChainGauss
import FreudenthalSVLean.ScaledFaceGauss
import FreudenthalSVLean.PolynomialChainTransport

/-!
# Actual smooth affine transport for the initial mean-lift stage

For manuscript Lemma `means` and its trace scaling, smooth functions on
every positively scaled, translated and coordinate-permuted tetrahedron
are pulled back through the actual affine map.  Its true Frechet derivative,
coordinate derivative transport, face-chart correspondence and Lebesgue
volume scaling are proved.  The complete squared gradient sum is invariant
under the coordinate permutation and scales by the explicit factor h^2
on pullback.  No stability of a continuous divergence inverse or an
interpolation operator is assumed.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.PolynomialInverseEstimate

noncomputable section

namespace FreudenthalSVLean.SmoothChainTransport

set_option backward.isDefEq.respectTransparency false

def physicalPoint (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (x : Space) : Space :=
  h • (unitNormalize σ o).symm x

def linearPart (σ : Equiv.Perm (Fin 3)) (h : ℝ) : Space →L[ℝ] Space :=
  h • ContinuousLinearMap.pi (fun j : Fin 3 =>
    (ContinuousLinearMap.proj (σ.symm j) : Space →L[ℝ] ℝ))

theorem physicalPoint_eq (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    physicalPoint σ o h = fun x => linearPart σ h x + h • o := by
  funext x j
  simp [physicalPoint, linearPart, unitNormalize_symm_apply, Pi.smul_apply, smul_eq_mul, mul_add]

theorem physicalPoint_contDiff (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    ContDiff ℝ 1 (physicalPoint σ o h) := by
  rw [physicalPoint_eq]
  exact (linearPart σ h).contDiff.add contDiff_const

theorem physicalPoint_hasFDerivAt (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (x : Space) :
    HasFDerivAt (physicalPoint σ o h) (linearPart σ h) x := by
  rw [physicalPoint_eq]
  simpa only using! (linearPart σ h).hasFDerivAt.add_const (h • o)

theorem linearPart_single (σ : Equiv.Perm (Fin 3)) (h : ℝ) (j : Fin 3) :
    linearPart σ h (Pi.single j 1) = h • (Pi.single (σ j) 1 : Space) := by
  ext l
  by_cases hl : l = σ j
  · subst l
    simp [linearPart, Pi.single_apply]
  · have hs : σ.symm l ≠ j := by
      intro he
      apply hl
      rw [← he, Equiv.apply_symm_apply]
    simp [linearPart, Pi.single_apply, hl, hs]

theorem physicalPoint_partial {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (x : Space) (j : Fin 3) :
    fderiv ℝ (fun y => f (physicalPoint σ o h y)) x (Pi.single j 1) =
      h * fderiv ℝ f (physicalPoint σ o h x) (Pi.single (σ j) 1) := by
  have hd : HasFDerivAt f (fderiv ℝ f (physicalPoint σ o h x)) (physicalPoint σ o h x) :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hc : HasFDerivAt (fun y => f (physicalPoint σ o h y))
      ((fderiv ℝ f (physicalPoint σ o h x)).comp (linearPart σ h)) x := by
    simpa only [Function.comp_def] using! hd.comp x (physicalPoint_hasFDerivAt σ o h x)
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, linearPart_single, map_smul, smul_eq_mul]

theorem normalize_symm_faceChart (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (p : FacePoint) :
    (unitNormalize σ o).symm (faceChart (Equiv.refl (Fin 3)) 0 r p) = faceChart σ o r p := by
  let y := (unitNormalize σ o).symm (faceChart (Equiv.refl (Fin 3)) 0 r p)
  have hb (a : Fin 4) : eval y (ChainGeometry.barycentric σ o a) = faceBarycentric r p a := by
    rw [unitBarycentric_normalize]
    simp only [y, MeasurableEquiv.apply_symm_apply]
    exact faceChart_barycentric (Equiv.refl (Fin 3)) 0 r a p
  ext j
  have hc := VertexJetAlgebra.coordinate_reconstruction σ o y j
  simp only [hb] at hc
  exact hc.symm

theorem physicalPoint_faceChart (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) (p : FacePoint) :
    physicalPoint σ o h (faceChart (Equiv.refl (Fin 3)) 0 r p) = scaledFaceChart σ o h r p := by
  rw [physicalPoint, normalize_symm_faceChart]
  rfl

theorem physical_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (f : Space → ℝ) :
    (∫ x in scaledChainSet σ o h, f x) =
      h ^ 3 * ∫ y in coordinateChainSet, f (physicalPoint σ o h y) := by
  calc
    _ = ∫ x in scaledChainSet σ o h, f (h • (h⁻¹ • x)) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [smul_smul, hh.ne']
    _ = h ^ 3 * ∫ y in unitChainSet σ o, f (h • y) :=
      scaled_chain_integral σ o h hh (fun y => f (h • y))
    _ = _ := by
      rw [unit_integral_normalize]
      rfl

theorem pullback_gradient_square_integral {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    (∑ j : Fin 3, ∫ x in coordinateChainSet,
      (fderiv ℝ (fun y => f (physicalPoint σ o h y)) x (Pi.single j 1)) ^ 2) =
        h ^ 2 * ∑ j : Fin 3, ∫ x in coordinateChainSet,
          (fderiv ℝ f (physicalPoint σ o h x) (Pi.single j 1)) ^ 2 := by
  simp only [physicalPoint_partial hf, mul_pow, integral_const_mul]
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ => h ^ 2 * z)
    (Equiv.sum_comp σ (fun j : Fin 3 => ∫ x in coordinateChainSet,
      (fderiv ℝ f (physicalPoint σ o h x) (Pi.single j 1)) ^ 2))

end FreudenthalSVLean.SmoothChainTransport
