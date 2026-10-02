import FreudenthalSVLean.BarycentricPolynomialGauss
import FreudenthalSVLean.AffineBarycentric
import FreudenthalSVLean.MeshSegments
import Mathlib.Analysis.Convex.Combination

/-!
# Genuine spatial face charts and polynomial flux identities

For manuscript Lemma `means`, the reference triangular chart is mapped
to the actual three vertices of each translated unit Freudenthal face.
Its actual barycentric values are proved, its image lies on the correct
tetrahedron face, and its pointwise polynomial integrals agree with the
proved barycentric face integrals.  The resulting volume/face identity
applies to every spatial polynomial, with no degree or homogeneous-
representation hypothesis.  The weights are minus the actual barycentric
gradients; identification with Euclidean vector surface measure and the
continuous nonpolynomial trace stage are not asserted here.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.AffineBarycentric
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricPolynomialGauss
open FreudenthalSVLean.HomogeneousBarycentric
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.MeshSegments

noncomputable section

namespace FreudenthalSVLean.BarycentricFaceGeometry

set_option backward.isDefEq.respectTransparency false

theorem faceBarycentric_sum (r : Fin 4) (x : FacePoint) :
    (∑ a : Fin 4, faceBarycentric r x a) = 1 := by
  rw [Fin.sum_univ_succAbove _ r]
  simp [faceBarycentric, triangleBarycentric, Fin.sum_univ_succ]

theorem faceBarycentric_nonneg (r : Fin 4) (x : FacePoint) (hx : x ∈ triangleSet 1) :
    ∀ a : Fin 4, 0 ≤ faceBarycentric r x a := by
  apply (Fin.forall_iff_succAbove r (P := fun a => 0 ≤ faceBarycentric r x a)).mpr
  constructor
  · simp [faceBarycentric]
  · intro i
    simp only [faceBarycentric, Fin.insertNth_apply_succAbove]
    fin_cases i <;> dsimp [triangleBarycentric] <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]

def faceChart (σ : Equiv.Perm (Fin 3)) (o : Space) (r : Fin 4) (x : FacePoint) : Space :=
  affinePoint σ o (faceBarycentric r x)

theorem faceChart_barycentric (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r a : Fin 4) (x : FacePoint) :
    eval (faceChart σ o r x) (barycentric σ o a) = faceBarycentric r x a :=
  affinePoint_barycentric σ o _ (faceBarycentric_sum r x) a

theorem faceChart_missing_zero (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (x : FacePoint) : eval (faceChart σ o r x) (barycentric σ o r) = 0 := by
  rw [faceChart_barycentric]
  simp [faceBarycentric]

theorem faceChart_mem_unitChainSet (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (x : FacePoint) (hx : x ∈ triangleSet 1) : faceChart σ o r x ∈ unitChainSet σ o := by
  have hs := (unitChainSet_convex σ o).sum_mem (t := Finset.univ)
    (w := faceBarycentric r x) (z := chainVertex σ o)
    (fun a _ => faceBarycentric_nonneg r x hx a) (faceBarycentric_sum r x)
    (fun a _ => chainVertex_mem_unitChainSet σ o a)
  have he : (∑ a : Fin 4, faceBarycentric r x a • chainVertex σ o a) =
      faceChart σ o r x := by
    ext j
    simp [faceChart, affinePoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he] at hs
  exact hs

theorem faceChart_continuous (σ : Equiv.Perm (Fin 3)) (o : Space) (r : Fin 4) :
    Continuous (faceChart σ o r) := by
  apply continuous_pi
  intro j
  change Continuous (fun x => ∑ a : Fin 4, faceBarycentric r x a * chainVertex σ o a j)
  exact continuous_finsetSum _ (fun a _ =>
    ((continuous_apply a).comp (faceBarycentric_continuous r)).mul continuous_const)

def spatialFaceIntegral (σ : Equiv.Perm (Fin 3)) (o : Space) (r : Fin 4) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in triangleSet 1, eval (faceChart σ o r x) p
  map_add' p q := by
    simp only [map_add]
    exact integral_add
      (((continuous_eval p).comp (faceChart_continuous σ o r)).continuousOn
        |>.integrableOn_compact (μ := volume) (triangleSet_isCompact 1))
      (((continuous_eval q).comp (faceChart_continuous σ o r)).continuousOn
        |>.integrableOn_compact (μ := volume) (triangleSet_isCompact 1))
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

theorem spatialFaceIntegral_substitution (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r : Fin 4) (p : MvPolynomial (Fin 4) ℝ) :
    spatialFaceIntegral σ o r (eval₂Hom C (barycentric σ o) p) = faceIntegral r p := by
  apply integral_congr_ae
  filter_upwards with x
  rw [PolynomialCalculus.eval_substitution]
  exact congrArg (fun y : Fin 4 → ℝ => eval y p) (funext (fun a => faceChart_barycentric σ o r a x))

theorem spatial_polynomial_gauss (σ : Equiv.Perm (Fin 3)) (o : Space)
    (p : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j p) =
      ∑ r : Fin 4, -barycentricGradient (R := ℝ) σ r j * spatialFaceIntegral σ o r p := by
  let H := eval₂Hom C (coordinateForm σ o) p
  have he : eval₂Hom C (barycentric σ o) H = p := substitute_coordinateForms σ o p
  have hg := unit_polynomial_gauss σ o H j
  have hf (r : Fin 4) : faceIntegral r H = spatialFaceIntegral σ o r p := by
    rw [← spatialFaceIntegral_substitution, he]
  rw [he] at hg
  simpa only [hf] using hg

end FreudenthalSVLean.BarycentricFaceGeometry
