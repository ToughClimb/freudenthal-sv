import FreudenthalSVLean.BarycentricFaceGeometry
import FreudenthalSVLean.PolynomialScaling
import FreudenthalSVLean.MeshIntersectionFaces

/-!
# Actual face charts, flux weights, and Gauss identities at every mesh scale

For manuscript Lemma `means`, the triangle chart is scaled to the actual
face of every positive-scale Freudenthal tetrahedron.  Its barycentric
coordinates, containment, polynomial face integrals, and divergence means
are proved from the already established reference integration identities.
The flux weights are proved to be orthogonal to face displacements and
to point out of the tetrahedron.  Their squared Euclidean component sum
is computed exactly.  No surface trace theorem for nonpolynomial H1
functions, or uniform initial mean lifting statement, is assumed here.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.ScaledFaceGauss

set_option backward.isDefEq.respectTransparency false

def scaledFaceChart (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (r : Fin 4) (x : FacePoint) : Space := h • faceChart σ o r x

theorem scaledFaceChart_continuous (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (r : Fin 4) : Continuous (scaledFaceChart σ o h r) :=
  (faceChart_continuous σ o r).const_smul h

theorem scaledFaceChart_barycentric (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r a : Fin 4) (x : FacePoint) :
    eval (scaledFaceChart σ o h r x) (scaledBarycentric σ o h a) =
      faceBarycentric r x a := by
  rw [scaledBarycentric_eval]
  simp only [scaledFaceChart, smul_smul, inv_mul_cancel₀ hh, one_smul]
  exact faceChart_barycentric σ o r a x

theorem scaledFaceChart_mem (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r : Fin 4) (x : FacePoint) (hx : x ∈ triangleSet 1) :
    scaledFaceChart σ o h r x ∈ scaledChainSet σ o h := by
  change h⁻¹ • (h • faceChart σ o r x) ∈ unitChainSet σ o
  rw [smul_smul, inv_mul_cancel₀ hh, one_smul]
  exact faceChart_mem_unitChainSet σ o r x hx

def scaledFaceIntegral (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in triangleSet 1, eval (scaledFaceChart σ o h r x) p
  map_add' p q := by
    simp only [map_add]
    exact integral_add
      (((continuous_eval p).comp (scaledFaceChart_continuous σ o h r)).continuousOn
        |>.integrableOn_compact (μ := volume) (triangleSet_isCompact 1))
      (((continuous_eval q).comp (scaledFaceChart_continuous σ o h r)).continuousOn
        |>.integrableOn_compact (μ := volume) (triangleSet_isCompact 1))
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

theorem scaledFaceIntegral_rescale (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (a : ℝ) (r : Fin 4) (p : MvPolynomial (Fin 3) ℝ) :
    scaledFaceIntegral σ o h r (rescale h a p) = a * spatialFaceIntegral σ o r p := by
  change (∫ x in triangleSet 1, eval (scaledFaceChart σ o h r x) (rescale h a p)) = _
  simp only [rescale_eval, scaledFaceChart, smul_smul, inv_mul_cancel₀ hh, one_smul]
  exact integral_const_mul a _

theorem rescale_inverse (h : ℝ) (hh : h ≠ 0) (p : MvPolynomial (Fin 3) ℝ) :
    rescale h 1 (rescale h⁻¹ 1 p) = p := by
  apply MvPolynomial.funext
  intro x
  simp [rescale_eval, smul_smul, hh]

def outwardWeight (σ : Equiv.Perm (Fin 3)) (h : ℝ) (r : Fin 4) : Space :=
  fun j => -h ^ 2 * barycentricGradient σ r j

/-- Polynomial Gauss identity in actual spatial coordinates at arbitrary
positive scale.  Both the volume and parameter-face integrals are genuine. -/
theorem scaled_polynomial_gauss (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    (∫ y in scaledChainSet σ o h, eval y (pderiv j p)) =
      ∑ r : Fin 4, outwardWeight σ h r j * scaledFaceIntegral σ o h r p := by
  let q := rescale h⁻¹ 1 p
  have he : rescale h 1 q = p := rescale_inverse h hh.ne' p
  rw [← he, derivative_mean_scaling σ o h hh, one_mul]
  change h ^ 2 * FaceBubbleMean.unitSpatialIntegral σ o (pderiv j q) = _
  rw [spatial_polynomial_gauss, Finset.mul_sum]
  simp only [scaledFaceIntegral_rescale σ o h hh.ne', one_mul, outwardWeight]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem scaled_polynomial_divergence_gauss (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (v : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∫ y in scaledChainSet σ o h, eval y (PolynomialCalculus.polynomialDivergence v)) =
      ∑ r : Fin 4, ∑ j : Fin 3,
        outwardWeight σ h r j * scaledFaceIntegral σ o h r (v j) := by
  simp only [PolynomialCalculus.polynomialDivergence, map_sum]
  rw [integral_finsetSum]
  · simp only [scaled_polynomial_gauss σ o h hh]
    exact Finset.sum_comm
  · intro j _
    exact (continuous_eval (pderiv j (v j))).continuousOn.integrableOn_compact
      (μ := volume) (scaledChainSet_isCompact σ o h hh.ne')

theorem outwardWeight_dot_displacement (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r : Fin 4) (x : FacePoint) (y : Space) :
    (∑ j : Fin 3, outwardWeight σ h r j * (y j - scaledFaceChart σ o h r x j)) =
      -h ^ 3 * eval y (scaledBarycentric σ o h r) := by
  have hd := VertexJetAlgebra.gradient_dot_displacement σ o
    (faceChart σ o r x) (h⁻¹ • y) r
  rw [faceChart_missing_zero, sub_zero, ← scaledBarycentric_eval] at hd
  calc
    _ = -h ^ 3 * ∑ j : Fin 3,
        barycentricGradient (R := ℝ) σ r j * ((h⁻¹ • y) j - faceChart σ o r x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [outwardWeight, scaledFaceChart, Pi.smul_apply, smul_eq_mul]
      field_simp [hh]
    _ = _ := by rw [hd]

theorem outwardWeight_face_orthogonal (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r : Fin 4) (x z : FacePoint) :
    (∑ j : Fin 3, outwardWeight σ h r j *
      (scaledFaceChart σ o h r z j - scaledFaceChart σ o h r x j)) = 0 := by
  rw [outwardWeight_dot_displacement σ o h hh, scaledFaceChart_barycentric σ o h hh]
  simp [faceBarycentric]

theorem outwardWeight_points_outward (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (r : Fin 4) (x : FacePoint) (y : Space)
    (hy : y ∈ scaledChainSet σ o h) :
    (∑ j : Fin 3, outwardWeight σ h r j * (y j - scaledFaceChart σ o h r x j)) ≤ 0 := by
  rw [outwardWeight_dot_displacement σ o h hh.ne']
  have hb : 0 ≤ eval y (scaledBarycentric σ o h r) := by
    rw [scaledBarycentric_eval]
    exact MeshIntersectionFaces.unit_barycentric_nonneg σ o _ hy r
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hh.le 3)) hb

theorem outwardWeight_square_sum (σ : Equiv.Perm (Fin 3)) (h : ℝ) (r : Fin 4) :
    (∑ j : Fin 3, (outwardWeight σ h r j) ^ 2) =
      h ^ 4 * (if r = 0 ∨ r = 3 then 1 else 2) := by
  simp only [outwardWeight, mul_pow, neg_sq]
  rw [← Finset.mul_sum, face_gradient_norm_square]
  ring

theorem mesh_polynomial_gauss {N : ℕ} (hN : 0 < N) (t : Tet N)
    (p : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    (∫ y in tetrahedron t, eval y (pderiv j p)) =
      ∑ r : Fin 4, outwardWeight t.2 (meshScale N) r j *
        scaledFaceIntegral t.2 (cellOrigin t.1) (meshScale N) r p :=
  scaled_polynomial_gauss t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) p j

end FreudenthalSVLean.ScaledFaceGauss
