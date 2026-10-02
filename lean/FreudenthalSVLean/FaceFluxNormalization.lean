import FreudenthalSVLean.ScaledFaceGauss
import FreudenthalSVLean.ActualFaceMean

/-!
# Exact face-bubble flux normalization

For the face correction in manuscript Lemma `means`, the continuous
cubic product of the three face barycentric coordinates has parameter
integral exactly `1/120` on that face, and zero on each other face of
the tetrahedron.  The corresponding actual physical vector field thus
has exactly one nonzero parameter-flux functional, equal to its genuine
divergence mean.  The statement applies to arbitrary positive mesh size.
These results concern actual polynomial fields and actual face integrals;
the uniform lift from general mean data is a separate obligation.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean

noncomputable section

namespace FreudenthalSVLean.FaceFluxNormalization

set_option backward.isDefEq.respectTransparency false

theorem faceExponent_factorialProduct (r : Fin 4) :
    factorialProduct (R := ℝ) (faceExponent r) = 1 := by
  apply Finset.prod_eq_one
  intro a _
  simp only [faceExponent_apply]
  by_cases ha : a = r <;> simp [ha]

theorem face_bubble_parameter_integral (r s : Fin 4) :
    faceIntegral s (faceBarycentricPolynomial r) = if s = r then 1 / 120 else 0 := by
  classical
  rw [faceBarycentricPolynomial, faceIntegral_monomial,
    faceExponent_factorialProduct, faceExponent_degree]
  by_cases h : s = r <;> norm_num [faceExponent_apply, h]

theorem spatial_face_bubble_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r s : Fin 4) : spatialFaceIntegral σ o s (spatialFaceBubble σ o r) =
      if s = r then 1 / 120 else 0 := by
  rw [spatialFaceBubble, spatialFaceIntegral_substitution, face_bubble_parameter_integral]

theorem scaled_face_bubble_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r s : Fin 4) :
    scaledFaceIntegral σ o h s (rescale h 1 (spatialFaceBubble σ o r)) =
      if s = r then 1 / 120 else 0 := by
  rw [scaledFaceIntegral_rescale σ o h hh, one_mul, spatial_face_bubble_integral]

def polynomialFlux (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (r : Fin 4)
    (v : Fin 3 → MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∑ j : Fin 3, outwardWeight σ h r j * scaledFaceIntegral σ o h r (v j)

theorem divergence_eq_flux_sum (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (v : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∫ x in ScaledChainGeometry.scaledChainSet σ o h,
      eval x (PolynomialCalculus.polynomialDivergence v)) =
        ∑ r : Fin 4, polynomialFlux σ o h r v :=
  scaled_polynomial_divergence_gauss σ o h hh v

theorem scaled_face_vector_flux (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (r s : Fin 4) (a : Space) :
    polynomialFlux σ o h s (fun j => rescale h 1 (C (a j) * spatialFaceBubble σ o r)) =
      if s = r then (∑ j : Fin 3, outwardWeight σ h r j * a j) / 120 else 0 := by
  classical
  have hp (j : Fin 3) : rescale h 1 (C (a j) * spatialFaceBubble σ o r) =
      a j • rescale h 1 (spatialFaceBubble σ o r) := by
    simp [rescale, map_mul, smul_eq_C_mul, mul_comm]
  simp only [polynomialFlux, hp, map_smul, smul_eq_mul,
    scaled_face_bubble_integral σ o h hh]
  by_cases he : s = r
  · simp only [he, if_true, div_eq_mul_inv, one_mul, Finset.sum_mul, mul_assoc]
  · simp [he]

theorem actual_face_scalar_integral {N : ℕ} (hN : 0 < N) (t : Tet N) (r s : Fin 4) :
    scaledFaceIntegral t.2 (cellOrigin t.1) (meshScale N) s (faceScalar t r t) =
      if s = r then 1 / 120 else 0 := by
  rw [faceScalar_self_rescale]
  exact scaled_face_bubble_integral t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN).ne' r s

theorem actual_face_vector_flux {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r s : Fin 4) (a : Space) :
    polynomialFlux t.2 (cellOrigin t.1) (meshScale N) s (faceField N t r a t) =
      if s = r then (∑ j : Fin 3, outwardWeight t.2 (meshScale N) r j * a j) / 120 else 0 := by
  have he : faceField N t r a t = fun j =>
      rescale (meshScale N) 1 (C (a j) * spatialFaceBubble t.2 (cellOrigin t.1) r) := by
    funext j
    exact faceField_self_rescale t r a j
  rw [he]
  exact scaled_face_vector_flux t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN).ne' r s a

theorem actual_face_mean_eq_designated_flux {N : ℕ} (hN : 0 < N)
    (t : Tet N) (r : Fin 4) (a : Space) :
    (∫ x in tetrahedron t, eval x (divergence N (faceField N t r a) t)) =
      polynomialFlux t.2 (cellOrigin t.1) (meshScale N) r (faceField N t r a t) := by
  change (∫ x in ScaledChainGeometry.scaledChainSet t.2 (cellOrigin t.1) (meshScale N),
    eval x (PolynomialCalculus.polynomialDivergence (faceField N t r a t))) = _
  rw [divergence_eq_flux_sum t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN)]
  simp only [actual_face_vector_flux hN]
  simp

end FreudenthalSVLean.FaceFluxNormalization
