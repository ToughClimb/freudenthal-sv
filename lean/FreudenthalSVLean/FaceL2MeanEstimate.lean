import FreudenthalSVLean.WeakFaceGauss
import FreudenthalSVLean.TriangleBernsteinIntegral

/-!
# Exact face measure and bounds for weak normal flux

For the face correction estimate in manuscript Lemma `means`, the
parameter triangle has genuine Lebesgue area one half.  Cauchy--Schwarz
therefore bounds its integral functional by the actual L2 norm.  Combining
this with the proved physical outward cofactor vectors and weak face
traces gives the explicit inequality h^{-3} delta_F^2 <=
6 h^{-2} ||f||_{L2(T)}^2 + ||grad f||_{L2(T)}^2.  This supplies the local
estimate for a cubic face correction; it does not supply an interpolant
with the needed h-order error estimate or a continuous divergence inverse.
-/

open scoped BigOperators Topology
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakFaceGauss

noncomputable section

namespace FreudenthalSVLean.FaceL2MeanEstimate

set_option backward.isDefEq.respectTransparency false

theorem triangle_area : (volume : Measure FacePoint).real (triangleSet 1) = 1 / 2 := by
  have he := triangle_monomial_integral (0 : Fin 3 →₀ ℕ) (1 : ℝ)
  simp [BernsteinPolynomial.factorialProduct] at he
  simpa only [setIntegral_const, smul_eq_mul, mul_one, one_div] using he

def faceOne : FaceL2 := indicatorConstLp 2 MeasurableSet.univ faceMeasure_finite (1 : ℝ)

theorem faceOne_norm_square : ‖faceOne‖ ^ 2 = 1 / 2 := by
  rw [← real_inner_self_eq_norm_sq, faceOne,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one MeasurableSet.univ MeasurableSet.univ
      faceMeasure_finite faceMeasure_finite]
  simpa only [Set.inter_self, Measure.real, Measure.restrict_apply_univ] using triangle_area

theorem faceMean_eq_inner (T : FaceL2) : faceMean T = inner ℝ faceOne T := rfl

theorem faceMean_square_bound (T : FaceL2) : (faceMean T) ^ 2 ≤ (1 / 2 : ℝ) * ‖T‖ ^ 2 := by
  have ht := real_inner_mul_inner_self_le faceOne T
  rw [faceMean_eq_inner]
  simpa only [real_inner_self_eq_norm_sq, faceOne_norm_square, ← pow_two] using ht

def traceFlux (σ : Equiv.Perm (Fin 3)) (h : ℝ) (r : Fin 4) (T : Fin 3 → FaceL2) : ℝ :=
  ∑ j : Fin 3, outwardWeight σ h r j * faceMean (T j)

theorem outwardWeight_square_bound (σ : Equiv.Perm (Fin 3)) (h : ℝ) (r : Fin 4) :
    (∑ j : Fin 3, (outwardWeight σ h r j) ^ 2) ≤ 2 * h ^ 4 := by
  rw [outwardWeight_square_sum]
  split_ifs <;> nlinarith [pow_nonneg (sq_nonneg h) 2]

theorem traceFlux_square_bound (σ : Equiv.Perm (Fin 3)) (h : ℝ) (r : Fin 4)
    (T : Fin 3 → FaceL2) : (traceFlux σ h r T) ^ 2 ≤ h ^ 4 * ∑ j : Fin 3, ‖T j‖ ^ 2 := by
  have hw := outwardWeight_square_bound σ h r
  have hm : (∑ j : Fin 3, (faceMean (T j)) ^ 2) ≤ (1 / 2 : ℝ) * ∑ j : Fin 3, ‖T j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => faceMean_square_bound (T j))
  have ht := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (outwardWeight σ h r) (fun j => faceMean (T j))
  calc
    _ ≤ (∑ j : Fin 3, (outwardWeight σ h r j) ^ 2) *
        ∑ j : Fin 3, (faceMean (T j)) ^ 2 := ht
    _ ≤ (2 * h ^ 4) * ((1 / 2 : ℝ) * ∑ j : Fin 3, ‖T j‖ ^ 2) :=
      mul_le_mul hw hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

theorem weak_traceFlux_scale_bound (f : Fin 3 → Space → ℝ)
    (g : Fin 3 → Fin 3 → Space → ℝ) (hf : ∀ j, ∃ u, SmoothH1Approximation (f j) (g j) u)
    (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (hh : 0 < h) (r : Fin 4)
    (T : Fin 3 → FaceL2) (hT : ∀ j, HasH1FaceTrace (f j) (g j) σ o h r (T j)) :
    (h ^ 3)⁻¹ * (traceFlux σ h r T) ^ 2 ≤
      6 * (h ^ 2)⁻¹ * (∑ j : Fin 3, ∫ x in scaledChainSet σ o h, (f j x) ^ 2) +
        ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in scaledChainSet σ o h, (g j i x) ^ 2 := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => weak_face_trace_bound (hf j) σ o h hh r (hT j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at ht
  have hflux := traceFlux_square_bound σ h r T
  have hb : (traceFlux σ h r T) ^ 2 ≤ h ^ 2 *
      (6 * h⁻¹ * (∑ j : Fin 3, ∫ x in scaledChainSet σ o h, (f j x) ^ 2) +
        h * ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in scaledChainSet σ o h, (g j i x) ^ 2) := by
    calc
      _ ≤ _ := hflux
      _ = h ^ 2 * (h ^ 2 * ∑ j : Fin 3, ‖T j‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (sq_nonneg h)
  calc
    _ ≤ (h ^ 3)⁻¹ * (h ^ 2 *
        (6 * h⁻¹ * (∑ j : Fin 3, ∫ x in scaledChainSet σ o h, (f j x) ^ 2) +
          h * ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in scaledChainSet σ o h, (g j i x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      field_simp [hh.ne']

end FreudenthalSVLean.FaceL2MeanEstimate
