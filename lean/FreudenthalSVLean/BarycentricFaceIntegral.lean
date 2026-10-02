import FreudenthalSVLean.TriangleBernsteinIntegral
import FreudenthalSVLean.BarycentricMonomialMean

/-!
# Actual barycentric face integrals for the initial mean-lift stage

For manuscript Lemma `means`, each face restriction is integrated over
the genuine two-dimensional reference triangle by setting its omitted
barycentric coordinate to zero.  Arbitrary monomials have zero integral
when that coordinate has a positive exponent and the symmetric factorial
value otherwise.  The face functional is linear by actual integrability.
The spatial outward-vector and scale transport are not assumed here.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.ReferenceChainMeasure
open FreudenthalSVLean.BernsteinPolynomial

noncomputable section

namespace FreudenthalSVLean.BarycentricFaceIntegral

set_option backward.isDefEq.respectTransparency false

def faceBarycentric (r : Fin 4) (p : FacePoint) : Fin 4 → ℝ :=
  r.insertNth 0 (triangleBarycentric p)

theorem faceBarycentric_continuous (r : Fin 4) : Continuous (faceBarycentric r) :=
  continuous_const.finInsertNth r triangleBarycentric_continuous

theorem face_polynomial_integrable (r : Fin 4) (p : MvPolynomial (Fin 4) ℝ) :
    IntegrableOn (fun x => eval (faceBarycentric r x) p) (triangleSet 1) :=
  ((continuous_eval p).comp (faceBarycentric_continuous r)).continuousOn
    |>.integrableOn_compact (μ := volume) (triangleSet_isCompact 1)

def faceIntegral (r : Fin 4) : MvPolynomial (Fin 4) ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in triangleSet 1, eval (faceBarycentric r x) p
  map_add' p q := by
    simp only [map_add]
    exact integral_add (face_polynomial_integrable r p) (face_polynomial_integrable r q)
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

theorem face_eval_monomial (r : Fin 4) (α : Fin 4 →₀ ℕ) (c : ℝ) (x : FacePoint) :
    eval (faceBarycentric r x) (monomial α c) = c *
      ((0 : ℝ) ^ (α r) * ∏ i : Fin 3, (triangleBarycentric x i) ^ (α (r.succAbove i))) := by
  classical
  rw [eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_succAbove _ r]
    simp only [faceBarycentric, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  · intro i
    simp

theorem face_monomial_zero {r : Fin 4} (α : Fin 4 →₀ ℕ) (c : ℝ) (hr : α r ≠ 0) :
    faceIntegral r (monomial α c) = 0 := by
  change (∫ x in triangleSet 1, eval (faceBarycentric r x) (monomial α c)) = 0
  simp only [face_eval_monomial, zero_pow hr, zero_mul, mul_zero, integral_zero]

theorem face_monomial_mean {r : Fin 4} (α : Fin 4 →₀ ℕ) (c : ℝ) (hr : α r = 0) :
    faceIntegral r (monomial α c) = c * factorialProduct α /
      (Nat.factorial (α.degree + 2) : ℝ) := by
  let a := α (r.succAbove 0)
  let b := α (r.succAbove 1)
  let d := α (r.succAbove 2)
  have he (x : FacePoint) : eval (faceBarycentric r x) (monomial α c) =
      c * ((1 - x.1) ^ a * ((x.1 - x.2) ^ b * x.2 ^ d)) := by
    rw [face_eval_monomial]
    simp [hr, triangleBarycentric, Fin.prod_univ_succ, a, b, d]
  have hd : α.degree = a + b + d := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succAbove _ r]
    simp only [hr, zero_add]
    simp [a, b, d, Fin.sum_univ_succ]
    omega
  have hf : factorialProduct (R := ℝ) α =
      (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial d : ℝ) := by
    rw [factorialProduct, Fin.prod_univ_succAbove _ r]
    simp [hr, a, b, d, Fin.prod_univ_succ]
    ring
  change (∫ x in triangleSet 1, eval (faceBarycentric r x) (monomial α c)) = _
  simp_rw [he, integral_const_mul]
  rw [triangle_barycentric_powers, hd, hf]
  ring

theorem faceIntegral_monomial (r : Fin 4) (α : Fin 4 →₀ ℕ) (c : ℝ) :
    faceIntegral r (monomial α c) = if α r = 0 then
      c * factorialProduct α / (Nat.factorial (α.degree + 2) : ℝ) else 0 := by
  by_cases hr : α r = 0
  · rw [if_pos hr]
    exact face_monomial_mean α c hr
  · rw [if_neg hr]
    exact face_monomial_zero α c hr

theorem faceIntegral_C_mul (r : Fin 4) (c : ℝ) (p : MvPolynomial (Fin 4) ℝ) :
    faceIntegral r (C c * p) = c * faceIntegral r p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

end FreudenthalSVLean.BarycentricFaceIntegral
