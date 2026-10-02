import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Degree preservation under affine coordinate changes

The manuscript's reference-element and `macro-scale` arguments transport
fixed-degree polynomials between translated, permuted, and scaled
tetrahedra.  This module proves that substitution by polynomials of degree
at most one cannot increase the total degree.  The proof works from the
actual monomial support and does not assume an affine invariance theorem.
-/

open scoped BigOperators
open MvPolynomial

namespace FreudenthalSVLean.PolynomialDegree

variable {σ τ R : Type*} [CommSemiring R]

theorem affine_substitution_degree (q : σ → MvPolynomial τ R)
    (hq : ∀ i, (q i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (eval₂Hom C q p).totalDegree ≤ p.totalDegree := by
  classical
  have he := congrArg (eval₂Hom C q) p.as_sum
  rw [map_sum] at he
  rw [he]
  apply totalDegree_finsetSum_le
  intro α hα
  rw [eval₂Hom_monomial]
  calc
    (C (coeff α p) * α.prod (fun i n => q i ^ n)).totalDegree ≤
        (C (coeff α p)).totalDegree + (α.prod (fun i n => q i ^ n)).totalDegree :=
      totalDegree_mul _ _
    _ = (α.prod (fun i n => q i ^ n)).totalDegree := by simp
    _ ≤ ∑ i ∈ α.support, (q i ^ α i).totalDegree :=
      totalDegree_finsetProd α.support (fun i => q i ^ α i)
    _ ≤ ∑ i ∈ α.support, α i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (α i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hα

/-- Differentiation lowers the total degree, with the zero and constant
cases covered by natural-number truncated subtraction.  This gives the
`P_{k-1}` elementwise pressure degree in the manuscript's definition of
`Q_{h,k}=div V_{h,k}`. -/
theorem pderiv_degree_le (i : σ) (p : MvPolynomial σ R) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro α hα
  have hc : coeff (α + Finsupp.single i 1) p ≠ 0 := by
    intro hz
    have hn := mem_support_iff.mp hα
    apply hn
    rw [coeff_pderiv, hz, zero_mul]
  have hs := le_totalDegree (mem_support_iff.mpr hc)
  have he : (α + Finsupp.single i 1).sum (fun _ n => n) =
      α.sum (fun _ n => n) + 1 := by
    rw [Finsupp.sum_add_index']
    · simp
    · simp
    · intros
      rfl
  rw [he] at hs
  omega

section Ring

variable {S : Type*} [CommRing S]

theorem neg_degree_le (p : MvPolynomial σ S) : (-p).totalDegree ≤ p.totalDegree := by
  simpa only [neg_one_smul] using totalDegree_smul_le (-1 : S) p

theorem sub_degree_le (p q : MvPolynomial σ S) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (totalDegree_add _ _).trans (max_le_max le_rfl (neg_degree_le q))

end Ring

end FreudenthalSVLean.PolynomialDegree
