import FreudenthalSVLean.BernsteinMean
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaled Freudenthal tetrahedra and exact integral scaling

For the manuscript's mesh definition and scaling arguments, this module
defines a tetrahedron at arbitrary positive scale `h` from the unit chain.
Its barycentric coordinates are actual polynomial substitutions.  The
Lebesgue change-of-scale formula has factor `h^3`; it is not assumed as
a property of a discrete coefficient functional.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.BernsteinPolynomial

noncomputable section

namespace FreudenthalSVLean.ScaledChainGeometry

def scaledChainSet (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) : Set Space :=
  (fun x => h⁻¹ • x) ⁻¹' unitChainSet σ o

def scaledVertex (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) (a : Fin 4) : Space :=
  h • ChainGeometry.chainVertex σ o a

def scaledBarycentric (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (i : Fin 4) : MvPolynomial (Fin 3) ℝ :=
  eval₂Hom C (fun j => C h⁻¹ * X j) (ChainGeometry.barycentric σ o i)

theorem scaledBarycentric_eval (σ : Equiv.Perm (Fin 3)) (o x : Space) (h : ℝ)
    (i : Fin 4) :
    eval x (scaledBarycentric σ o h i) =
      eval (h⁻¹ • x) (ChainGeometry.barycentric σ o i) := by
  rw [scaledBarycentric, PolynomialCalculus.eval_substitution]
  simp [Pi.smul_def, smul_eq_mul]

theorem scaledBarycentric_vertex (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (i a : Fin 4) :
    eval (scaledVertex σ o h a) (scaledBarycentric σ o h i) =
      if i = a then 1 else 0 := by
  rw [scaledBarycentric_eval]
  simp only [scaledVertex, smul_smul, inv_mul_cancel₀ hh, one_smul]
  exact ChainGeometry.barycentric_vertex σ o i a

theorem scaledBarycentric_sum (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    (∑ i : Fin 4, scaledBarycentric σ o h i) = 1 := by
  simp only [scaledBarycentric, ← map_sum, ChainGeometry.barycentric_sum, map_one]

theorem pderiv_scaledBarycentric (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (i : Fin 4) (j : Fin 3) :
    pderiv j (scaledBarycentric σ o h i) =
      C (h⁻¹ * ChainGeometry.barycentricGradient σ i j) := by
  rw [scaledBarycentric, PolynomialCalculus.pderiv_substitution]
  simp [ChainGeometry.pderiv_barycentric, pderiv_X, Pi.single_apply,
    C_mul, mul_comm]

theorem scaledChainSet_isCompact (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) : IsCompact (scaledChainSet σ o h) := by
  have hs : scaledChainSet σ o h = (fun y : Space => h • y) '' unitChainSet σ o := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ • x, hx, by simp [smul_smul, hh]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [scaledChainSet, Set.mem_preimage, smul_smul,
        inv_mul_cancel₀ hh, one_smul] using hy
  rw [hs]
  exact (unitChainSet_isCompact σ o).image (continuous_const_smul h)

/-- Genuine three-dimensional volume scaling, for an arbitrary integrand.
The theorem also covers nonintegrable functions under the Bochner convention. -/
theorem scaled_chain_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (f : Space → ℝ) :
    (∫ x in scaledChainSet σ o h, f (h⁻¹ • x)) =
      h ^ 3 * ∫ y in unitChainSet σ o, f y := by
  have hu := (unitChainSet_isCompact σ o).measurableSet
  have hs := (scaledChainSet_isCompact σ o h hh.ne').measurableSet
  rw [← integral_indicator hs, ← integral_indicator hu]
  have he : (scaledChainSet σ o h).indicator (fun x => f (h⁻¹ • x)) =
      fun x => (unitChainSet σ o).indicator f (h⁻¹ • x) := by
    funext x
    by_cases hx : h⁻¹ • x ∈ unitChainSet σ o
    · simp [scaledChainSet, hx]
    · simp [scaledChainSet, hx]
  rw [he]
  simpa [Module.finrank_pi, smul_eq_mul] using
    (Measure.integral_comp_inv_smul_of_nonneg volume
      ((unitChainSet σ o).indicator f) hh.le)

/-- Bernstein volume integration on every positive-scale tetrahedron. -/
theorem scaled_bernstein_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (d : ℕ) (α : Fin 4 →₀ ℕ) :
    (∫ x in scaledChainSet σ o h,
      eval (fun i => eval x (scaledBarycentric σ o h i))
        (bernstein (R := ℝ) d α)) =
      h ^ 3 * (Nat.factorial d : ℝ) / (Nat.factorial (α.degree + 3) : ℝ) := by
  simp only [scaledBarycentric_eval]
  rw [scaled_chain_integral σ o h hh
      (fun x => eval (fun i => eval x (ChainGeometry.barycentric σ o i))
        (bernstein (R := ℝ) d α)),
    unit_bernstein_integral σ o d α, mul_div_assoc]

end FreudenthalSVLean.ScaledChainGeometry
