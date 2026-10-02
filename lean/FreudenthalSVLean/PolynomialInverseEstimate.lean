import FreudenthalSVLean.PolynomialL2Space
import FreudenthalSVLean.PolynomialDegree
import FreudenthalSVLean.FreudenthalMesh

/-!
# Mesh-independent vertex inverse estimates

The manuscript's proof of Proposition `vertex` uses
`h³ |r|_T(a)|² ≤ C(k) ∫_T r²`.  This module proves that estimate on
every positively scaled, translated, and coordinate-permuted Freudenthal
tetrahedron.  The constant is quantified before all geometry and scale
parameters.  It follows from the genuine reference volume norm and an
affine polynomial pullback, not from enumeration of meshes.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.PolynomialL2Space

noncomputable section

namespace FreudenthalSVLean.PolynomialInverseEstimate

def pullback (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  eval₂Hom C (fun j => C h * (X (σ.symm j) + C (o j))) p

def pullbackLinear (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun := pullback σ o h
  map_add' p q := by simp only [pullback, map_add]
  map_smul' c p := by
    simp only [pullback, smul_eq_C_mul, map_mul, eval₂Hom_C, RingHom.id_apply]

theorem pullback_eval (σ : Equiv.Perm (Fin 3)) (o y : Space) (h : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    eval y (pullback σ o h p) = eval (h • (unitNormalize σ o).symm y) p := by
  rw [pullback, PolynomialCalculus.eval_substitution]
  apply congrArg (fun z : Space => eval z p)
  funext j
  simp [unitNormalize_symm_apply, Pi.smul_apply, smul_eq_mul]

theorem pullback_degree (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (pullback σ o h p).totalDegree ≤ p.totalDegree := by
  apply PolynomialDegree.affine_substitution_degree
  intro j
  calc
    (C h * (X (σ.symm j) + C (o j))).totalDegree ≤
        (C h).totalDegree + (X (σ.symm j) + C (o j)).totalDegree :=
      totalDegree_mul _ _
    _ ≤ 1 := by
      simpa using totalDegree_add (X (σ.symm j) : MvPolynomial (Fin 3) ℝ) (C (o j))

theorem unit_integral_normalize (σ : Equiv.Perm (Fin 3)) (o : Space) (f : Space → ℝ) :
    (∫ x in unitChainSet σ o, f x) =
      ∫ y in coordinateChainSet, f ((unitNormalize σ o).symm y) := by
  calc
    _ = ∫ x in unitChainSet σ o, f ((unitNormalize σ o).symm (unitNormalize σ o x)) := by
      simp
    _ = _ := (unitNormalize_preserving σ o).setIntegral_preimage_emb
      (unitNormalize σ o).measurableEmbedding
      (fun y => f ((unitNormalize σ o).symm y)) coordinateChainSet

/-- Actual pressure-integral transport, also used for the element-bubble
zero-mean compatibility in manuscript Lemma `bubble`. -/
theorem pullback_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : MvPolynomial (Fin 3) ℝ) :
    (∫ x in scaledChainSet σ o h, eval x p) =
      h ^ 3 * ∫ y in coordinateChainSet, eval y (pullback σ o h p) := by
  have he : (fun x : Space => eval x p) =
      (fun x => eval (h • (h⁻¹ • x)) p) := by
    funext x
    simp [smul_smul, hh.ne']
  rw [he, scaled_chain_integral σ o h hh
    (fun y => eval (h • y) p), unit_integral_normalize]
  simp only [pullback_eval]

/-- Actual square-volume transport, valid for every spatial polynomial. -/
theorem pullback_square_integral (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : MvPolynomial (Fin 3) ℝ) :
    (∫ x in scaledChainSet σ o h, (eval x p) ^ 2) =
      h ^ 3 * referenceSquareIntegral (pullback σ o h p) := by
  have he : (fun x : Space => (eval x p) ^ 2) =
      (fun x => (eval (h • (h⁻¹ • x)) p) ^ 2) := by
    funext x
    simp [smul_smul, hh.ne']
  rw [he, scaled_chain_integral σ o h hh
    (fun y => (eval (h • y) p) ^ 2), unit_integral_normalize]
  simp only [referenceSquareIntegral, pullback_eval]

theorem pullback_vertex_eval (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (a : Fin 4) :
    eval (ChainGeometry.chainVertex (Equiv.refl (Fin 3)) (0 : Space) a)
      (pullback σ o h p) = eval (scaledVertex σ o h a) p := by
  rw [pullback_eval]
  congr 1
  congr 1
  funext j
  simp [unitNormalize_symm_apply, scaledVertex, ChainGeometry.chainVertex, add_comm]
  left
  rfl

/-- One reference constant works for all four vertices. -/
theorem reference_vertex_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 4, ∀ p : degreeSpace d,
      (eval (ChainGeometry.chainVertex (Equiv.refl (Fin 3)) (0 : Space) a) p.val) ^ 2 ≤
        C * referenceSquareIntegral p.val := by
  choose C hC hb using fun a : Fin 4 => point_evaluation_squared_bound d
    (ChainGeometry.chainVertex (Equiv.refl (Fin 3)) (0 : Space) a)
  refine ⟨∑ a : Fin 4, C a, ?_, ?_⟩
  · exact Finset.sum_pos (fun a _ => hC a) Finset.univ_nonempty
  · intro a p
    apply (hb a p).trans
    apply mul_le_mul_of_nonneg_right _ (referenceSquareIntegral_nonneg p.val)
    exact Finset.single_le_sum (fun b _ => (hC b).le) (Finset.mem_univ a)

/-- The exact scaling and quantifiers required by the vertex-lift estimate.
In particular the constant does not depend on `h`, `o`, or `σ`. -/
theorem scaled_vertex_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Equiv.Perm (Fin 3)) (o : Space)
      (h : ℝ), 0 < h → ∀ (p : MvPolynomial (Fin 3) ℝ), p.totalDegree ≤ d →
      ∀ a : Fin 4, h ^ 3 * (eval (scaledVertex σ o h a) p) ^ 2 ≤
        C * ∫ x in scaledChainSet σ o h, (eval x p) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := reference_vertex_bound d
  refine ⟨C, hC, ?_⟩
  intro σ o h hh p hp a
  let q : degreeSpace d := ⟨pullback σ o h p,
    (mem_restrictTotalDegree _ _ _).mpr ((pullback_degree σ o h p).trans hp)⟩
  have hq := hb a q
  have hs := mul_le_mul_of_nonneg_left hq (pow_nonneg hh.le 3)
  simpa only [q, pullback_vertex_eval, pullback_square_integral σ o h hh p,
    mul_left_comm] using hs

end FreudenthalSVLean.PolynomialInverseEstimate
