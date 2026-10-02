import FreudenthalSVLean.PolynomialInverseEstimate
import FreudenthalSVLean.VertexJetAlgebra
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial lifting transport under chain permutations and translations

The reference-element step in manuscript Lemma `bubble` and the local
lifting estimates transports a fixed reference right inverse to every
translated coordinate-chain tetrahedron.  This module proves the actual
polynomial inverse substitutions, derivative and divergence transport, and
integral identities.  Coordinate permutations are orthogonal and preserve
the sum of all squared gradient components, so this transport requires no
enumeration of the six tetrahedron orientations.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.PolynomialL2

noncomputable section

namespace FreudenthalSVLean.PolynomialChainTransport

set_option backward.isDefEq.respectTransparency false

def forward (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : MvPolynomial Coordinate ℝ :=
  eval₂Hom C (chainCoordinate σ o) p

def backward (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : MvPolynomial Coordinate ℝ :=
  PolynomialInverseEstimate.pullback σ o 1 p

def forwardLinear (σ : Equiv.Perm Coordinate) (o : Space) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] MvPolynomial Coordinate ℝ where
  toFun := forward σ o
  map_add' p q := by simp only [forward, map_add]
  map_smul' c p := by
    simp only [forward, smul_eq_C_mul, map_mul, eval₂Hom_C, RingHom.id_apply]

def backwardLinear (σ : Equiv.Perm Coordinate) (o : Space) :
    MvPolynomial Coordinate ℝ →ₗ[ℝ] MvPolynomial Coordinate ℝ where
  toFun := backward σ o
  map_add' p q := by simp only [backward, PolynomialInverseEstimate.pullback, map_add]
  map_smul' c p := by
    simp only [backward, PolynomialInverseEstimate.pullback, smul_eq_C_mul,
      map_mul, eval₂Hom_C, RingHom.id_apply]

theorem reference_set_eq :
    unitChainSet (Equiv.refl Coordinate) (0 : Space) = coordinateChainSet := by
  have he : unitNormalize (Equiv.refl Coordinate) (0 : Space) =
      MeasurableEquiv.refl Space := by
    ext x j
    simp [unitNormalize_apply]
  rw [unitChainSet, he]
  rfl

theorem normalize_symm_vertex (σ : Equiv.Perm Coordinate) (o : Space) (a : Vertex) :
    (unitNormalize σ o).symm (chainVertex (Equiv.refl Coordinate) (0 : Space) a) =
      chainVertex σ o a := by
  funext j
  simp only [unitNormalize_symm_apply, chainVertex, Pi.zero_apply,
    Equiv.refl_symm, Equiv.refl_apply, zero_add]
  ring

theorem normalize_symm_segment (σ : Equiv.Perm Coordinate) (o x y : Space) (t : ℝ) :
    (unitNormalize σ o).symm (segmentPoint x y t) =
      segmentPoint ((unitNormalize σ o).symm x) ((unitNormalize σ o).symm y) t := by
  funext j
  simp only [unitNormalize_symm_apply, segmentPoint]
  ring

theorem forward_barycentric (σ : Equiv.Perm Coordinate) (o : Space) (a : Vertex) :
    forward σ o (barycentric (Equiv.refl Coordinate) (0 : Space) a) =
      barycentric σ o a := by
  fin_cases a <;>
    simp [forward, barycentric, chainCoordinate, map_sub]

theorem forward_eval (σ : Equiv.Perm Coordinate) (o x : Space)
    (p : MvPolynomial Coordinate ℝ) :
    eval x (forward σ o p) = eval (unitNormalize σ o x) p := by
  rw [forward, PolynomialCalculus.eval_substitution]
  apply congrArg (fun y : Space => eval y p)
  funext j
  simp [chainCoordinate, unitNormalize_apply]

theorem backward_eval (σ : Equiv.Perm Coordinate) (o x : Space)
    (p : MvPolynomial Coordinate ℝ) :
    eval x (backward σ o p) = eval ((unitNormalize σ o).symm x) p := by
  simpa only [backward, one_smul] using
    PolynomialInverseEstimate.pullback_eval σ o x 1 p

theorem forward_backward (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : forward σ o (backward σ o p) = p := by
  apply MvPolynomial.funext
  intro x
  rw [forward_eval, backward_eval, MeasurableEquiv.symm_apply_apply]

theorem backward_forward (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : backward σ o (forward σ o p) = p := by
  apply MvPolynomial.funext
  intro x
  rw [backward_eval, forward_eval, MeasurableEquiv.apply_symm_apply]

theorem forward_degree (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : (forward σ o p).totalDegree ≤ p.totalDegree := by
  apply PolynomialDegree.affine_substitution_degree
  intro j
  exact (PolynomialDegree.sub_degree_le _ _).trans (by simp)

theorem backward_degree (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) : (backward σ o p).totalDegree ≤ p.totalDegree :=
  PolynomialInverseEstimate.pullback_degree σ o 1 p

theorem pderiv_chainCoordinate (σ : Equiv.Perm Coordinate) (o : Space)
    (r j : Coordinate) :
    pderiv j (chainCoordinate σ o r) = if σ r = j then 1 else 0 := by
  simp [chainCoordinate, pderiv_X, Pi.single_apply]

theorem pderiv_forward (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) (j : Coordinate) :
    pderiv j (forward σ o p) = forward σ o (pderiv (σ.symm j) p) := by
  rw [forward, PolynomialCalculus.pderiv_substitution]
  simp only [pderiv_chainCoordinate, mul_ite, mul_one, mul_zero,
    ← σ.eq_symm_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

def pushVector (σ : Equiv.Perm Coordinate) (o : Space)
    (v : Coordinate → MvPolynomial Coordinate ℝ) :
    Coordinate → MvPolynomial Coordinate ℝ :=
  fun j => forward σ o (v (σ.symm j))

def pushVectorLinear (σ : Equiv.Perm Coordinate) (o : Space) :
    (Coordinate → MvPolynomial Coordinate ℝ) →ₗ[ℝ]
      (Coordinate → MvPolynomial Coordinate ℝ) where
  toFun := pushVector σ o
  map_add' v w := by
    funext j
    simp only [pushVector, Pi.add_apply, forward, map_add]
  map_smul' c v := by
    funext j
    simp only [pushVector, Pi.smul_apply]
    exact (forwardLinear σ o).map_smul c (v (σ.symm j))

theorem divergence_pushVector (σ : Equiv.Perm Coordinate) (o : Space)
    (v : Coordinate → MvPolynomial Coordinate ℝ) :
    PolynomialCalculus.polynomialDivergence (pushVector σ o v) =
      forward σ o (PolynomialCalculus.polynomialDivergence v) := by
  simp only [PolynomialCalculus.polynomialDivergence, pushVector, pderiv_forward]
  calc
    (∑ j : Coordinate, forward σ o (pderiv (σ.symm j) (v (σ.symm j)))) =
        forward σ o (∑ j : Coordinate, pderiv (σ.symm j) (v (σ.symm j))) := by
      simp only [forward, map_sum]
    _ = _ := congrArg (forward σ o)
      (Equiv.sum_comp σ.symm (fun j : Coordinate => pderiv j (v j)))

theorem forward_integral (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) :
    (∫ x in unitChainSet σ o, eval x (forward σ o p)) =
      ∫ x in coordinateChainSet, eval x p := by
  rw [PolynomialInverseEstimate.unit_integral_normalize]
  simp only [forward_eval, MeasurableEquiv.apply_symm_apply]

theorem backward_integral (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) :
    (∫ x in coordinateChainSet, eval x (backward σ o p)) =
      ∫ x in unitChainSet σ o, eval x p := by
  rw [PolynomialInverseEstimate.unit_integral_normalize]
  simp only [backward_eval]

theorem forward_square_integral (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) :
    (∫ x in unitChainSet σ o, (eval x (forward σ o p)) ^ 2) =
      referenceSquareIntegral p := by
  rw [PolynomialInverseEstimate.unit_integral_normalize]
  simp only [forward_eval, MeasurableEquiv.apply_symm_apply, referenceSquareIntegral]

theorem backward_square_integral (σ : Equiv.Perm Coordinate) (o : Space)
    (p : MvPolynomial Coordinate ℝ) :
    referenceSquareIntegral (backward σ o p) =
      ∫ x in unitChainSet σ o, (eval x p) ^ 2 := by
  rw [PolynomialInverseEstimate.unit_integral_normalize]
  simp only [backward_eval, referenceSquareIntegral]

/-- The actual vector gradient energy is unchanged by a chain permutation
and translation; the constant is therefore independent of both. -/
theorem pushVector_energy (σ : Equiv.Perm Coordinate) (o : Space)
    (v : Coordinate → MvPolynomial Coordinate ℝ) :
    (∑ j : Coordinate, ∑ i : Coordinate,
      ∫ x in unitChainSet σ o, (eval x (pderiv i (pushVector σ o v j))) ^ 2) =
      ∑ j : Coordinate, ∑ i : Coordinate, referenceSquareIntegral (pderiv i (v j)) := by
  simp only [pushVector, pderiv_forward, forward_square_integral]
  have hi (j : Coordinate) :
      (∑ i : Coordinate, referenceSquareIntegral (pderiv (σ.symm i) (v j))) =
        ∑ i : Coordinate, referenceSquareIntegral (pderiv i (v j)) :=
    Equiv.sum_comp σ.symm (fun i : Coordinate => referenceSquareIntegral (pderiv i (v j)))
  simp only [hi]
  exact Equiv.sum_comp σ.symm
    (fun j : Coordinate => ∑ i : Coordinate, referenceSquareIntegral (pderiv i (v j)))

end FreudenthalSVLean.PolynomialChainTransport
