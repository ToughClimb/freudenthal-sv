import FreudenthalSVLean.ElementBubbleLift
import FreudenthalSVLean.PolynomialChainTransport
import FreudenthalSVLean.PolynomialScaling

/-!
# Scale-independent element-bubble lifting in the genuine energy norm

For manuscript Lemma `bubble` and equation `bubble-bound`, a fixed
reference polynomial right inverse is transported to every translated,
coordinate-permuted, positively scaled Freudenthal tetrahedron.  This
module proves its linearity, pressure recovery, degree and face protections,
and a squared gradient bound by the actual pressure square integral.
The constant precedes the permutation, translation, and scale quantifiers.
The cubic and quartic pressure lifts from `ElementBubbleLift` discharge
the reference right-inverse hypotheses explicitly.

The global assembly of local corrections and weak Sobolev interfaces are
separate obligations; no global inf-sup assertion is made here.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.PolynomialL2Space
open FreudenthalSVLean.ElementBubbleLift

noncomputable section

namespace FreudenthalSVLean.StableElementBubbleLift

set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial Coordinate ℝ
abbrev VectorPoly := Coordinate → Poly

def rescaleVectorLinear (h a : ℝ) : VectorPoly →ₗ[ℝ] VectorPoly where
  toFun v j := rescale h a (v j)
  map_add' v w := by
    funext j
    exact (rescaleLinear h a).map_add (v j) (w j)
  map_smul' c v := by
    funext j
    exact (rescaleLinear h a).map_smul c (v j)

def scaledLift (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ)
    (J : Poly →ₗ[ℝ] VectorPoly) : Poly →ₗ[ℝ] VectorPoly :=
  (rescaleVectorLinear h h).comp ((pushVectorLinear σ o).comp
    (J.comp (PolynomialInverseEstimate.pullbackLinear σ o h)))

theorem scaledLift_apply (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ)
    (J : Poly →ₗ[ℝ] VectorPoly) (p : Poly) (j : Coordinate) :
    scaledLift σ o h J p j = rescale h h
      (pushVector σ o (J (PolynomialInverseEstimate.pullback σ o h p)) j) := rfl

def zeroScaledEdgeTrace (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ)
    (p : Poly) : Prop :=
  ∀ a b : Vertex, a ≠ b → ∀ t ∈ Icc (0 : ℝ) 1,
    eval (segmentPoint (scaledVertex σ o h a) (scaledVertex σ o h b) t) p = 0

theorem pullback_zeroEdgeTrace (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ)
    (p : Poly) (he : zeroScaledEdgeTrace σ o h p) :
    zeroEdgeTrace (Equiv.refl Coordinate) 0 (PolynomialInverseEstimate.pullback σ o h p) := by
  intro a b hab t ht
  rw [PolynomialInverseEstimate.pullback_eval]
  have hs : h • (unitNormalize σ o).symm
      (segmentPoint (chainVertex (Equiv.refl Coordinate) (0 : Space) a)
        (chainVertex (Equiv.refl Coordinate) (0 : Space) b) t) =
      segmentPoint (scaledVertex σ o h a) (scaledVertex σ o h b) t := by
    rw [normalize_symm_segment, normalize_symm_vertex, normalize_symm_vertex]
    funext j
    simp only [scaledVertex, Pi.smul_apply, smul_eq_mul, segmentPoint]
    ring
  rw [hs]
  exact he a b hab t ht

theorem pullback_zeroMean (σ : Equiv.Perm Coordinate) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : Poly)
    (hm : (∫ x in scaledChainSet σ o h, eval x p) = 0) :
    FaceBubbleMean.unitSpatialIntegral (Equiv.refl Coordinate) 0
      (PolynomialInverseEstimate.pullback σ o h p) = 0 := by
  change (∫ x in unitChainSet (Equiv.refl Coordinate) 0,
    eval x (PolynomialInverseEstimate.pullback σ o h p)) = 0
  rw [reference_set_eq]
  have hi := PolynomialInverseEstimate.pullback_integral σ o h hh p
  rw [hm] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 3 hh.ne')

/-- Transport of a fully proved reference right inverse to every physical
tetrahedron.  Edge and mean conditions concern actual polynomial values
and volume integrals. -/
theorem scaledLift_divergence (d : ℕ) (J : Poly →ₗ[ℝ] VectorPoly)
    (hJ : ∀ p : Poly, p.totalDegree ≤ d → zeroEdgeTrace (Equiv.refl Coordinate) 0 p →
      FaceBubbleMean.unitSpatialIntegral (Equiv.refl Coordinate) 0 p = 0 →
        PolynomialCalculus.polynomialDivergence (J p) = p)
    (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ) (hh : 0 < h)
    (p : Poly) (hp : p.totalDegree ≤ d) (he : zeroScaledEdgeTrace σ o h p)
    (hm : (∫ x in scaledChainSet σ o h, eval x p) = 0) :
    PolynomialCalculus.polynomialDivergence (scaledLift σ o h J p) = p := by
  have hright := hJ (PolynomialInverseEstimate.pullback σ o h p)
    ((PolynomialInverseEstimate.pullback_degree σ o h p).trans hp)
    (pullback_zeroEdgeTrace σ o h p he) (pullback_zeroMean σ o h hh p hm)
  change PolynomialCalculus.polynomialDivergence (fun j => rescale h h
    (pushVector σ o (J (PolynomialInverseEstimate.pullback σ o h p)) j)) = p
  rw [divergence_rescale, divergence_pushVector, hright, mul_inv_cancel₀ hh.ne']
  apply MvPolynomial.funext
  intro x
  rw [rescale_eval, forward_eval, PolynomialInverseEstimate.pullback_eval]
  simp only [MeasurableEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hh.ne',
    one_smul, one_mul]

theorem scaledLift_degree (k : ℕ) (J : Poly →ₗ[ℝ] VectorPoly)
    (hJ : ∀ p : Poly, ∀ j : Coordinate, (J p j).totalDegree ≤ k)
    (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ) (p : Poly) (j : Coordinate) :
    (scaledLift σ o h J p j).totalDegree ≤ k :=
  (rescale_degree_le _ _ _).trans ((forward_degree _ _ _).trans (hJ _ _))

theorem scaledLift_face_zero (J : Poly →ₗ[ℝ] VectorPoly)
    (hJ : ∀ p : Poly, ∀ x : Space, ∀ a : Vertex,
      eval x (barycentric (Equiv.refl Coordinate) (0 : Space) a) = 0 →
        ∀ j : Coordinate, eval x (J p j) = 0)
    (σ : Equiv.Perm Coordinate) (o x : Space) (h : ℝ) (p : Poly) (a : Vertex)
    (ha : eval x (scaledBarycentric σ o h a) = 0) (j : Coordinate) :
    eval x (scaledLift σ o h J p j) = 0 := by
  rw [scaledLift_apply, rescale_eval]
  simp only [pushVector, forward_eval]
  have href : eval (unitNormalize σ o (h⁻¹ • x))
      (barycentric (Equiv.refl Coordinate) (0 : Space) a) = 0 := by
    rw [← forward_eval, forward_barycentric, ← scaledBarycentric_eval]
    exact ha
  rw [hJ _ _ a href, mul_zero]

/-- A fixed reference polynomial lifting operator has one stability
constant for every positive scale, translation and coordinate permutation.
No mean or trace condition is needed for this operator-norm bound. -/
theorem scaledLift_energy_bound (d : ℕ) (J : Poly →ₗ[ℝ] VectorPoly) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : Equiv.Perm Coordinate, ∀ o : Space, ∀ h : ℝ, 0 < h →
      ∀ p : Poly, p.totalDegree ≤ d →
      (∑ j : Coordinate, ∑ i : Coordinate, ∫ x in scaledChainSet σ o h,
        (eval x (pderiv i (scaledLift σ o h J p j))) ^ 2) ≤
        C * ∫ x in scaledChainSet σ o h, (eval x p) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := vector_linear_lift_energy_bound d J
  refine ⟨C, hC, ?_⟩
  intro σ o h hh p hp
  let q : degreeSpace d := ⟨PolynomialInverseEstimate.pullback σ o h p,
    (mem_restrictTotalDegree _ _ _).mpr ((PolynomialInverseEstimate.pullback_degree σ o h p).trans hp)⟩
  calc
    _ = h ^ 3 * (∑ j : Coordinate, ∑ i : Coordinate, ∫ x in unitChainSet σ o,
        (eval x (pderiv i (pushVector σ o (J q.val) j))) ^ 2) := by
      simp only [scaledLift_apply, derivative_energy_scaling σ o h hh, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = h ^ 3 * (∑ j : Coordinate, ∑ i : Coordinate,
        referenceSquareIntegral (pderiv i (J q.val j))) := by rw [pushVector_energy]
    _ ≤ h ^ 3 * (C * referenceSquareIntegral q.val) :=
      mul_le_mul_of_nonneg_left (hb q) (pow_nonneg hh.le 3)
    _ = _ := by
      rw [PolynomialInverseEstimate.pullback_square_integral σ o h hh p]
      ring

def quarticVelocityLift (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ) :
    Poly →ₗ[ℝ] VectorPoly := scaledLift σ o h (cubicLift (Equiv.refl Coordinate) 0)

def quinticVelocityLift (σ : Equiv.Perm Coordinate) (o : Space) (h : ℝ) :
    Poly →ₗ[ℝ] VectorPoly := scaledLift σ o h (quarticLift (Equiv.refl Coordinate) 0)

theorem quarticVelocityLift_divergence (σ : Equiv.Perm Coordinate) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : Poly) (hp : p.totalDegree ≤ 3)
    (he : zeroScaledEdgeTrace σ o h p)
    (hm : (∫ x in scaledChainSet σ o h, eval x p) = 0) :
    PolynomialCalculus.polynomialDivergence (quarticVelocityLift σ o h p) = p :=
  scaledLift_divergence 3 _ (cubicLift_divergence (Equiv.refl Coordinate) 0) σ o h hh p hp he hm

theorem quinticVelocityLift_divergence (σ : Equiv.Perm Coordinate) (o : Space)
    (h : ℝ) (hh : 0 < h) (p : Poly) (hp : p.totalDegree ≤ 4)
    (he : zeroScaledEdgeTrace σ o h p)
    (hm : (∫ x in scaledChainSet σ o h, eval x p) = 0) :
    PolynomialCalculus.polynomialDivergence (quinticVelocityLift σ o h p) = p :=
  scaledLift_divergence 4 _ (quarticLift_divergence (Equiv.refl Coordinate) 0) σ o h hh p hp he hm

theorem quarticVelocityLift_degree (σ : Equiv.Perm Coordinate) (o : Space)
    (h : ℝ) (p : Poly) (j : Coordinate) :
    (quarticVelocityLift σ o h p j).totalDegree ≤ 4 :=
  scaledLift_degree 4 _ (cubicLift_degree (Equiv.refl Coordinate) 0) σ o h p j

theorem quinticVelocityLift_degree (σ : Equiv.Perm Coordinate) (o : Space)
    (h : ℝ) (p : Poly) (j : Coordinate) :
    (quinticVelocityLift σ o h p j).totalDegree ≤ 5 :=
  scaledLift_degree 5 _ (quarticLift_degree (Equiv.refl Coordinate) 0) σ o h p j

theorem quarticVelocityLift_face_zero (σ : Equiv.Perm Coordinate) (o x : Space)
    (h : ℝ) (p : Poly) (a : Vertex) (ha : eval x (scaledBarycentric σ o h a) = 0)
    (j : Coordinate) : eval x (quarticVelocityLift σ o h p j) = 0 :=
  scaledLift_face_zero _
    (fun p x a ha j => cubicLift_face_zero (Equiv.refl Coordinate) 0 x p a ha j)
    σ o x h p a ha j

theorem quinticVelocityLift_face_zero (σ : Equiv.Perm Coordinate) (o x : Space)
    (h : ℝ) (p : Poly) (a : Vertex) (ha : eval x (scaledBarycentric σ o h a) = 0)
    (j : Coordinate) : eval x (quinticVelocityLift σ o h p j) = 0 :=
  scaledLift_face_zero _
    (fun p x a ha j => quarticLift_face_zero (Equiv.refl Coordinate) 0 x p a ha j)
    σ o x h p a ha j

theorem quarticVelocityLift_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : Equiv.Perm Coordinate, ∀ o : Space, ∀ h : ℝ, 0 < h →
      ∀ p : Poly, p.totalDegree ≤ 3 →
      (∑ j : Coordinate, ∑ i : Coordinate, ∫ x in scaledChainSet σ o h,
        (eval x (pderiv i (quarticVelocityLift σ o h p j))) ^ 2) ≤
        C * ∫ x in scaledChainSet σ o h, (eval x p) ^ 2 :=
  scaledLift_energy_bound 3 (cubicLift (Equiv.refl Coordinate) 0)

theorem quinticVelocityLift_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : Equiv.Perm Coordinate, ∀ o : Space, ∀ h : ℝ, 0 < h →
      ∀ p : Poly, p.totalDegree ≤ 4 →
      (∑ j : Coordinate, ∑ i : Coordinate, ∫ x in scaledChainSet σ o h,
        (eval x (pderiv i (quinticVelocityLift σ o h p j))) ^ 2) ≤
        C * ∫ x in scaledChainSet σ o h, (eval x p) ^ 2 :=
  scaledLift_energy_bound 4 (quarticLift (Equiv.refl Coordinate) 0)

end FreudenthalSVLean.StableElementBubbleLift
