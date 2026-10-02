import FreudenthalSVLean.BarycentricMonomialMean
import FreudenthalSVLean.ConformingFaceModes
import FreudenthalSVLean.StarMeanRouting

/-!
# Actual zero-total-mean compatibility of weighted face modes

For manuscript equations `endpoint-face-bubble` and `middle-face-bubble`,
the positive nodal powers used by the quartic and quintic endpoint modes
have opposite genuine divergence means on the two face owners.  If the
weighted node is off the face, each owner mean is zero instead.  The
identity follows from the structural barycentric monomial mean theorem,
the actual shared-face gradients and polynomial two-owner support.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BarycentricMonomialMean
open FreudenthalSVLean.StarMeanRouting

noncomputable section

namespace FreudenthalSVLean.WeightedFaceMean

set_option backward.isDefEq.respectTransparency false

def weightedExponent (r l : Fin 4) (e : ℕ) : Fin 4 →₀ ℕ :=
  faceExponent r + Finsupp.single l e

theorem weightedExponent_degree (r l : Fin 4) (e : ℕ) :
    (weightedExponent r l e).degree = 3 + e := by
  rw [weightedExponent, map_add, faceExponent_degree, Finsupp.degree_single]

theorem weightedExponent_factorial (r l : Fin 4) (e : ℕ) :
    factorialProduct (R := ℝ) (weightedExponent r l e) =
      if l = r then (Nat.factorial e : ℝ) else (Nat.factorial (e + 1) : ℝ) := by
  classical
  unfold factorialProduct
  rw [Finset.prod_eq_single l]
  · by_cases hl : l = r <;> simp [weightedExponent, faceExponent_apply, Nat.add_comm, hl]
  · intro a _ ha
    simp only [weightedExponent, Finsupp.add_apply, Finsupp.single_apply,
      if_neg ha.symm, add_zero, faceExponent_apply]
    split_ifs <;> norm_num
  · simp

theorem spatialMonomial_weightedExponent (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r l : Fin 4) (e : ℕ) :
    spatialMonomial σ o (weightedExponent r l e) =
      spatialFaceBubble σ o r * barycentric σ o l ^ e := by
  simp [spatialMonomial, weightedExponent, monomial_add_single,
    spatialFaceBubble, faceBarycentricPolynomial]

def powerCoefficient (e : ℕ) : ℝ :=
  (Nat.factorial (e + 1) : ℝ) / (Nat.factorial (e + 5) : ℝ)

/-- The mean depends only on face support, not on which face vertex is
weighted.  Weighting the missing vertex gives a full-support monomial. -/
theorem spatial_face_power_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r l : Fin 4) (e : ℕ) (he : 0 < e) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialFaceBubble σ o r * barycentric σ o l ^ e)) =
      if l = r then 0 else -powerCoefficient e * barycentricGradient (R := ℝ) σ r j := by
  rw [← spatialMonomial_weightedExponent]
  by_cases hl : l = r
  · rw [if_pos hl]
    apply fullSupport_derivative_mean_zero
    intro a
    simp only [weightedExponent, Finsupp.add_apply, faceExponent_apply, Finsupp.single_apply]
    subst l
    by_cases ha : a = r
    · simp [ha, he.ne']
    · simp [ha, Ne.symm ha]
  · rw [if_neg hl, faceSupport_derivative_mean σ o _ r]
    · rw [weightedExponent_degree, weightedExponent_factorial, if_neg hl]
      congr 1
      simp [powerCoefficient, Nat.add_comm, Nat.add_left_comm]
    · simp [weightedExponent, faceExponent_apply, hl]
    · intro a ha
      simp only [weightedExponent, Finsupp.add_apply, faceExponent_apply, if_neg ha]
      omega

theorem weighted_face_vertex_mean {N : ℕ} (hN : 0 < N) (t : Tet N) (r l : Fin 4)
    (e : ℕ) (he : 0 < e) (z : Space) :
    tetIntegral hN t (divergence N
      (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t l) e 0 z) t) =
      if l = r then 0 else -(meshScale N) ^ 2 * powerCoefficient e *
        (∑ j : Fin 3, z j * barycentricGradient (R := ℝ) t.2 r j) := by
  change tetIntegral hN t (∑ j : Fin 3, pderiv j
    (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t l) e 0 z t j)) = _
  rw [map_sum]
  have hm (j : Fin 3) : tetIntegral hN t (pderiv j
      (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t l) e 0 z t j)) =
      if l = r then 0 else -(meshScale N) ^ 2 * powerCoefficient e *
        (z j * barycentricGradient (R := ℝ) t.2 r j) := by
    rw [weightedFaceField_self_rescale t r l l e 0 z j]
    simp only [pow_zero, mul_one]
    change (∫ x in ScaledChainGeometry.scaledChainSet t.2 (cellOrigin t.1) (meshScale N),
      eval x (pderiv j (rescale (meshScale N) (z j)
        (spatialFaceBubble t.2 (cellOrigin t.1) r * ChainGeometry.barycentric t.2 (cellOrigin t.1) l ^ e)))) = _
    rw [derivative_mean_scaling _ _ _ (meshScale_pos N hN)]
    change z j * (meshScale N) ^ 2 * unitSpatialIntegral t.2 (cellOrigin t.1)
      (pderiv j (spatialFaceBubble t.2 (cellOrigin t.1) r * ChainGeometry.barycentric t.2 (cellOrigin t.1) l ^ e)) = _
    rw [spatial_face_power_derivative_mean t.2 (cellOrigin t.1) r l e he j]
    by_cases hl : l = r <;> simp only [hl, if_true, if_false] <;> ring
  simp only [hm]
  by_cases hl : l = r
  · simp [hl]
  · simp only [hl, if_false, Finset.mul_sum]

theorem weighted_face_node_mean {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (m : GridVertex N) (e : ℕ) (he : 0 < e) (z : Space) :
    tetIntegral hN t (divergence N (weightedFaceField N t r m m e 0 z) t) =
      if m ∈ gridFace t r then -(meshScale N) ^ 2 * powerCoefficient e *
        (∑ j : Fin 3, z j * barycentricGradient (R := ℝ) t.2 r j) else 0 := by
  classical
  by_cases hm : m ∈ gridVertices t
  · obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hm
    have hface : m ∈ gridFace t r ↔ l ≠ r := by
      rw [← hl]
      simp only [gridFace, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, he⟩
        have he' := gridVertexOfTet_injective t he
        subst a
        exact (Finset.mem_erase.mp ha).1
      · intro h
        exact ⟨l, Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩
    simp only [hface]
    rw [← hl, weighted_face_vertex_mean hN t r l e he z]
    by_cases hr : l = r <;> simp [hr]
  · have hf : m ∉ gridFace t r := fun hf => hm (gridFace_subset_vertices t r hf)
    rw [if_neg hf]
    have hz : weightedFaceField N t r m m e 0 z t = 0 := by
      funext j
      simp [weightedFaceField, node_polynomial_zero_of_missing t m hm, he.ne']
    change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
      (weightedFaceField N t r m m e 0 z t)) = 0
    rw [hz]
    simp [PolynomialCalculus.polynomialDivergence]

theorem weightedFaceField_shared {N : ℕ} (t v : Tet N) (r u : Fin 4)
    (he : gridFace t r = gridFace v u) (m : GridVertex N) (e : ℕ) (z : Space) :
    weightedFaceField N t r m m e 0 z = weightedFaceField N v u m m e 0 z := by
  funext w j
  simp only [weightedFaceField, faceScalar, he]

/-- Actual owner means cancel, including the borrowed-face case in which
the weighted endpoint is not a face node. -/
theorem weighted_face_paired_means {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (m : GridVertex N) (e : ℕ) (he : 0 < e) (z : Space) :
    tetIntegral hN ta.val.1 (divergence N (weightedFaceField N ta.val.1 r m m e 0 z) ta.val.1) +
      tetIntegral hN tb.val.1 (divergence N (weightedFaceField N ta.val.1 r m m e 0 z) tb.val.1) = 0 := by
  rw [weighted_face_node_mean hN ta.val.1 r m e he z]
  conv_lhs => rhs; rw [weightedFaceField_shared ta.val.1 tb.val.1 r u hf m e z,
    weighted_face_node_mean hN tb.val.1 u m e he z]
  rw [hf]
  by_cases hm : m ∈ gridFace tb.val.1 u
  · simp only [hm, if_true, actual_shared_gradients_opposite ta tb r u hr hu hne hf,
      mul_neg, Finset.sum_neg_distrib]
    ring
  · simp [hm]

theorem weighted_face_total_mean_zero {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (m : GridVertex N) (e : ℕ) (he : 0 < e) (z : Space) :
    (∑ t : Tet N, tetIntegral hN t
      (divergence N (weightedFaceField N ta.val.1 r m m e 0 z) t)) = 0 := by
  classical
  let f := fun t : Tet N => tetIntegral hN t
    (divergence N (weightedFaceField N ta.val.1 r m m e 0 z) t)
  have hs : (∑ t ∈ ({ta.val.1, tb.val.1} : Finset (Tet N)), f t) = ∑ t : Tet N, f t := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hta : t ≠ ta.val.1 := by intro he; subst t; exact ht (by simp)
    have htb : t ≠ tb.val.1 := by intro he; subst t; exact ht (by simp)
    have hz : weightedFaceField N ta.val.1 r m m e 0 z t = 0 := by
      funext j
      exact weightedFaceField_zero_off_pair ta tb r u hr hne hf m m e 0 z t hta htb j
    change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
      (weightedFaceField N ta.val.1 r m m e 0 z t)) = 0
    rw [hz]
    simp [PolynomialCalculus.polynomialDivergence]
  change (∑ t : Tet N, f t) = 0
  rw [← hs, Finset.sum_pair hne]
  exact weighted_face_paired_means hN ta tb r u hr hu hne hf m e he z

end FreudenthalSVLean.WeightedFaceMean
