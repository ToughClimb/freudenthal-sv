import FreudenthalSVLean.WeightedFaceMean

/-!
# Actual zero-total-mean compatibility of quintic middle modes

For manuscript equation `middle-face-bubble`, a cubic face product times
two nodal factors has paired opposite genuine means.  The two endpoints
can coincide or differ, lie on the common face, be omitted owner vertices,
or be absent from an owner.  All cases follow from barycentric support and
the symmetric factorial product; no mesh-specific integral rule is assumed.
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
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.BarycentricMonomialMean
open FreudenthalSVLean.WeightedFaceMean
open FreudenthalSVLean.StarMeanRouting

noncomputable section

namespace FreudenthalSVLean.BilinearFaceMean

set_option backward.isDefEq.respectTransparency false

def twoExponent (r l m : Fin 4) : Fin 4 →₀ ℕ :=
  weightedExponent r l 1 + Finsupp.single m 1

def coefficient {ι : Type*} [DecidableEq ι] (l m : ι) : ℝ :=
  if l = m then 1 / 840 else 1 / 1260

theorem twoExponent_degree (r l m : Fin 4) : (twoExponent r l m).degree = 5 := by
  rw [twoExponent, map_add, weightedExponent_degree, Finsupp.degree_single]

theorem twoExponent_factorial (r l m : Fin 4) (hl : l ≠ r) (hm : m ≠ r) :
    factorialProduct (R := ℝ) (twoExponent r l m) = if l = m then 6 else 4 := by
  rw [twoExponent, factorialProduct_raised, weightedExponent_factorial, if_neg hl]
  simp only [weightedExponent, Finsupp.add_apply, faceExponent_apply, if_neg hm]
  by_cases he : l = m
  · subst m
    norm_num
  · norm_num [Finsupp.single_apply, he, Ne.symm he]

theorem spatialMonomial_twoExponent (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r l m : Fin 4) : spatialMonomial σ o (twoExponent r l m) =
      spatialFaceBubble σ o r * ChainGeometry.barycentric σ o l *
        ChainGeometry.barycentric σ o m := by
  simp [spatialMonomial, twoExponent, weightedExponent, monomial_add_single,
    spatialFaceBubble, faceBarycentricPolynomial]

theorem spatial_bilinear_derivative_mean (σ : Equiv.Perm (Fin 3)) (o : Space)
    (r l m : Fin 4) (j : Fin 3) :
    unitSpatialIntegral σ o (pderiv j (spatialFaceBubble σ o r *
      ChainGeometry.barycentric σ o l * ChainGeometry.barycentric σ o m)) =
      if l = r ∨ m = r then 0 else -coefficient l m * barycentricGradient (R := ℝ) σ r j := by
  rw [← spatialMonomial_twoExponent]
  by_cases hf : l = r ∨ m = r
  · rw [if_pos hf]
    apply fullSupport_derivative_mean_zero
    intro a
    simp only [twoExponent, weightedExponent, Finsupp.add_apply, faceExponent_apply,
      Finsupp.single_apply]
    rcases hf with hf | hf <;> subst_vars <;> split_ifs <;> omega
  · rw [if_neg hf]
    have hl : l ≠ r := fun h => hf (Or.inl h)
    have hm : m ≠ r := fun h => hf (Or.inr h)
    rw [faceSupport_derivative_mean σ o _ r]
    · rw [twoExponent_degree, twoExponent_factorial r l m hl hm]
      by_cases he : l = m <;> norm_num [coefficient, he]
    · simp [twoExponent, weightedExponent, faceExponent_apply, hl, hm]
    · intro a ha
      simp only [twoExponent, weightedExponent, Finsupp.add_apply, faceExponent_apply,
        if_neg ha]
      omega

theorem weighted_face_two_vertices_mean {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r l m : Fin 4) (z : Space) :
    tetIntegral hN t (divergence N
      (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t m) 1 1 z) t) =
      if l = r ∨ m = r then 0 else -(meshScale N) ^ 2 * coefficient l m *
        (∑ j : Fin 3, z j * barycentricGradient (R := ℝ) t.2 r j) := by
  change tetIntegral hN t (∑ j : Fin 3, pderiv j
    (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t m) 1 1 z t j)) = _
  rw [map_sum]
  have hm (j : Fin 3) : tetIntegral hN t (pderiv j
      (weightedFaceField N t r (gridVertexOfTet t l) (gridVertexOfTet t m) 1 1 z t j)) =
      if l = r ∨ m = r then 0 else -(meshScale N) ^ 2 * coefficient l m *
        (z j * barycentricGradient (R := ℝ) t.2 r j) := by
    rw [weightedFaceField_self_rescale t r l m 1 1 z j]
    simp only [pow_one]
    change (∫ x in ScaledChainGeometry.scaledChainSet t.2 (cellOrigin t.1) (meshScale N),
      eval x (pderiv j (rescale (meshScale N) (z j)
        (spatialFaceBubble t.2 (cellOrigin t.1) r * ChainGeometry.barycentric t.2 (cellOrigin t.1) l *
          ChainGeometry.barycentric t.2 (cellOrigin t.1) m)))) = _
    rw [derivative_mean_scaling _ _ _ (meshScale_pos N hN)]
    change z j * (meshScale N) ^ 2 * unitSpatialIntegral t.2 (cellOrigin t.1)
      (pderiv j (spatialFaceBubble t.2 (cellOrigin t.1) r * ChainGeometry.barycentric t.2 (cellOrigin t.1) l *
        ChainGeometry.barycentric t.2 (cellOrigin t.1) m)) = _
    rw [spatial_bilinear_derivative_mean t.2 (cellOrigin t.1) r l m j]
    by_cases hf : l = r ∨ m = r <;> simp only [hf, if_true, if_false] <;> ring
  simp only [hm]
  by_cases hf : l = r ∨ m = r
  · simp [hf]
  · simp only [hf, if_false, Finset.mul_sum]

theorem face_node_index_iff {N : ℕ} (t : Tet N) (r l : Fin 4) :
    gridVertexOfTet t l ∈ gridFace t r ↔ l ≠ r := by
  classical
  simp only [gridFace, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' := gridVertexOfTet_injective t he
    subst a
    exact (Finset.mem_erase.mp ha).1
  · intro h
    exact ⟨l, Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩, rfl⟩

theorem weighted_face_two_nodes_mean {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (a b : GridVertex N) (z : Space) :
    tetIntegral hN t (divergence N (weightedFaceField N t r a b 1 1 z) t) =
      if a ∈ gridFace t r ∧ b ∈ gridFace t r then -(meshScale N) ^ 2 * coefficient a b *
        (∑ j : Fin 3, z j * barycentricGradient (R := ℝ) t.2 r j) else 0 := by
  classical
  by_cases ha : a ∈ gridVertices t
  · by_cases hb : b ∈ gridVertices t
    · obtain ⟨l, _, hl⟩ := Finset.mem_image.mp ha
      obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hb
      rw [← hl, ← hm, weighted_face_two_vertices_mean]
      simp only [face_node_index_iff, coefficient, (gridVertexOfTet_injective t).eq_iff]
      by_cases h1 : l = r <;> by_cases h2 : m = r <;> simp [h1, h2]
    · have hf : ¬ (a ∈ gridFace t r ∧ b ∈ gridFace t r) :=
        fun hf => hb (gridFace_subset_vertices t r hf.2)
      rw [if_neg hf]
      have hz : weightedFaceField N t r a b 1 1 z t = 0 := by
        funext j
        simp [weightedFaceField, node_polynomial_zero_of_missing t b hb]
      change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
        (weightedFaceField N t r a b 1 1 z t)) = 0
      rw [hz]
      simp [PolynomialCalculus.polynomialDivergence]
  · have hf : ¬ (a ∈ gridFace t r ∧ b ∈ gridFace t r) :=
      fun hf => ha (gridFace_subset_vertices t r hf.1)
    rw [if_neg hf]
    have hz : weightedFaceField N t r a b 1 1 z t = 0 := by
      funext j
      simp [weightedFaceField, node_polynomial_zero_of_missing t a ha]
    change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
      (weightedFaceField N t r a b 1 1 z t)) = 0
    rw [hz]
    simp [PolynomialCalculus.polynomialDivergence]

theorem weightedTwoFaceField_shared {N : ℕ} (t v : Tet N) (r u : Fin 4)
    (he : gridFace t r = gridFace v u) (a b : GridVertex N) (z : Space) :
    weightedFaceField N t r a b 1 1 z = weightedFaceField N v u a b 1 1 z := by
  funext w j
  simp only [weightedFaceField, faceScalar, he]

theorem weighted_two_face_paired_means {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (a b : GridVertex N) (z : Space) :
    tetIntegral hN ta.val.1 (divergence N (weightedFaceField N ta.val.1 r a b 1 1 z) ta.val.1) +
      tetIntegral hN tb.val.1 (divergence N (weightedFaceField N ta.val.1 r a b 1 1 z) tb.val.1) = 0 := by
  rw [weighted_face_two_nodes_mean hN ta.val.1 r a b z]
  conv_lhs => rhs; rw [weightedTwoFaceField_shared ta.val.1 tb.val.1 r u hf a b z,
    weighted_face_two_nodes_mean hN tb.val.1 u a b z]
  rw [hf]
  by_cases hm : a ∈ gridFace tb.val.1 u ∧ b ∈ gridFace tb.val.1 u
  · simp only [hm, and_self, if_true, actual_shared_gradients_opposite ta tb r u hr hu hne hf,
      mul_neg, Finset.sum_neg_distrib]
    ring
  · simp [hm]

theorem weighted_two_face_total_mean_zero {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r u : Fin 4) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (hf : gridFace ta.val.1 r = gridFace tb.val.1 u)
    (a b : GridVertex N) (z : Space) :
    (∑ t : Tet N, tetIntegral hN t
      (divergence N (weightedFaceField N ta.val.1 r a b 1 1 z) t)) = 0 := by
  classical
  let f := fun t : Tet N => tetIntegral hN t
    (divergence N (weightedFaceField N ta.val.1 r a b 1 1 z) t)
  have hs : (∑ t ∈ ({ta.val.1, tb.val.1} : Finset (Tet N)), f t) = ∑ t : Tet N, f t := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hta : t ≠ ta.val.1 := by intro he; subst t; exact ht (by simp)
    have htb : t ≠ tb.val.1 := by intro he; subst t; exact ht (by simp)
    have hz : weightedFaceField N ta.val.1 r a b 1 1 z t = 0 := by
      funext j
      exact weightedFaceField_zero_off_pair ta tb r u hr hne hf a b 1 1 z t hta htb j
    change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
      (weightedFaceField N ta.val.1 r a b 1 1 z t)) = 0
    rw [hz]
    simp [PolynomialCalculus.polynomialDivergence]
  change (∑ t : Tet N, f t) = 0
  rw [← hs, Finset.sum_pair hne]
  exact weighted_two_face_paired_means hN ta tb r u hr hu hne hf a b z

end FreudenthalSVLean.BilinearFaceMean
