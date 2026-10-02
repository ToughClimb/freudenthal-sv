import FreudenthalSVLean.ElementBubbleInjectivity
import FreudenthalSVLean.StableElementBubbleLift

/-!
# The actual low-degree element-bubble spaces and isomorphism

This module supplies the source and target interfaces of manuscript Lemma
`bubble`.  The source is the vector spatial polynomial space of degree
at most zero or one.  The target consists of degree-at-most-three or four
spatial polynomials with actual zero geometric edge traces and actual zero
volume integral.  Inclusion in the target is proved by differentiation and
the genuine monomial integrals.  Explicit local lifts give surjectivity;
the barycentric face argument gives injectivity.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ElementBubbleAlgebra
open FreudenthalSVLean.ElementBubbleLift
open FreudenthalSVLean.ElementBubbleInjectivity
open FreudenthalSVLean.LowDegreeBubbleExpansion
open FreudenthalSVLean.LowDegreeBubbleIndices
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.ChainMeasureTransport

noncomputable section

namespace FreudenthalSVLean.ElementBubbleRange

set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial Coordinate ℝ
abbrev VectorPoly := Coordinate → Poly

def sourceCubic (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly) : VectorPoly :=
  fun j => C (constantLiftVector σ o (cubicCoefficients σ o q) j)

def sourceQuartic (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly) : VectorPoly :=
  fun j => ∑ a : Vertex, C (affineLiftCoefficient σ o (quarticCoefficients σ o q) a j) *
    barycentric σ o a

theorem sourceCubic_degree (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly)
    (j : Coordinate) : (sourceCubic σ o q j).totalDegree ≤ 0 := by
  simp [sourceCubic]

theorem sourceQuartic_degree (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly)
    (j : Coordinate) : (sourceQuartic σ o q j).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro a _
  exact (totalDegree_mul _ _).trans
    (by simpa only [totalDegree_C, zero_add] using GridNodalSupport.barycentric_degree_le σ o a)

theorem sourceCubic_field (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly) :
    (fun j => bubble σ o * sourceCubic σ o q j) = cubicLift σ o q := by
  rw [cubicLift_eq]
  funext j
  exact mul_comm _ _

theorem sourceQuartic_field (σ : Equiv.Perm Coordinate) (o : Space) (q : Poly) :
    (fun j => bubble σ o * sourceQuartic σ o q j) = quarticLift σ o q := by
  funext j
  simp only [sourceQuartic, Finset.mul_sum]
  change (∑ a : Vertex, bubble σ o *
    (C (affineLiftCoefficient σ o (quarticCoefficients σ o q) a j) * barycentric σ o a)) =
    ∑ a : Vertex, C (affineLiftCoefficient σ o (quarticCoefficients σ o q) a j) *
      bubble σ o * barycentric σ o a
  apply Finset.sum_congr rfl
  intro a _
  ring

def divergenceLinear : VectorPoly →ₗ[ℝ] Poly where
  toFun := PolynomialCalculus.polynomialDivergence
  map_add' v w := by
    simp only [PolynomialCalculus.polynomialDivergence, Pi.add_apply, map_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PolynomialCalculus.polynomialDivergence, Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (pderiv j).map_smul c (v j)

def multiplyBubbleLinear (σ : Equiv.Perm Coordinate) (o : Space) :
    VectorPoly →ₗ[ℝ] VectorPoly where
  toFun p j := bubble σ o * p j
  map_add' p q := by funext j; simp only [Pi.add_apply, mul_add]
  map_smul' c p := by
    funext j
    simp only [Pi.smul_apply, smul_eq_C_mul, RingHom.id_apply]
    ring

def elementD (σ : Equiv.Perm Coordinate) (o : Space) : VectorPoly →ₗ[ℝ] Poly :=
  divergenceLinear.comp (multiplyBubbleLinear σ o)

theorem elementD_degree (σ : Equiv.Perm Coordinate) (o : Space) (s : ℕ)
    (p : VectorPoly) (hp : ∀ j : Coordinate, (p j).totalDegree ≤ s) :
    (elementD σ o p).totalDegree ≤ s + 3 := by
  apply totalDegree_finsetSum_le
  intro j _
  apply (PolynomialDegree.pderiv_degree_le j (bubble σ o * p j)).trans
  have hproduct := (totalDegree_mul (bubble σ o) (p j)).trans
    (Nat.add_le_add (bubble_degree σ o) (hp j))
  omega

theorem elementD_zeroEdgeTrace (σ : Equiv.Perm Coordinate) (o : Space) (p : VectorPoly) :
    zeroEdgeTrace σ o (elementD σ o p) := by
  intro a b _ t _
  let x := segmentPoint (chainVertex σ o a) (chainVertex σ o b) t
  obtain ⟨c, d, hcd, hca, hda, hcb, hdb⟩ := face_missing_pair a b
  have hc : eval x (barycentric σ o c) = 0 := by
    rw [barycentric_edge]
    simp [hca, hcb]
  have hd : eval x (barycentric σ o d) = 0 := by
    rw [barycentric_edge]
    simp [hda, hdb]
  have hb : eval x (bubble σ o) = 0 := bubble_eval_zero σ o x c hc
  have hg (j : Coordinate) : eval x (pderiv j (bubble σ o)) = 0 := by
    rw [bubble_derivative, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul]
    by_cases hci : c = i
    · subst i
      rw [faceCubic_eval_zero σ o x d c (Ne.symm hcd) hd, mul_zero]
    · rw [faceCubic_eval_zero σ o x c i hci hc, mul_zero]
  change eval x (∑ j : Coordinate, pderiv j (bubble σ o * p j)) = 0
  simp only [map_sum, pderiv_mul, map_add, map_mul, hg, hb, zero_mul,
    Finset.sum_const_zero, zero_add]

theorem bubble_mean (σ : Equiv.Perm Coordinate) (o : Space) :
    unitSpatialIntegral σ o (bubble σ o) = 1 / 5040 := by
  have hh := substitution_integral σ o (monomial bubbleExponent 1)
  rw [substitute_bubble_monomial, C_1, one_mul, bubble_monomial_mean] at hh
  exact hh

theorem faceCubic_barycentric_mean (σ : Equiv.Perm Coordinate) (o : Space)
    (i a : Vertex) :
    unitSpatialIntegral σ o (faceCubic σ o i * barycentric σ o a) =
      if i = a then 1 / 5040 else 2 / 5040 := by
  by_cases hia : i = a
  · subst a
    simp [faceCubic_mul_barycentric, bubble_mean]
  · let p : FacePair := ⟨(i, a), hia⟩
    have hh := substitution_integral σ o (monomial (quarticFaceExponent p) 1)
    rw [quarticFace_monomial_mean] at hh
    rw [quarticFaceExponent, substitute_quartic_face_monomial, C_1, one_mul] at hh
    rw [if_neg hia]
    simpa using hh

theorem weighted_mean_row_zero (i : Vertex) (r : Vertex → ℝ)
    (hr : ∑ a : Vertex, r a = 0) :
    (∑ a : Vertex, r a * (if a = i then 1 / 5040 else 2 / 5040)) +
      r i * (1 / 5040) = 0 := by
  have he :
      (∑ a : Vertex, r a * (if a = i then 1 / 5040 else 2 / 5040)) +
        (∑ a : Vertex, if a = i then r i * (1 / 5040) else 0) =
        ∑ a : Vertex, (2 / 5040) * r a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hai : a = i
    · subst a
      simp only [if_true]
      ring
    · simp only [hai, if_false, add_zero]
      ring
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum, hr, mul_zero] using he

theorem affine_elementD_zeroMean (σ : Equiv.Perm Coordinate) (o : Space)
    (p : VectorPoly) (hp : ∀ j : Coordinate, (p j).totalDegree ≤ 1) :
    unitSpatialIntegral σ o (elementD σ o p) = 0 := by
  let v : Vertex → Coordinate → ℝ := fun a j => eval (chainVertex σ o a) (p j)
  have hinterp (j : Coordinate) : p j = ∑ a : Vertex, C (v a j) * barycentric σ o a :=
    AffineBarycentric.affine_interpolation σ o (p j) (hp j)
  have hfield : (fun j => bubble σ o * p j) = bubbleAffineField σ o v := by
    funext j
    rw [hinterp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change unitSpatialIntegral σ o (divergence (fun j => bubble σ o * p j)) = 0
  rw [hfield, bubbleAffineField_divergence, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  simp only [map_add, map_sum, mul_assoc, unitSpatialIntegral_C_mul,
    faceCubic_barycentric_mean, bubble_mean]
  exact weighted_mean_row_zero a (fun i => normalCoefficient σ v i a)
    (normalCoefficient_sum σ v a)

def sourceSpace (s : ℕ) : Submodule ℝ VectorPoly where
  carrier := {p | ∀ j : Coordinate, (p j).totalDegree ≤ s}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro p q hp hq j
    exact (totalDegree_add _ _).trans (max_le (hp j) (hq j))
  smul_mem' := by
    intro c p hp j
    exact (totalDegree_smul_le _ _).trans (hp j)

def targetSpace (σ : Equiv.Perm Coordinate) (o : Space) (s : ℕ) : Submodule ℝ Poly where
  carrier := {q | q.totalDegree ≤ s + 3 ∧ zeroEdgeTrace σ o q ∧ unitSpatialIntegral σ o q = 0}
  zero_mem' := by
    refine ⟨by simp, ?_, by simp⟩
    intro a b _ t _
    simp
  add_mem' := by
    rintro p q ⟨hp, he, hm⟩ ⟨hq, hf, hn⟩
    refine ⟨(totalDegree_add _ _).trans (max_le hp hq), ?_, ?_⟩
    · intro a b hab t ht
      simp only [map_add, he a b hab t ht, hf a b hab t ht, add_zero]
    · simp only [map_add, hm, hn, add_zero]
  smul_mem' := by
    rintro c q ⟨hq, he, hm⟩
    refine ⟨(totalDegree_smul_le _ _).trans hq, ?_, ?_⟩
    · intro a b hab t ht
      rw [MvPolynomial.smul_eval, he a b hab t ht, mul_zero]
    · simp only [map_smul, hm, smul_zero]

def restrictedD (σ : Equiv.Perm Coordinate) (o : Space) (s : ℕ) (hs : s ≤ 1) :
    sourceSpace s →ₗ[ℝ] targetSpace σ o s where
  toFun p := ⟨elementD σ o p.val,
    elementD_degree σ o s p.val p.property, elementD_zeroEdgeTrace σ o p.val,
      affine_elementD_zeroMean σ o p.val (fun j => (p.property j).trans hs)⟩
  map_add' p q := Subtype.ext ((elementD σ o).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((elementD σ o).map_smul c p.val)

theorem restrictedD_injective (σ : Equiv.Perm Coordinate) (o : Space)
    (s : ℕ) (hs : s ≤ 1) : Function.Injective (restrictedD σ o s hs) := by
  intro p q he
  have hd : elementD σ o (p.val - q.val) = 0 := by
    rw [(elementD σ o).map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val he)
  have hpq : ∀ j : Coordinate, ((p.val - q.val) j).totalDegree ≤ 1 := by
    intro j
    exact (PolynomialDegree.sub_degree_le _ _).trans
      (max_le ((p.property j).trans hs) ((q.property j).trans hs))
  have hz := affine_bubble_divergence_kernel σ o (p.val - q.val) hpq hd
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem restrictedD_surjective (σ : Equiv.Perm Coordinate) (o : Space)
    (s : ℕ) (hs : s ≤ 1) : Function.Surjective (restrictedD σ o s hs) := by
  intro q
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h
  · subst s
    let p : sourceSpace 0 := ⟨sourceCubic σ o q.val, sourceCubic_degree σ o q.val⟩
    refine ⟨p, Subtype.ext ?_⟩
    change PolynomialCalculus.polynomialDivergence (fun j => bubble σ o * sourceCubic σ o q.val j) = q.val
    rw [sourceCubic_field]
    exact cubicLift_divergence σ o q.val q.property.1 q.property.2.1 q.property.2.2
  · subst s
    let p : sourceSpace 1 := ⟨sourceQuartic σ o q.val, sourceQuartic_degree σ o q.val⟩
    refine ⟨p, Subtype.ext ?_⟩
    change PolynomialCalculus.polynomialDivergence (fun j => bubble σ o * sourceQuartic σ o q.val j) = q.val
    rw [sourceQuartic_field]
    exact quarticLift_divergence σ o q.val q.property.1 q.property.2.1 q.property.2.2

/-- The manuscript's low-degree element-bubble isomorphism on every
translated and coordinate-permuted unit tetrahedron.  Both inclusion and
bijectivity concern the actual source and zero-edge/zero-integral target. -/
def bubbleIsomorphism (σ : Equiv.Perm Coordinate) (o : Space) (s : ℕ) (hs : s ≤ 1) :
    sourceSpace s ≃ₗ[ℝ] targetSpace σ o s :=
  LinearEquiv.ofBijective (restrictedD σ o s hs)
    ⟨restrictedD_injective σ o s hs, restrictedD_surjective σ o s hs⟩

end FreudenthalSVLean.ElementBubbleRange
