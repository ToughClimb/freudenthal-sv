import FreudenthalSVLean.ConformingFaceModes
import FreudenthalSVLean.StableFaceTransfer
import FreudenthalSVLean.ActualFaceEdgeTraces

/-!
# Uniform genuine gradient energy of weighted face fields

For the stability estimate in manuscript Lemma edge-star, arbitrary
fixed nodal powers on a two-owner face have energy bounded by one
constant times h times the squared vector amplitude. Coordinate
transport and actual Lebesgue scaling prove the bound. Missing nodal
factors and zero exponents are handled explicitly; two-owner support
proves the whole-mesh estimate.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ConformingFaceModes
open FreudenthalSVLean.ActualFaceEdgeTraces
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableWeightedFaceField

def unitPolynomial (σ : Equiv.Perm Coordinate) (o : Space) (p q : ℕ) (r a b : Vertex) :
    MvPolynomial Coordinate ℝ :=
  spatialFaceBubble σ o r * ChainGeometry.barycentric σ o a ^ p *
    ChainGeometry.barycentric σ o b ^ q

def referenceEnergy (p q : ℕ) (r a b : Vertex) : ℝ :=
  ∑ i : Coordinate, referenceSquareIntegral
    (pderiv i (unitPolynomial (Equiv.refl Coordinate) 0 p q r a b))

theorem referenceEnergy_nonneg (p q : ℕ) (r a b : Vertex) : 0 ≤ referenceEnergy p q r a b :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

def referenceBound (p q : ℕ) : ℝ :=
  1 + ∑ r : Vertex, ∑ a : Vertex, ∑ b : Vertex, referenceEnergy p q r a b

theorem referenceBound_pos (p q : ℕ) : 0 < referenceBound p q := by
  have hs : 0 ≤ ∑ r : Vertex, ∑ a : Vertex, ∑ b : Vertex, referenceEnergy p q r a b :=
    Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => referenceEnergy_nonneg p q r a b)))
  unfold referenceBound
  linarith

theorem referenceEnergy_le_bound (p q : ℕ) (r a b : Vertex) :
    referenceEnergy p q r a b ≤ referenceBound p q := by
  have hb := Finset.single_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset Vertex)) => referenceEnergy_nonneg p q r a c)
    (Finset.mem_univ b)
  have ha := Finset.single_le_sum (f := fun d : Vertex => ∑ c : Vertex, referenceEnergy p q r d c)
    (fun d _ => Finset.sum_nonneg (fun c _ => referenceEnergy_nonneg p q r d c)) (Finset.mem_univ a)
  have hr := Finset.single_le_sum
    (f := fun s : Vertex => ∑ d : Vertex, ∑ c : Vertex, referenceEnergy p q s d c)
    (fun s _ => Finset.sum_nonneg (fun d _ =>
      Finset.sum_nonneg (fun c _ => referenceEnergy_nonneg p q s d c))) (Finset.mem_univ r)
  unfold referenceBound
  linarith

theorem forward_unitPolynomial (σ : Equiv.Perm Coordinate) (o : Space)
    (p q : ℕ) (r a b : Vertex) :
    forward σ o (unitPolynomial (Equiv.refl Coordinate) 0 p q r a b) =
      unitPolynomial σ o p q r a b := by
  simp only [unitPolynomial, forward, map_mul, map_pow]
  change forward σ o (spatialFaceBubble (Equiv.refl Coordinate) 0 r) *
    (forward σ o (ChainGeometry.barycentric (Equiv.refl Coordinate) 0 a)) ^ p *
    (forward σ o (ChainGeometry.barycentric (Equiv.refl Coordinate) 0 b)) ^ q = _
  rw [StableFaceTransfer.forward_faceBubble σ o r,
    forward_barycentric σ o a, forward_barycentric σ o b]

theorem unitPolynomial_energy (σ : Equiv.Perm Coordinate) (o : Space)
    (p q : ℕ) (r a b : Vertex) :
    (∑ i : Coordinate, ∫ x in unitChainSet σ o,
      (eval x (pderiv i (unitPolynomial σ o p q r a b))) ^ 2) = referenceEnergy p q r a b := by
  rw [← forward_unitPolynomial σ o p q r a b]
  simp only [pderiv_forward, forward_square_integral]
  unfold referenceEnergy
  exact Equiv.sum_comp σ.symm (fun i : Coordinate => referenceSquareIntegral
    (pderiv i (unitPolynomial (Equiv.refl Coordinate) 0 p q r a b)))

theorem scaled_unitPolynomial_energy {N : ℕ} (hN : 0 < N) (t : Tet N)
    (p q : ℕ) (r a b : Vertex) (z : Space) :
    localEnergy t (fun j => rescale (meshScale N) (z j)
      (unitPolynomial t.2 (cellOrigin t.1) p q r a b)) =
      meshScale N * (∑ j : Coordinate, (z j) ^ 2) * referenceEnergy p q r a b := by
  rw [localEnergy_eq_sum hN]
  simp only [tetrahedron, derivative_energy_scaling t.2 (cellOrigin t.1)
    (meshScale N) (meshScale_pos N hN), ← Finset.mul_sum, unitPolynomial_energy]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem nodal_power_cases {N : ℕ} (t : Tet N) (n : GridVertex N) (p : ℕ) :
    meshNodalPolynomial t (integerGrid n) ^ p = 0 ∨
      ∃ a : Vertex, meshNodalPolynomial t (integerGrid n) ^ p =
        FreudenthalMesh.barycentric t a ^ p := by
  classical
  by_cases hp : p = 0
  · exact Or.inr ⟨0, by simp [hp]⟩
  · by_cases hn : n ∈ gridVertices t
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hn
      right
      refine ⟨a, ?_⟩
      rw [← ha, meshNodalPolynomial_eq_barycentric t _ a (gridVertex_intPoint t a)]
    · left
      simp [node_polynomial_zero_of_missing t n hn, hp]

theorem weighted_local_bound {N : ℕ} (hN : 0 < N) (t : Tet N)
    (r : Vertex) (a b : GridVertex N) (p q : ℕ) (z : Space) :
    localEnergy t (weightedFaceField N t r a b p q z t) ≤
      referenceBound p q * meshScale N * ∑ j : Coordinate, (z j) ^ 2 := by
  have hnon : 0 ≤ meshScale N * ∑ j : Coordinate, (z j) ^ 2 :=
    mul_nonneg (meshScale_pos N hN).le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rcases nodal_power_cases t a p with ha | ⟨α, ha⟩
  · have hz : weightedFaceField N t r a b p q z t = 0 := by
      funext j
      simp [weightedFaceField, ha]
    rw [hz, localEnergy_zero]
    nlinarith [referenceBound_pos p q]
  · rcases nodal_power_cases t b q with hb | ⟨β, hb⟩
    · have hz : weightedFaceField N t r a b p q z t = 0 := by
        funext j
        simp [weightedFaceField, hb]
      rw [hz, localEnergy_zero]
      nlinarith [referenceBound_pos p q]
    · have he : weightedFaceField N t r a b p q z t =
          fun j => rescale (meshScale N) (z j) (unitPolynomial t.2 (cellOrigin t.1) p q r α β) := by
        funext j
        simp only [weightedFaceField, ha, hb, faceScalar_self_rescale, unitPolynomial,
          rescale, FreudenthalMesh.barycentric, ScaledChainGeometry.scaledBarycentric,
          C_1, one_mul, map_mul, map_pow, mul_assoc]
      rw [he, scaled_unitPolynomial_energy hN]
      have h := mul_le_mul_of_nonneg_left (referenceEnergy_le_bound p q r α β) hnon
      nlinarith

/-- A common constant before all actual mesh and face data. -/
theorem weighted_global_bound (p q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N) (n : GridVertex N) (ta tb : VertexStar n) (r u : Vertex),
      r ≠ ta.val.2 → ta.val.1 ≠ tb.val.1 → gridFace ta.val.1 r = gridFace tb.val.1 u →
      ∀ (a b : GridVertex N) (z : Space),
      velocityEnergy (weightedFaceField N ta.val.1 r a b p q z) ≤
        C * meshScale N * ∑ j : Coordinate, (z j) ^ 2 := by
  classical
  refine ⟨2 * referenceBound p q, mul_pos (by norm_num) (referenceBound_pos p q), ?_⟩
  intro N hN n ta tb r u hr hne he a b z
  let v := weightedFaceField N ta.val.1 r a b p q z
  have hs (t : Tet N) : localEnergy t (v t) =
      (if t = ta.val.1 then localEnergy ta.val.1 (v ta.val.1) else 0) +
      (if t = tb.val.1 then localEnergy tb.val.1 (v tb.val.1) else 0) := by
    by_cases hta : t = ta.val.1
    · subst t
      simp [hne]
    · by_cases htb : t = tb.val.1
      · subst t
        simp [hne.symm]
      · have hz : v t = 0 := by
          funext j
          exact weightedFaceField_zero_off_pair ta tb r u hr hne he a b p q z t hta htb j
        simp only [hz, localEnergy_zero, if_neg hta, if_neg htb, add_zero]
  rw [velocityEnergy_eq_sum, Finset.sum_congr rfl (fun t _ => hs t)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hfirst := weighted_local_bound hN ta.val.1 r a b p q z
  have hsecond := weighted_local_bound hN tb.val.1 u a b p q z
  have hv : v tb.val.1 = weightedFaceField N tb.val.1 u a b p q z tb.val.1 :=
    weightedFaceField_shared ta.val.1 tb.val.1 r u he a b p q z
  change localEnergy ta.val.1 (weightedFaceField N ta.val.1 r a b p q z ta.val.1) +
    localEnergy tb.val.1 (v tb.val.1) ≤ _
  rw [hv]
  linarith

end FreudenthalSVLean.StableWeightedFaceField
