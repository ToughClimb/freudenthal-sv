import FreudenthalSVLean.ActualFaceMean
import FreudenthalSVLean.VelocityEnergy
import FreudenthalSVLean.PolynomialChainTransport

/-!
# Geometry-independent energy of normalized face transfers

For manuscript equation `vertex-face-transfer` and its `h^{-3}` energy
estimate, coordinate transport reduces each unit face field to one of the
four actual reference polynomials.  Exact positive-scale differentiation
and integration then give the physical energy factor `h^{-3}`.
There is no input-dependent geometry or unproved scaling assertion.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.StableFaceTransfer

theorem gradient_permuted (σ : Equiv.Perm Coordinate) (r : Vertex) (j : Coordinate) :
    ChainGeometry.barycentricGradient (R := ℝ) σ r j =
      ChainGeometry.barycentricGradient (R := ℝ) (Equiv.refl Coordinate) r (σ.symm j) := by
  obtain ⟨j, rfl⟩ := σ.surjective j
  fin_cases r <;> simp [ChainGeometry.barycentricGradient, ChainGeometry.coordinateUnit,
    σ.injective.eq_iff] <;> rfl

theorem unitTransferVector_permuted (σ : Equiv.Perm Coordinate) (r : Vertex) (j : Coordinate) :
    unitTransferVector σ r j = unitTransferVector (Equiv.refl Coordinate) r (σ.symm j) := by
  unfold unitTransferVector
  rw [face_gradient_norm_square, face_gradient_norm_square, gradient_permuted σ r j]

def unitField (σ : Equiv.Perm Coordinate) (o : Space) (r : Vertex) : LocalVelocity :=
  fun j => C (unitTransferVector σ r j) * spatialFaceBubble σ o r

theorem forward_faceBubble (σ : Equiv.Perm Coordinate) (o : Space) (r : Vertex) :
    forward σ o (spatialFaceBubble (Equiv.refl Coordinate) 0 r) = spatialFaceBubble σ o r := by
  simp only [spatialFaceBubble_eq_product, forward, map_prod]
  apply Finset.prod_congr rfl
  intro a _
  exact forward_barycentric σ o a

theorem pushVector_unitField (σ : Equiv.Perm Coordinate) (o : Space) (r : Vertex) :
    pushVector σ o (unitField (Equiv.refl Coordinate) 0 r) = unitField σ o r := by
  funext j
  change forward σ o (C (unitTransferVector (Equiv.refl Coordinate) r (σ.symm j)) *
    spatialFaceBubble (Equiv.refl Coordinate) 0 r) = _
  have hm (c : ℝ) (p : MvPolynomial Coordinate ℝ) :
      forward σ o (C c * p) = C c * forward σ o p := by simp [forward, map_mul]
  rw [hm, forward_faceBubble]
  change C (unitTransferVector (Equiv.refl Coordinate) r (σ.symm j)) * spatialFaceBubble σ o r =
    C (unitTransferVector σ r j) * spatialFaceBubble σ o r
  rw [unitTransferVector_permuted σ r j]

def referenceEnergy (r : Vertex) : ℝ :=
  ∑ j : Coordinate, ∑ i : Coordinate,
    referenceSquareIntegral (pderiv i (unitField (Equiv.refl Coordinate) 0 r j))

theorem referenceEnergy_nonneg (r : Vertex) : 0 ≤ referenceEnergy r := by
  unfold referenceEnergy referenceSquareIntegral
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem unitField_energy (σ : Equiv.Perm Coordinate) (o : Space) (r : Vertex) :
    (∑ j : Coordinate, ∑ i : Coordinate,
      ∫ x in unitChainSet σ o, (eval x (pderiv i (unitField σ o r j))) ^ 2) =
        referenceEnergy r := by
  rw [← pushVector_unitField σ o r]
  exact pushVector_energy σ o (unitField (Equiv.refl Coordinate) 0 r)

theorem transferField_self_rescale {N : ℕ} (t : Tet N) (r : Vertex) (j : Coordinate) :
    transferField N t r t j =
      rescale (meshScale N) ((meshScale N) ^ 2)⁻¹ (unitField t.2 (cellOrigin t.1) r j) := by
  simp only [transferField, faceField, transferVector, faceScalar_self_rescale, unitField,
    rescale, map_mul, eval₂Hom_C, C_1, one_mul, inv_pow]
  ring

/-- Exact local energy on the positively oriented owner. -/
theorem transfer_local_energy {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Vertex) :
    localEnergy t (transferField N t r t) =
      ((meshScale N) ^ 3)⁻¹ * referenceEnergy r := by
  rw [localEnergy_eq_sum hN]
  simp only [transferField_self_rescale]
  have hs (j i : Coordinate) :
      (∫ x in tetrahedron t, (eval x (pderiv i
        (rescale (meshScale N) ((meshScale N) ^ 2)⁻¹
          (unitField t.2 (cellOrigin t.1) r j)))) ^ 2) =
        ((meshScale N) ^ 3)⁻¹ * ∫ y in unitChainSet t.2 (cellOrigin t.1),
          (eval y (pderiv i (unitField t.2 (cellOrigin t.1) r j))) ^ 2 :=
    macro_derivative_energy_scaling t.2 (cellOrigin t.1) (meshScale N)
      (meshScale_pos N hN) _ i
  simp only [hs, ← Finset.mul_sum, unitField_energy]

theorem transferVector_opposite {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1)
    (he : ActualVertexStarGraph.gridFace ta.val.1 r = ActualVertexStarGraph.gridFace tb.val.1 u)
    (j : Coordinate) : transferVector N ta.val.1 r j = -transferVector N tb.val.1 u j := by
  have hg (l : Coordinate) := actual_shared_gradients_opposite ta tb r u hr hu hne he l
  have hs : (∑ l : Coordinate, (ChainGeometry.barycentricGradient (R := ℝ) ta.val.1.2 r l) ^ 2) =
      ∑ l : Coordinate, (ChainGeometry.barycentricGradient (R := ℝ) tb.val.1.2 u l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l _
    rw [hg l]
    ring
  simp only [transferVector, unitTransferVector, hs, hg j]
  ring

theorem transferField_reverse {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1)
    (he : ActualVertexStarGraph.gridFace ta.val.1 r = ActualVertexStarGraph.gridFace tb.val.1 u) :
    transferField N ta.val.1 r = (-1 : ℝ) • transferField N tb.val.1 u := by
  funext t j
  simp only [transferField, faceField, faceScalar, Pi.smul_apply, smul_eq_C_mul,
    transferVector_opposite ta tb r u hr hu hne he j, he, C_neg, C_1]
  ring

theorem transfer_other_energy {N : ℕ} (hN : 0 < N) {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1)
    (he : ActualVertexStarGraph.gridFace ta.val.1 r = ActualVertexStarGraph.gridFace tb.val.1 u) :
    localEnergy tb.val.1 (transferField N ta.val.1 r tb.val.1) =
      ((meshScale N) ^ 3)⁻¹ * referenceEnergy u := by
  rw [transferField_reverse ta tb r u hr hu hne he]
  change localEnergy tb.val.1 ((-1 : ℝ) • (transferField N tb.val.1 u tb.val.1)) = _
  rw [localEnergy_smul, transfer_local_energy hN]
  norm_num

/-- Exact whole-mesh energy of the two-owner field; non-star and all
other star elements contribute zero by the proved polynomial support. -/
theorem transfer_global_energy {N : ℕ} (hN : 0 < N) {n : GridVertex N} (ta tb : VertexStar n)
    (r u : Vertex) (hr : r ≠ ta.val.2) (hu : u ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1)
    (he : ActualVertexStarGraph.gridFace ta.val.1 r = ActualVertexStarGraph.gridFace tb.val.1 u) :
    velocityEnergy (transferField N ta.val.1 r) =
      ((meshScale N) ^ 3)⁻¹ * (referenceEnergy r + referenceEnergy u) := by
  classical
  have hs (t : Tet N) : localEnergy t (transferField N ta.val.1 r t) =
      (if t = ta.val.1 then localEnergy ta.val.1 (transferField N ta.val.1 r ta.val.1) else 0) +
      (if t = tb.val.1 then localEnergy tb.val.1 (transferField N ta.val.1 r tb.val.1) else 0) := by
    by_cases hta : t = ta.val.1
    · subst t
      simp [hne]
    · by_cases htb : t = tb.val.1
      · subst t
        simp [hne.symm]
      · have hz : transferField N ta.val.1 r t = 0 := by
          funext j
          exact transfer_zero_off_pair ta tb r u hr hne he t hta htb j
        simp only [hz, localEnergy_zero, if_neg hta, if_neg htb, add_zero]
  rw [velocityEnergy_eq_sum]
  rw [Finset.sum_congr rfl (fun t _ => hs t)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [transfer_local_energy hN, transfer_other_energy hN ta tb r u hr hu hne he]
  ring

def referenceBound : ℝ := 1 + ∑ r : Vertex, referenceEnergy r

theorem referenceBound_pos : 0 < referenceBound := by
  have h := Finset.sum_nonneg (fun r (_ : r ∈ (Finset.univ : Finset Vertex)) => referenceEnergy_nonneg r)
  unfold referenceBound
  linarith

theorem referenceEnergy_le_bound (r : Vertex) : referenceEnergy r ≤ referenceBound := by
  have h := Finset.single_le_sum
    (fun l (_ : l ∈ (Finset.univ : Finset Vertex)) => referenceEnergy_nonneg l) (Finset.mem_univ r)
  unfold referenceBound
  linarith

/-- A single constant is chosen before mesh size, vertex, orientation,
and face.  The right-hand side is the actual physical `h^{-3}` scale. -/
theorem transfer_uniform_energy : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_hN : 0 < N)
    (n : GridVertex N) (ta tb : VertexStar n) (r u : Vertex),
    r ≠ ta.val.2 → u ≠ tb.val.2 → ta.val.1 ≠ tb.val.1 →
    ActualVertexStarGraph.gridFace ta.val.1 r = ActualVertexStarGraph.gridFace tb.val.1 u →
      velocityEnergy (transferField N ta.val.1 r) ≤ C * ((meshScale N) ^ 3)⁻¹ := by
  refine ⟨2 * referenceBound, mul_pos (by norm_num) referenceBound_pos, ?_⟩
  intro N hN n ta tb r u hr hu hne he
  rw [transfer_global_energy hN ta tb r u hr hu hne he]
  calc
    _ ≤ ((meshScale N) ^ 3)⁻¹ * (2 * referenceBound) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (meshScale_pos N hN).le _))
      linarith [referenceEnergy_le_bound r, referenceEnergy_le_bound u]
    _ = _ := by ring

end FreudenthalSVLean.StableFaceTransfer
