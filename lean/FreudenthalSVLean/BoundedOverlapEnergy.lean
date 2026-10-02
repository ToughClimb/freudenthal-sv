import FreudenthalSVLean.VelocityEnergy

/-!
# Genuine gradient-energy estimates from local overlap

For manuscript Proposition `vertex` and the global assembly estimates,
only fields whose local polynomial is nonzero enter the pointwise
Cauchy--Schwarz bound.  A bound on the number of such fields per
tetrahedron, not on the total number of mesh vertices or edges, gives a
mesh-independent whole-mesh estimate.  The support hypotheses concern
actual polynomial identities and the energy uses actual Lebesgue
integrals.
-/

open scoped BigOperators
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.BoundedOverlapEnergy

theorem localEnergy_sum_overlap {I : Type*} {N : ℕ} (hN : 0 < N) (t : Tet N)
    (S F : Finset I) (v : I → LocalVelocity) (M : ℝ) (hM : 0 ≤ M)
    (hF : F ⊆ S) (hcard : (F.card : ℝ) ≤ M)
    (hv : ∀ i ∈ S, i ∉ F → v i = 0) :
    localEnergy t (∑ i ∈ S, v i) ≤ M * ∑ i ∈ S, localEnergy t (v i) := by
  have he : (∑ i ∈ F, v i) = ∑ i ∈ S, v i := Finset.sum_subset hF hv
  rw [← he]
  calc
    _ ≤ (F.card : ℝ) * ∑ i ∈ F, localEnergy t (v i) := localEnergy_sum hN t F v
    _ ≤ M * ∑ i ∈ S, localEnergy t (v i) := by
      apply mul_le_mul hcard (Finset.sum_le_sum_of_subset_of_nonneg hF (fun i _ _ => localEnergy_nonneg t (v i)))
        (Finset.sum_nonneg (fun i _ => localEnergy_nonneg t (v i))) hM

/-- The overlap bound precedes the actual count of mesh entities. -/
theorem velocityEnergy_sum_overlap {I : Type*} {N : ℕ} (hN : 0 < N)
    (S : Finset I) (v : I → BrokenVelocity N) (M : ℝ) (hM : 0 ≤ M)
    (hlocal : ∀ t : Tet N, ∃ F : Finset I, F ⊆ S ∧ (F.card : ℝ) ≤ M ∧
      ∀ i ∈ S, i ∉ F → v i t = 0) :
    velocityEnergy (∑ i ∈ S, v i) ≤ M * ∑ i ∈ S, velocityEnergy (v i) := by
  simp only [velocityEnergy_eq_sum, Finset.sum_apply]
  calc
    _ ≤ ∑ t : Tet N, M * ∑ i ∈ S, localEnergy t (v i t) := by
      apply Finset.sum_le_sum
      intro t _
      obtain ⟨F, hF, hc, hv⟩ := hlocal t
      exact localEnergy_sum_overlap hN t S F (fun i => v i t) M hM hF hc hv
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end FreudenthalSVLean.BoundedOverlapEnergy
