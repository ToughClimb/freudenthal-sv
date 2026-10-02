import FreudenthalSVLean.MacroPatchAdjacency

/-!
# Edge-protecting actual element-mean transfers

For manuscript Lemma `routing`, the actual quartic macro inverse gives a
transfer with genuine divergence means `delta_T - delta_U` for any two
owners of a fixed admissible patch.  All element-edge restrictions remain
zero, including on nonowners.  The energy bound has one constant before
the mesh size, patch geometry and owner choices.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticReferenceLift
open FreudenthalSVLean.PhysicalMacroFields
open FreudenthalSVLean.PhysicalMacroLift
open FreudenthalSVLean.QuarticPatchCoverage
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MeanRoutingAlgebra

noncomputable section

namespace FreudenthalSVLean.MacroMeanTransfer

set_option backward.isDefEq.respectTransparency false

/-- Actual divergence means, as a linear map on conforming velocities. -/
def elementMeans {N : ℕ} (hN : 0 < N) (k : ℕ) :
    velocitySpace N k →ₗ[ℝ] (Tet N → ℝ) :=
  LinearMap.pi (fun t => (tetIntegral hN t).comp
    ((LinearMap.proj t).comp ((divergence N).comp (velocitySpace N k).subtype)))

theorem elementMeans_apply {N : ℕ} (hN : 0 < N) (k : ℕ)
    (v : velocitySpace N k) (t : Tet N) :
    elementMeans hN k v t = tetIntegral hN t (divergence N v.val t) := rfl

def ownerIndex {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t) : TetIndex :=
  Classical.choose (patchTet_surjective_on_patch π o hf t ht)

theorem ownerIndex_spec {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t) :
    patchTet π o hf (ownerIndex π o hf t ht) = t :=
  Classical.choose_spec (patchTet_surjective_on_patch π o hf t ht)

def pairMeans (i j : TetIndex) : CompatibleMeans :=
  ⟨Pi.single i 1 - Pi.single j 1, by
    rw [mem_zeroSum]
    simp [Finset.sum_sub_distrib, Pi.single_apply]⟩

theorem pairMeans_square_sum (i j : TetIndex) :
    (∑ r : TetIndex, ((pairMeans i j).val r) ^ 2) ≤ 2 := by
  classical
  have hp (r : TetIndex) : ((pairMeans i j).val r) ^ 2 ≤
      ((Pi.single i (1 : ℝ) : TetIndex → ℝ) r) ^ 2 +
        ((Pi.single j (1 : ℝ) : TetIndex → ℝ) r) ^ 2 := by
    simp only [pairMeans, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ r : TetIndex, (((Pi.single i (1 : ℝ) : TetIndex → ℝ) r) ^ 2 +
        ((Pi.single j (1 : ℝ) : TetIndex → ℝ) r) ^ 2) := Finset.sum_le_sum (fun r _ => hp r)
    _ = 2 := by norm_num [Finset.sum_add_distrib, Pi.single_apply]

def transfer {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t)
    (u : Tet N) (hu : inPatch π o u) : velocitySpace N 4 :=
  physicalLift hN π o hf (pairMeans (ownerIndex π o hf t ht) (ownerIndex π o hf u hu))

/-- The transfer has the required means on every actual tetrahedron,
not just on the twelve reference labels. -/
theorem transfer_means {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t)
    (u : Tet N) (hu : inPatch π o u) :
    elementMeans hN 4 (transfer hN π o hf t ht u hu) =
      Pi.single t 1 - Pi.single u 1 := by
  classical
  funext v
  rw [elementMeans_apply]
  by_cases hv : inPatch π o v
  · obtain ⟨r, rfl⟩ := patchTet_surjective_on_patch π o hf v hv
    change tetIntegral hN _ (divergence N
      (physicalLift hN π o hf (pairMeans (ownerIndex π o hf t ht)
        (ownerIndex π o hf u hu))).val _) = _
    rw [physicalLift_means]
    have hi : r = ownerIndex π o hf t ht ↔ patchTet π o hf r = t := by
      constructor
      · intro he
        exact (congrArg (patchTet π o hf) he).trans (ownerIndex_spec π o hf t ht)
      · intro he
        exact patchTet_injective π o hf (he.trans (ownerIndex_spec π o hf t ht).symm)
    have hj : r = ownerIndex π o hf u hu ↔ patchTet π o hf r = u := by
      constructor
      · intro he
        exact (congrArg (patchTet π o hf) he).trans (ownerIndex_spec π o hf u hu)
      · intro he
        exact patchTet_injective π o hf (he.trans (ownerIndex_spec π o hf u hu).symm)
    simp only [pairMeans, Pi.sub_apply, Pi.single_apply, hi, hj]
  · have hvt : v ≠ t := by intro he; subst v; exact hv ht
    have hvu : v ≠ u := by intro he; subst v; exact hv hu
    change tetIntegral hN v (divergence N
      (physicalLift hN π o hf (pairMeans (ownerIndex π o hf t ht)
        (ownerIndex π o hf u hu))).val v) = _
    rw [physicalLift_mean_zero_off_patch hN π o hf _ v hv]
    simp [hvt, hvu]

theorem transfer_zero_off_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t)
    (u : Tet N) (hu : inPatch π o u) (v : Tet N) (hv : ¬ inPatch π o v) :
    (transfer hN π o hf t ht u hu).val v = 0 :=
  physicalLift_zero_off_patch hN π o hf _ v hv

theorem transfer_zero_edges {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t)
    (u : Tet N) (hu : inPatch π o u) (v : Tet N) (a b : Vertex) (s : ℝ) :
    eval (segmentPoint (vertex v a) (vertex v b) s)
      (divergence N (transfer hN π o hf t ht u hu).val v) = 0 :=
  physicalLift_all_edges_zero hN π o hf _ v a b s

theorem transfer_uniform_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
      (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t)
      (u : Tet N) (hu : inPatch π o u),
      velocityEnergy (transfer hN π o hf t ht u hu).val ≤ C * ((meshScale N) ^ 3)⁻¹ := by
  obtain ⟨C, hC, hE⟩ := physicalLift_uniform_energy
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN π o hf t ht u hu
  have hscale : 0 ≤ C * ((meshScale N) ^ 3)⁻¹ := by positivity [meshScale_pos N hN]
  calc
    _ ≤ C * ((meshScale N) ^ 3)⁻¹ * ∑ r : TetIndex,
        ((pairMeans (ownerIndex π o hf t ht) (ownerIndex π o hf u hu)).val r) ^ 2 :=
      hE N hN π o hf _
    _ ≤ C * ((meshScale N) ^ 3)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left (pairMeans_square_sum _ _) hscale
    _ = _ := by ring

end FreudenthalSVLean.MacroMeanTransfer
