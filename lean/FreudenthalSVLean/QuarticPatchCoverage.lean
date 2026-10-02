import FreudenthalSVLean.PhysicalMacroFields

/-!
# Exact arbitrary-mesh coverage of the physical two-cube macro patch

For manuscript Lemma `macro` and its affine `macro-scale` transport, the
twelve reference labels parameterize exactly every actual tetrahedron of
the two chosen cubes.  Every actual nonowner has an integer relative
origin outside the rectangle.  The translated nodal products consequently
vanish there as polynomials.  The reference enumeration enters through
an explicit all-origin/all-permutation equivalence, not through sampled
meshes or an assumed coverage assertion.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticNodalRealization
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.QuarticMacroConformity
open FreudenthalSVLean.LatticeAffineTransport
open FreudenthalSVLean.PhysicalMacroFields
open FreudenthalSVLean.PolynomialScaling

noncomputable section

namespace FreudenthalSVLean.QuarticPatchCoverage

def referenceIndex (side : Bool) (r : LocalTetIndex) : TetIndex :=
  ⟨r.val + if side then 6 else 0, by have hr := r.isLt; split_ifs <;> omega⟩

theorem referenceIndex_origin : ∀ (side : Bool) (r : LocalTetIndex),
    integerCorner (referenceIndex side r) = fun j => if j = 0 ∧ side = true then 1 else 0 := by
  decide +kernel

theorem referenceIndex_order : ∀ (side : Bool) (r : LocalTetIndex),
    tetPermutation (referenceIndex side r) = MeshCoverage.orderMap r := by
  decide +kernel

theorem referenceIndex_perm (side : Bool) (r : LocalTetIndex) :
    tetEquiv (referenceIndex side r) = MeshCoverage.orderPerm r := by
  apply Equiv.ext
  intro j
  exact congrFun (referenceIndex_order side r) j

/-- All unit lattice tetrahedra in the rectangle have one of the twelve
reference labels, for arbitrary integer origins and coordinate orders. -/
theorem reference_label_exists (c : Coordinate → ℤ) (σ : Equiv.Perm Coordinate)
    (hc : ∀ j, 0 ≤ c j ∧ c j < upperCorner j) :
    ∃ i : TetIndex, integerCorner i = c ∧ tetEquiv i = σ := by
  obtain ⟨r, hr⟩ := VertexStarTypes.orderPerm_bijective.2 σ
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  norm_num [upperCorner] at h0 h1 h2
  change 0 ≤ c 2 ∧ c 2 < 1 at h2
  have hc1 : c 1 = 0 := by omega
  have hc2 : c 2 = 0 := by omega
  by_cases hc0 : c 0 = 0
  · refine ⟨referenceIndex false r, ?_, (referenceIndex_perm false r).trans hr⟩
    rw [referenceIndex_origin]
    funext j
    fin_cases j <;> simp [hc0, hc1, hc2]
  · have hc0' : c 0 = 1 := by omega
    refine ⟨referenceIndex true r, ?_, (referenceIndex_perm true r).trans hr⟩
    rw [referenceIndex_origin]
    funext j
    fin_cases j <;> simp [hc0', hc1, hc2]

def relativeOrigin {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (t : Tet N) : Coordinate → ℤ := inverseNode π o (cellIntOrigin t.1)

def inPatch {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ) (t : Tet N) : Prop :=
  ∀ j, 0 ≤ relativeOrigin π o t j ∧ relativeOrigin π o t j < upperCorner j

theorem patchTet_inPatch {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) : inPatch π o (patchTet π o hf i) := by
  intro j
  simp only [relativeOrigin, patchTet_origin, inverseNode_affine]
  exact reference_corner_bounds i j

/-- Every actual patch owner is the image of a reference tetrahedron. -/
theorem patchTet_surjective_on_patch {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (t : Tet N) (ht : inPatch π o t) :
    ∃ i : TetIndex, patchTet π o hf i = t := by
  obtain ⟨i, hi, hp⟩ := reference_label_exists (relativeOrigin π o t) (t.2.trans π.symm) ht
  refine ⟨i, Prod.ext ?_ ?_⟩
  · have hc : cellIntOrigin (patchTet π o hf i).1 = cellIntOrigin t.1 := by
      rw [patchTet_origin, hi]
      exact affineNode_inverse π o _
    funext j
    apply Fin.ext
    have hj := congrFun hc j
    change (((patchTet π o hf i).1 j).val : ℤ) = ((t.1 j).val : ℤ) at hj
    exact_mod_cast hj
  · rw [patchTet_permutation, hp]
    apply Equiv.ext
    intro j
    simp

theorem inPatch_iff_owner {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (t : Tet N) :
    inPatch π o t ↔ ∃ i : TetIndex, patchTet π o hf i = t := by
  constructor
  · exact patchTet_surjective_on_patch π o hf t
  · rintro ⟨i, rfl⟩
    exact patchTet_inPatch π o hf i

/-- No nonowner carries a nonzero polynomial field.  This includes every
boundary position and every arbitrary mesh size admitting the patch. -/
theorem field_zero_off_patch {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (w : FieldIndex) (amplitude : ℝ) (t : Tet N) (ht : ¬ inPatch π o t) :
    field N π o w amplitude t = 0 := by
  have ho : ∃ j, relativeOrigin π o t j < 0 ∨ upperCorner j ≤ relativeOrigin π o t j := by
    unfold inPatch at ht
    push Not at ht
    obtain ⟨j, hj⟩ := ht
    refine ⟨j, ?_⟩
    by_cases hl : relativeOrigin π o t j < 0
    · exact Or.inl hl
    · exact Or.inr (hj (le_of_not_gt hl))
  funext j
  rw [field_representation]
  have hv : nodalVector w (t.2.trans π.symm) (inverseNode π o (cellIntOrigin t.1)) = 0 := by
    funext l
    exact nodalVector_zero_off_rectangle w _ _ ho l
  rw [hv]
  simp [PolynomialChainTransport.pushVector, PolynomialChainTransport.forward, rescale]

end FreudenthalSVLean.QuarticPatchCoverage
