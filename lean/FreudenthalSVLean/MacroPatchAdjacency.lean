import FreudenthalSVLean.PhysicalMacroLift

/-!
# Actual face-adjacent cubes and the twelve-element macro patch

For manuscript Lemma `routing`, every face-neighbor pair of actual cubes
is identified with the translated coordinate-permuted two-cube patch of
Lemma `macro`.  The identification is proved for arbitrary `N` by integer
coordinate inequalities; no sampled-mesh coverage assertion is used.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.QuarticMacroConformity
open FreudenthalSVLean.PhysicalMacroFields
open FreudenthalSVLean.QuarticPatchCoverage
open FreudenthalSVLean.LatticeAffineTransport

noncomputable section

namespace FreudenthalSVLean.MacroPatchAdjacency

/-- An ordered face-neighbor pair, with the second cube one step above
the first in one coordinate. -/
def PositiveAdjacent {N : ℕ} (c d : Cell N) : Prop :=
  ∃ j : Coordinate, (d j).val = (c j).val + 1 ∧ ∀ r, r ≠ j → d r = c r

def FaceAdjacent {N : ℕ} (c d : Cell N) : Prop :=
  PositiveAdjacent c d ∨ PositiveAdjacent d c

theorem faceAdjacent_symm {N : ℕ} {c d : Cell N} (h : FaceAdjacent c d) :
    FaceAdjacent d c := h.symm

theorem positiveAdjacent_ne {N : ℕ} {c d : Cell N} (h : PositiveAdjacent c d) : c ≠ d := by
  obtain ⟨j, hj, _⟩ := h
  intro he
  rw [← he] at hj
  omega

theorem faceAdjacent_ne {N : ℕ} {c d : Cell N} (h : FaceAdjacent c d) : c ≠ d := by
  rcases h with h | h
  · exact positiveAdjacent_ne h
  · exact (positiveAdjacent_ne h).symm

/-- The inequalities defining the reference rectangle, written in actual
mesh coordinates. -/
theorem inPatch_coordinate_iff {N : ℕ} (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (t : Tet N) :
    inPatch π o t ↔ ∀ j, o j ≤ cellIntOrigin t.1 j ∧
      cellIntOrigin t.1 j < o j + upperCorner (π.symm j) := by
  constructor
  · intro h j
    have hj := h (π.symm j)
    simp only [relativeOrigin, inverseNode, Equiv.apply_symm_apply] at hj
    omega
  · intro h j
    have hj := h (π j)
    simp only [Equiv.symm_apply_apply] at hj
    change 0 ≤ cellIntOrigin t.1 (π j) - o (π j) ∧
      cellIntOrigin t.1 (π j) - o (π j) < upperCorner j
    omega

theorem swapped_upperCorner (j r : Coordinate) :
    upperCorner ((Equiv.swap 0 j).symm r) = if r = j then 2 else 1 := by
  have he : (Equiv.swap 0 j).symm r = 0 ↔ r = j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [upperCorner, he]

theorem positive_patch_fits {N : ℕ} (c d : Cell N) (j : Coordinate)
    (hj : (d j).val = (c j).val + 1) :
    patchFits N (Equiv.swap 0 j) (cellIntOrigin c) := by
  intro r
  rw [swapped_upperCorner]
  have hc := (c r).isLt
  have hd := (d j).isLt
  change 0 ≤ ((c r).val : ℤ) ∧
    ((c r).val : ℤ) + (if r = j then 2 else 1) ≤ (N : ℤ)
  by_cases hr : r = j
  · subst r
    simp only [if_true]
    omega
  · simp only [hr, if_false]
    omega

/-- Exact two-cube coverage, independent of the tetrahedron's coordinate
order and of the mesh size. -/
theorem positive_patch_owners {N : ℕ} (c d : Cell N) (j : Coordinate)
    (hj : (d j).val = (c j).val + 1) (ho : ∀ r, r ≠ j → d r = c r)
    (t : Tet N) :
    inPatch (Equiv.swap 0 j) (cellIntOrigin c) t ↔ t.1 = c ∨ t.1 = d := by
  rw [inPatch_coordinate_iff]
  constructor
  · intro ht
    have hcoord : ∀ r, r ≠ j → t.1 r = c r := by
      intro r hr
      have h := ht r
      rw [swapped_upperCorner, if_neg hr] at h
      change ((c r).val : ℤ) ≤ ((t.1 r).val : ℤ) ∧
        ((t.1 r).val : ℤ) < ((c r).val : ℤ) + 1 at h
      apply Fin.ext
      omega
    have hv := ht j
    rw [swapped_upperCorner, if_pos rfl] at hv
    change ((c j).val : ℤ) ≤ ((t.1 j).val : ℤ) ∧
      ((t.1 j).val : ℤ) < ((c j).val : ℤ) + 2 at hv
    by_cases he : t.1 j = c j
    · left
      funext r
      by_cases hr : r = j
      · subst r; exact he
      · exact hcoord r hr
    · right
      have hval : (t.1 j).val = (d j).val := by
        have hne : (t.1 j).val ≠ (c j).val := fun h => he (Fin.ext h)
        omega
      funext r
      by_cases hr : r = j
      · subst r; exact Fin.ext hval
      · exact (hcoord r hr).trans (ho r hr).symm
  · rintro (ht | ht) r
    · rw [ht, swapped_upperCorner]
      by_cases hr : r = j <;> simp [hr]
    · rw [ht, swapped_upperCorner]
      by_cases hr : r = j
      · subst r
        simp only [if_true]
        change ((c j).val : ℤ) ≤ ((d j).val : ℤ) ∧
          ((d j).val : ℤ) < ((c j).val : ℤ) + 2
        omega
      · simp [cellIntOrigin, ho r hr, hr]

/-- A face-neighbor pair fixes an admissible macro patch before any
prescribed mean vector is supplied. -/
theorem faceAdjacent_patch {N : ℕ} (c d : Cell N) (h : FaceAdjacent c d) :
    ∃ (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ),
      patchFits N π o ∧ ∀ t : Tet N, inPatch π o t ↔ t.1 = c ∨ t.1 = d := by
  rcases h with h | h
  · obtain ⟨j, hj, ho⟩ := h
    exact ⟨Equiv.swap 0 j, cellIntOrigin c, positive_patch_fits c d j hj,
      positive_patch_owners c d j hj ho⟩
  · obtain ⟨j, hj, ho⟩ := h
    refine ⟨Equiv.swap 0 j, cellIntOrigin d, positive_patch_fits d c j hj, ?_⟩
    intro t
    rw [positive_patch_owners d c j hj ho, or_comm]

/-- A fixed companion cube exists even for cubes meeting the boundary.
Its selection depends only on the cube, never on a mean input. -/
def companion {N : ℕ} (hN : 2 ≤ N) (c : Cell N) : Cell N :=
  Function.update c 0 ⟨if (c 0).val = 0 then 1 else (c 0).val - 1, by
    have hc := (c 0).isLt
    split_ifs <;> omega⟩

theorem companion_adjacent {N : ℕ} (hN : 2 ≤ N) (c : Cell N) :
    FaceAdjacent c (companion hN c) := by
  classical
  by_cases h0 : (c 0).val = 0
  · left
    refine ⟨0, ?_, ?_⟩
    · simp [companion, h0]
    · intro r hr
      simp [companion, hr]
  · right
    refine ⟨0, ?_, ?_⟩
    · have hc : 0 < (c 0).val := by omega
      simp only [companion, Function.update_self, h0, if_false]
      omega
    · intro r hr
      simp [companion, hr]

theorem companion_ne {N : ℕ} (hN : 2 ≤ N) (c : Cell N) : c ≠ companion hN c :=
  faceAdjacent_ne (companion_adjacent hN c)

/-- Any two tetrahedra in the same cube or in face-neighbor cubes admit a
fixed common macro patch.  In the same-cube case only one companion is
needed, so the polynomial support is still confined to two cubes. -/
theorem local_pair_patch {N : ℕ} (hN : 2 ≤ N) (t u : Tet N)
    (h : t.1 = u.1 ∨ FaceAdjacent t.1 u.1) :
    ∃ (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ), patchFits N π o ∧
      inPatch π o t ∧ inPatch π o u ∧
      ∀ v : Tet N, inPatch π o v →
        v.1 = t.1 ∨ FaceAdjacent t.1 v.1 := by
  rcases h with he | ha
  · obtain ⟨π, o, hf, ho⟩ := faceAdjacent_patch t.1 (companion hN t.1)
      (companion_adjacent hN t.1)
    refine ⟨π, o, hf, (ho t).mpr (Or.inl rfl), (ho u).mpr (Or.inl he.symm), ?_⟩
    intro v hv
    rcases (ho v).mp hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (hv ▸ companion_adjacent hN t.1)
  · obtain ⟨π, o, hf, ho⟩ := faceAdjacent_patch t.1 u.1 ha
    refine ⟨π, o, hf, (ho t).mpr (Or.inl rfl), (ho u).mpr (Or.inr rfl), ?_⟩
    intro v hv
    rcases (ho v).mp hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (hv ▸ ha)

end FreudenthalSVLean.MacroPatchAdjacency
