import FreudenthalSVLean.VertexStarSymmetry
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Exact physical symmetries of the Freudenthal mesh

For the manuscript's seven-type edge lifting theorem, coordinate
permutations and central inversion act on the actual arbitrary-size mesh,
not only on its finite incidence labels.  This module proves covariance of
grid vertices, physical tetrahedra and boundary traces, and preservation of
Lebesgue measure.  Central inversion reverses the four-vertex chain; it
also interchanges the lower and upper boundary labels.
-/

open scoped BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry

noncomputable section

namespace FreudenthalSVLean.CubeMeshSymmetry

def permPoint (π : Equiv.Perm Coordinate) : Space ≃ᵐ Space :=
  MeasurableEquiv.piCongrLeft (fun _ : Coordinate => ℝ) π

theorem permPoint_apply (π : Equiv.Perm Coordinate) (x : Space) (j : Coordinate) :
    permPoint π x j = x (π.symm j) := by
  simp [permPoint, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

def reversePoint : Space ≃ᵐ Space := MeasurableEquiv.subLeft (1 : Space)

theorem reversePoint_apply (x : Space) (j : Coordinate) :
    reversePoint x j = 1 - x j := rfl

theorem permPoint_preserving (π : Equiv.Perm Coordinate) :
    MeasurePreserving (permPoint π) :=
  volume_measurePreserving_piCongrLeft (fun _ : Coordinate => ℝ) π

theorem reversePoint_preserving : MeasurePreserving reversePoint := by
  exact volume_preserving_pi (fun _ : Coordinate =>
    Measure.measurePreserving_sub_left (volume : Measure ℝ) 1)

def permNode {N : ℕ} (π : Equiv.Perm Coordinate) (n : GridVertex N) : GridVertex N :=
  fun j => n (π.symm j)

def reverseNode {N : ℕ} (n : GridVertex N) : GridVertex N :=
  fun j => Fin.rev (n j)

def permCell {N : ℕ} (π : Equiv.Perm Coordinate) (c : Cell N) : Cell N :=
  fun j => c (π.symm j)

def reverseCell {N : ℕ} (c : Cell N) : Cell N := fun j => Fin.rev (c j)

def permTet {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N) : Tet N :=
  (permCell π t.1, t.2.trans π)

def reverseTet {N : ℕ} (t : Tet N) : Tet N :=
  (reverseCell t.1, reverseCoordinate.trans t.2)

theorem permNode_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (n : GridVertex N) :
    permNode π.symm (permNode π n) = n := by
  funext j
  simp [permNode]

theorem reverseNode_involutive {N : ℕ} :
    Function.Involutive (reverseNode (N := N)) := by
  intro n
  funext j
  exact Fin.rev_rev _

theorem permTet_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N) :
    permTet π.symm (permTet π t) = t := by
  apply Prod.ext
  · funext j
    simp [permTet, permCell]
  · ext j
    simp [permTet]

theorem reverseTet_involutive {N : ℕ} :
    Function.Involutive (reverseTet (N := N)) := by
  intro t
  apply Prod.ext
  · funext j
    exact Fin.rev_rev _
  · ext j
    simp [reverseTet, reverseCoordinate]

def permTetEquiv {N : ℕ} (π : Equiv.Perm Coordinate) : Tet N ≃ Tet N where
  toFun := permTet π
  invFun := permTet π.symm
  left_inv := permTet_inverse π
  right_inv t := by simpa using permTet_inverse π.symm t

def reverseTetEquiv {N : ℕ} : Tet N ≃ Tet N :=
  Function.Involutive.toPerm reverseTet reverseTet_involutive

theorem perm_gridVertex {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N) (a : Vertex) :
    gridVertexOfTet (permTet π t) a = permNode π (gridVertexOfTet t a) := rfl

theorem reverse_gridVertex {N : ℕ} (t : Tet N) (a : Vertex) :
    gridVertexOfTet (reverseTet t) (Fin.rev a) = reverseNode (gridVertexOfTet t a) := by
  funext j
  apply Fin.ext
  have hp := prefix_le_one (t.2, a) j
  have hc := (t.1 j).isLt
  change (Fin.rev (t.1 j)).val + prefixMask (reverseState (t.2, a)) j =
    (Fin.rev (gridVertexOfTet t a j)).val
  rw [reverse_prefix]
  simp only [Fin.val_rev, gridVertexOfTet]
  omega

theorem perm_gridPoint {N : ℕ} (π : Equiv.Perm Coordinate) (n : GridVertex N) :
    gridPoint (permNode π n) = permPoint π (gridPoint n) := by
  funext j
  rw [permPoint_apply]
  rfl

theorem reverse_gridPoint {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    gridPoint (reverseNode n) = reversePoint (gridPoint n) := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  funext j
  have hv : (Fin.rev (n j)).val + (n j).val = N := by
    simp only [Fin.val_rev]
    omega
  have hvr : ((Fin.rev (n j)).val : ℝ) = (N : ℝ) - (n j).val := by
    have he : ((Fin.rev (n j)).val : ℝ) + (n j).val = (N : ℝ) := by
      exact_mod_cast hv
    linarith
  change (N : ℝ)⁻¹ * ((Fin.rev (n j)).val : ℝ) = 1 - (N : ℝ)⁻¹ * (n j).val
  rw [hvr]
  field_simp

theorem perm_vertex {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N) (a : Vertex) :
    vertex (permTet π t) a = permPoint π (vertex t a) := by
  rw [← gridVertexOfTet_point, perm_gridVertex, perm_gridPoint, gridVertexOfTet_point]

theorem reverse_vertex {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Vertex) :
    vertex (reverseTet t) (Fin.rev a) = reversePoint (vertex t a) := by
  rw [← gridVertexOfTet_point, reverse_gridVertex, reverse_gridPoint hN,
    gridVertexOfTet_point]

theorem perm_boundaryTag {N : ℕ} (π : Equiv.Perm Coordinate) (n : GridVertex N) :
    boundaryTag (permNode π n) = relabelTags π (boundaryTag n) := rfl

theorem reverse_boundaryTag {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    boundaryTag (reverseNode n) = reverseTags (boundaryTag n) := by
  funext j
  have hv : (Fin.rev (n j)).val + (n j).val = N := by
    simp only [Fin.val_rev]
    omega
  have hz : (Fin.rev (n j)).val = 0 ↔ (n j).val = N := by omega
  have hu : (Fin.rev (n j)).val = N ↔ (n j).val = 0 := by omega
  change (if (Fin.rev (n j)).val = 0 then 0 else
    if (Fin.rev (n j)).val = N then 2 else 1) =
      Fin.rev (if (n j).val = 0 then 0 else if (n j).val = N then 2 else 1)
  simp only [hz, hu]
  by_cases h0 : (n j).val = 0
  · have h2 : (n j).val ≠ N := by omega
    simp [h0, (Nat.ne_of_gt hN).symm]
  · by_cases h2 : (n j).val = N <;> simp [h0, h2, Nat.ne_of_gt hN]

def normalizedChain {N : ℕ} (t : Tet N) (x : Space) : Space :=
  unitNormalize t.2 (cellOrigin t.1) ((meshScale N)⁻¹ • x)

theorem normalizedChain_apply {N : ℕ} (t : Tet N) (x : Space) (j : Coordinate) :
    normalizedChain t x j = (N : ℝ) * x (t.2 j) - (t.1 (t.2 j)).val := by
  simp [normalizedChain, unitNormalize_apply, cellOrigin, meshScale,
    Pi.smul_apply, smul_eq_mul]

theorem tetrahedron_mem_iff {N : ℕ} (t : Tet N) (x : Space) :
    x ∈ tetrahedron t ↔ normalizedChain t x ∈ coordinateChainSet := Iff.rfl

theorem perm_normalizedChain {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N)
    (x : Space) : normalizedChain (permTet π t) (permPoint π x) = normalizedChain t x := by
  funext j
  simp [normalizedChain_apply, permTet, permCell, permPoint_apply]

theorem reverse_normalizedChain {N : ℕ} (t : Tet N) (x : Space) (j : Coordinate) :
    normalizedChain (reverseTet t) (reversePoint x) j =
      1 - normalizedChain t x (Fin.rev j) := by
  have hc := (t.1 (t.2 (Fin.rev j))).isLt
  have hv : (Fin.rev (t.1 (t.2 (Fin.rev j)))).val +
      (t.1 (t.2 (Fin.rev j))).val + 1 = N := by
    simp only [Fin.val_rev]
    omega
  have hvr : ((Fin.rev (t.1 (t.2 (Fin.rev j)))).val : ℝ) =
      (N : ℝ) - (t.1 (t.2 (Fin.rev j))).val - 1 := by
    have he : ((Fin.rev (t.1 (t.2 (Fin.rev j)))).val : ℝ) +
        (t.1 (t.2 (Fin.rev j))).val + 1 = (N : ℝ) := by exact_mod_cast hv
    linarith
  simp only [normalizedChain_apply, reverseTet, Equiv.trans_apply,
    reverseCoordinate, Equiv.coe_fn_mk, reversePoint_apply, reverseCell]
  rw [hvr]
  ring

theorem coordinateChain_reverse (x : Space) :
    (fun j => 1 - x (Fin.rev j)) ∈ coordinateChainSet ↔ x ∈ coordinateChainSet := by
  rw [coordinateChainSet_mem, coordinateChainSet_mem]
  change (0 ≤ 1 - x 2 ∧ 1 - x 2 ≤ 1 ∧ 0 ≤ 1 - x 1 ∧
    1 - x 1 ≤ 1 - x 2 ∧ 0 ≤ 1 - x 0 ∧ 1 - x 0 ≤ 1 - x 1) ↔ _
  constructor <;> intro h <;> rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  · exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩

theorem perm_tetrahedron_mem {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N)
    (x : Space) : permPoint π x ∈ tetrahedron (permTet π t) ↔ x ∈ tetrahedron t := by
  rw [tetrahedron_mem_iff, perm_normalizedChain, tetrahedron_mem_iff]

theorem reverse_tetrahedron_mem {N : ℕ} (t : Tet N) (x : Space) :
    reversePoint x ∈ tetrahedron (reverseTet t) ↔ x ∈ tetrahedron t := by
  rw [tetrahedron_mem_iff, tetrahedron_mem_iff]
  have he : normalizedChain (reverseTet t) (reversePoint x) =
      fun j => 1 - normalizedChain t x (Fin.rev j) := by
    funext j
    exact reverse_normalizedChain t x j
  rw [he, coordinateChain_reverse]

theorem perm_cube_mem (π : Equiv.Perm Coordinate) (x : Space) :
    permPoint π x ∈ cube ↔ x ∈ cube := by
  have he : permPoint π x = fun j => x (π.symm j) := funext (permPoint_apply π x)
  rw [he]
  change ((∀ j, 0 ≤ x (π.symm j)) ∧ ∀ j, x (π.symm j) ≤ 1) ↔
    ((∀ j, 0 ≤ x j) ∧ ∀ j, x j ≤ 1)
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> intro j
  · simpa using h0 (π j)
  · simpa using h1 (π j)
  · exact h0 (π.symm j)
  · exact h1 (π.symm j)

theorem reverse_cube_mem (x : Space) : reversePoint x ∈ cube ↔ x ∈ cube := by
  change ((∀ j, 0 ≤ 1 - x j) ∧ ∀ j, 1 - x j ≤ 1) ↔
    ((∀ j, 0 ≤ x j) ∧ ∀ j, x j ≤ 1)
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> intro j
  · linarith [h1 j]
  · linarith [h0 j]
  · linarith [h1 j]
  · linarith [h0 j]

theorem perm_boundary_mem (π : Equiv.Perm Coordinate) (x : Space) :
    permPoint π x ∈ cubeBoundary ↔ x ∈ cubeBoundary := by
  change (permPoint π x ∈ cube ∧ ∃ j, permPoint π x j = 0 ∨ permPoint π x j = 1) ↔
    (x ∈ cube ∧ ∃ j, x j = 0 ∨ x j = 1)
  simp only [permPoint_apply]
  rw [perm_cube_mem]
  constructor
  · rintro ⟨hc, j, hj⟩
    exact ⟨hc, π.symm j, hj⟩
  · rintro ⟨hc, j, hj⟩
    exact ⟨hc, π j, by simpa using hj⟩

theorem reverse_boundary_mem (x : Space) :
    reversePoint x ∈ cubeBoundary ↔ x ∈ cubeBoundary := by
  change (reversePoint x ∈ cube ∧ ∃ j, 1 - x j = 0 ∨ 1 - x j = 1) ↔ _
  rw [reverse_cube_mem]
  have he (j : Coordinate) : (1 - x j = 0 ∨ 1 - x j = 1) ↔ (x j = 0 ∨ x j = 1) := by
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  simp only [he]
  rfl

def pointEquiv (π : Equiv.Perm Coordinate) (flip : Bool) : Space ≃ᵐ Space :=
  if flip then (permPoint π).trans reversePoint else permPoint π

def nodeMap {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (n : GridVertex N) : GridVertex N :=
  if flip then reverseNode (permNode π n) else permNode π n

def tetMap {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (t : Tet N) : Tet N :=
  if flip then reverseTet (permTet π t) else permTet π t

def tetEquiv {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) : Tet N ≃ Tet N :=
  if flip then (permTetEquiv π).trans reverseTetEquiv else permTetEquiv π

theorem tetEquiv_apply {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (t : Tet N) :
    tetEquiv π flip t = tetMap π flip t := by
  cases flip <;> rfl

theorem pointEquiv_apply (π : Equiv.Perm Coordinate) (flip : Bool)
    (x : Space) (j : Coordinate) :
    pointEquiv π flip x j = if flip then 1 - x (π.symm j) else x (π.symm j) := by
  cases flip <;> simp [pointEquiv, permPoint_apply, reversePoint_apply]

theorem pointEquiv_inverse (π : Equiv.Perm Coordinate) (flip : Bool) (x : Space) :
    pointEquiv π.symm flip (pointEquiv π flip x) = x := by
  funext j
  cases flip <;> simp [pointEquiv_apply]

theorem pointEquiv_symm (π : Equiv.Perm Coordinate) (flip : Bool) :
    (pointEquiv π flip).symm = pointEquiv π.symm flip := by
  apply MeasurableEquiv.ext
  funext x
  apply (pointEquiv π flip).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simpa using (pointEquiv_inverse π.symm flip x).symm

theorem pointEquiv_preserving (π : Equiv.Perm Coordinate) (flip : Bool) :
    MeasurePreserving (pointEquiv π flip) := by
  cases flip
  · exact permPoint_preserving π
  · exact reversePoint_preserving.comp (permPoint_preserving π)

theorem nodeMap_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (n : GridVertex N) : nodeMap π.symm flip (nodeMap π flip n) = n := by
  funext j
  cases flip <;> simp [nodeMap, permNode, reverseNode]

theorem perm_reverseTet {N : ℕ} (π : Equiv.Perm Coordinate) (t : Tet N) :
    permTet π (reverseTet t) = reverseTet (permTet π t) := rfl

theorem tetMap_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) (t : Tet N) :
    tetMap π.symm flip (tetMap π flip t) = t := by
  cases flip
  · exact permTet_inverse π t
  · simp only [tetMap, if_true, perm_reverseTet, permTet_inverse]
    exact reverseTet_involutive t

theorem tetEquiv_symm_apply {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (t : Tet N) : (tetEquiv π flip).symm t = tetMap π.symm flip t := by
  apply (tetEquiv π flip).injective
  rw [Equiv.apply_symm_apply, tetEquiv_apply]
  simpa using (tetMap_inverse π.symm flip t).symm

theorem nodeMap_gridPoint {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (flip : Bool) (n : GridVertex N) :
    gridPoint (nodeMap π flip n) = pointEquiv π flip (gridPoint n) := by
  cases flip
  · exact perm_gridPoint π n
  · simp only [nodeMap, pointEquiv, if_true, MeasurableEquiv.trans_apply]
    rw [reverse_gridPoint hN, perm_gridPoint]

theorem tetMap_gridVertex {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (t : Tet N) (a : Vertex) :
    gridVertexOfTet (tetMap π flip t) (transformVertex flip a) =
      nodeMap π flip (gridVertexOfTet t a) := by
  cases flip
  · exact perm_gridVertex π t a
  · simp only [tetMap, nodeMap, transformVertex, if_true]
    rw [reverse_gridVertex, perm_gridVertex]

theorem tetMap_vertex {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (flip : Bool) (t : Tet N) (a : Vertex) :
    vertex (tetMap π flip t) (transformVertex flip a) = pointEquiv π flip (vertex t a) := by
  rw [← gridVertexOfTet_point, tetMap_gridVertex, nodeMap_gridPoint hN,
    gridVertexOfTet_point]

theorem nodeMap_boundaryTag {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (flip : Bool) (n : GridVertex N) :
    boundaryTag (nodeMap π flip n) = transformTags π flip (boundaryTag n) := by
  cases flip
  · exact perm_boundaryTag π n
  · simp only [nodeMap, transformTags, if_true]
    rw [reverse_boundaryTag hN, perm_boundaryTag]

theorem tetMap_mem {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (t : Tet N) (x : Space) :
    pointEquiv π flip x ∈ tetrahedron (tetMap π flip t) ↔ x ∈ tetrahedron t := by
  cases flip
  · exact perm_tetrahedron_mem π t x
  · simp only [pointEquiv, tetMap, if_true, MeasurableEquiv.trans_apply]
    rw [reverse_tetrahedron_mem, perm_tetrahedron_mem]

theorem pointEquiv_cube_mem (π : Equiv.Perm Coordinate) (flip : Bool) (x : Space) :
    pointEquiv π flip x ∈ cube ↔ x ∈ cube := by
  cases flip
  · exact perm_cube_mem π x
  · simp only [pointEquiv, if_true, MeasurableEquiv.trans_apply]
    rw [reverse_cube_mem, perm_cube_mem]

theorem pointEquiv_boundary_mem (π : Equiv.Perm Coordinate) (flip : Bool) (x : Space) :
    pointEquiv π flip x ∈ cubeBoundary ↔ x ∈ cubeBoundary := by
  cases flip
  · exact perm_boundary_mem π x
  · simp only [pointEquiv, if_true, MeasurableEquiv.trans_apply]
    rw [reverse_boundary_mem, perm_boundary_mem]

theorem tetMap_integral {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (t : Tet N) (f : Space → ℝ) :
    (∫ x in tetrahedron (tetMap π flip t), f ((pointEquiv π flip).symm x)) =
      ∫ x in tetrahedron t, f x := by
  have hs : tetrahedron (tetMap π flip t) =
      (pointEquiv π flip).symm ⁻¹' tetrahedron t := by
    ext x
    have hm := tetMap_mem π flip t ((pointEquiv π flip).symm x)
    simpa only [MeasurableEquiv.apply_symm_apply, Set.mem_preimage] using hm
  rw [hs]
  exact (pointEquiv_preserving π flip).symm.setIntegral_preimage_emb
    (pointEquiv π flip).symm.measurableEmbedding f (tetrahedron t)

theorem pullback_integral {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (t : Tet N) (f : Space → ℝ) :
    (∫ x in tetrahedron t, f ((pointEquiv π flip).symm x)) =
      ∫ x in tetrahedron ((tetEquiv π flip).symm t), f x := by
  have hi := tetMap_integral π flip ((tetEquiv π flip).symm t) f
  rwa [← tetEquiv_apply, Equiv.apply_symm_apply] at hi

end FreudenthalSVLean.CubeMeshSymmetry
