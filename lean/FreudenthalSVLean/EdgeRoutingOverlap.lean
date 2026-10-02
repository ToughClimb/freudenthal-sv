import FreudenthalSVLean.EdgeRoutingBox

/-!
# Bounded overlap of the actual edge routing neighborhoods

For manuscript Proposition `edge` and Lemma `routing`, a tetrahedron can
belong to the one-cube face neighborhoods of at most 875 fixed edge boxes.
An injection records the first endpoint's three coordinate offsets in a
five-point interval and the geometric positive edge direction.  The proof
holds for arbitrary meshes and boundary positions, not sampled meshes.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.MacroPatchAdjacency
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.RectangularCubeCluster
open FreudenthalSVLean.EdgeAssemblyGeometry
open FreudenthalSVLean.EdgeRoutingBox

noncomputable section

namespace FreudenthalSVLean.EdgeRoutingOverlap

theorem positiveAdjacent_coordinate_bound {N : ℕ} {c d : Cell N}
    (h : PositiveAdjacent c d) (r : Fin 3) :
    (d r).val ≤ (c r).val + 1 ∧ (c r).val ≤ (d r).val + 1 := by
  obtain ⟨j, hj, ho⟩ := h
  by_cases hr : r = j
  · subst r
    omega
  · rw [ho r hr]
    omega

theorem faceAdjacent_coordinate_bound {N : ℕ} {c d : Cell N}
    (h : FaceAdjacent c d) (r : Fin 3) :
    (d r).val ≤ (c r).val + 1 ∧ (c r).val ≤ (d r).val + 1 := by
  rcases h with h | h
  · exact positiveAdjacent_coordinate_bound h r
  · exact (positiveAdjacent_coordinate_bound h r).symm

theorem near_box_coordinate_bound {N : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (t : Tet N) (ht : nearCluster (cells (edgeBox hN e)) t) (j : Fin 3) :
    (e.val.1 j).val ≤ (t.1 j).val + 2 ∧ (t.1 j).val ≤ (e.val.1 j).val + 2 := by
  obtain ⟨c, hc, ht⟩ := ht
  have hb := (mem_cells (edgeBox hN e) c).mp hc j
  have he := edge_coordinate_step e j
  dsimp [edgeBox] at hb
  rcases ht with ht | ht
  · rw [ht]
    omega
  · have hf := faceAdjacent_coordinate_bound ht j
    omega

def nearBoxEdges {N : ℕ} (hN : 0 < N) (t : Tet N) : Finset (MeshEdge N) := by
  classical
  exact Finset.univ.filter (fun e => nearCluster (cells (edgeBox hN e)) t)

theorem nearBoxEdges_iff {N : ℕ} (hN : 0 < N) (t : Tet N) (e : MeshEdge N) :
    e ∈ nearBoxEdges hN t ↔ nearCluster (cells (edgeBox hN e)) t := by
  classical
  simp [nearBoxEdges]

def offsetIndex {N : ℕ} (hN : 0 < N) (t : Tet N) (e : ↥(nearBoxEdges hN t)) :
    Fin 3 → Fin 5 := fun j =>
  ⟨(e.val.val.1 j).val + 2 - (t.1 j).val, by
    have h := near_box_coordinate_bound hN e.val t ((nearBoxEdges_iff hN t e.val).mp e.property) j
    omega⟩

def overlapIndex {N : ℕ} (hN : 0 < N) (t : Tet N) (e : ↥(nearBoxEdges hN t)) :
    (Fin 3 → Fin 5) × Fin 7 := (offsetIndex hN t e, edgeDirection e.val)

theorem overlapIndex_injective {N : ℕ} (hN : 0 < N) (t : Tet N) :
    Function.Injective (overlapIndex hN t) := by
  intro e f he
  have hd : edgeDirection e.val = edgeDirection f.val := congrArg Prod.snd he
  have hi : offsetIndex hN t e = offsetIndex hN t f := congrArg Prod.fst he
  have ha : e.val.val.1 = f.val.val.1 := by
    funext j
    apply Fin.ext
    have hj := congrArg (fun i : Fin 3 → Fin 5 => (i j).val) hi
    change (e.val.val.1 j).val + 2 - (t.1 j).val =
      (f.val.val.1 j).val + 2 - (t.1 j).val at hj
    have hE := near_box_coordinate_bound hN e.val t ((nearBoxEdges_iff hN t e.val).mp e.property) j
    have hF := near_box_coordinate_bound hN f.val t ((nearBoxEdges_iff hN t f.val).mp f.property) j
    omega
  exact Subtype.ext (first_endpoint_determines_edge e.val f.val ha hd)

/-- The overlap constant precedes every mesh size and tetrahedron. -/
theorem nearBoxEdges_card {N : ℕ} (hN : 0 < N) (t : Tet N) :
    (nearBoxEdges hN t).card ≤ 875 := by
  classical
  have hc := Fintype.card_le_of_injective (overlapIndex hN t) (overlapIndex_injective hN t)
  norm_num only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hc
  exact hc

end FreudenthalSVLean.EdgeRoutingOverlap
