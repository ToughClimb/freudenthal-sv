import FreudenthalSVLean.RectangularCubeCluster
import FreudenthalSVLean.EdgeAssemblyGeometry

/-!
# Fixed bounded routing boxes for every actual edge

For manuscript Lemma `routing` in the proof of Proposition `edge`, each
increasing mesh edge fixes a rectangular cube cluster containing both
endpoint stars.  Each coordinate interval has at most three cells, hence
the cluster has at most 27 cubes and 162 tetrahedra.  Face connectivity is
proved geometrically, with no dependence on the pressure input.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.EdgeAssemblyGeometry
open FreudenthalSVLean.CubeClusterGraph
open FreudenthalSVLean.RectangularCubeCluster

noncomputable section

namespace FreudenthalSVLean.EdgeRoutingBox

/-- Every coordinate increment of an actual increasing mesh edge is zero
or one, as a consequence of its two vertices belonging to one chain. -/
theorem edge_coordinate_step {N : ℕ} (e : MeshEdge N) (j : Coordinate) :
    (e.val.2 j).val ≤ (e.val.1 j).val + 1 := by
  let x : ActualEdgeStar e.val.1 e.val.2 := Classical.choice e.property.2.2
  have ha := congrArg (fun n : GridVertex N => (n j).val) x.val.1.property
  have hb := congrArg (fun n : GridVertex N => (n j).val) x.property
  change (x.val.1.val.1.1 j).val + prefixMask (x.val.1.val.1.2, x.val.1.val.2) j =
    (e.val.1 j).val at ha
  change (x.val.1.val.1.1 j).val + prefixMask (x.val.1.val.1.2, x.val.2) j =
    (e.val.2 j).val at hb
  have hp := prefix_le_one (x.val.1.val.1.2, x.val.2) j
  omega

def edgeBox {N : ℕ} (hN : 0 < N) (e : MeshEdge N) : Box N where
  lower j := (e.val.1 j).val - 1
  upper j := min (N - 1) (e.val.2 j).val
  valid j := by
    have ha := (e.val.1 j).isLt
    have hb := (e.val.2 j).isLt
    have hm := e.property.2.1 j
    constructor <;> omega

theorem edgeBox_width {N : ℕ} (hN : 0 < N) (e : MeshEdge N) (j : Coordinate) :
    width (edgeBox hN e) j ≤ 3 := by
  have he := edge_coordinate_step e j
  dsimp [width, edgeBox]
  omega

theorem edgeBox_card {N : ℕ} (hN : 0 < N) (e : MeshEdge N) :
    (cells (edgeBox hN e)).card ≤ 27 :=
  cells_card_le_cube (edgeBox hN e) 3 (edgeBox_width hN e)

theorem edgeBox_tet_card {N : ℕ} (hN : 0 < N) (e : MeshEdge N) :
    Fintype.card (ClusterTet (cells (edgeBox hN e))) ≤ 162 := by
  rw [clusterTet_card]
  have h := edgeBox_card hN e
  omega

theorem first_endpoint_star_in_box {N : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (t : Tet N) (a : Fin 4) (ha : gridVertexOfTet t a = e.val.1) :
    t.1 ∈ cells (edgeBox hN e) := by
  rw [mem_cells]
  intro j
  have hv := congrArg (fun n : GridVertex N => (n j).val) ha
  change (t.1 j).val + prefixMask (t.2, a) j = (e.val.1 j).val at hv
  have hp := prefix_le_one (t.2, a) j
  have ht := (t.1 j).isLt
  have hm := e.property.2.1 j
  dsimp [edgeBox]
  omega

theorem second_endpoint_star_in_box {N : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (t : Tet N) (a : Fin 4) (ha : gridVertexOfTet t a = e.val.2) :
    t.1 ∈ cells (edgeBox hN e) := by
  rw [mem_cells]
  intro j
  have hv := congrArg (fun n : GridVertex N => (n j).val) ha
  change (t.1 j).val + prefixMask (t.2, a) j = (e.val.2 j).val at hv
  have hp := prefix_le_one (t.2, a) j
  have ht := (t.1 j).isLt
  have hm := e.property.2.1 j
  dsimp [edgeBox]
  omega

theorem off_box_has_no_endpoints {N : ℕ} (hN : 0 < N) (e : MeshEdge N)
    (t : Tet N) (ht : t.1 ∉ cells (edgeBox hN e)) :
    (∀ a : Fin 4, gridVertexOfTet t a ≠ e.val.1) ∧
      (∀ a : Fin 4, gridVertexOfTet t a ≠ e.val.2) := by
  constructor
  · intro a ha
    exact ht (first_endpoint_star_in_box hN e t a ha)
  · intro a ha
    exact ht (second_endpoint_star_in_box hN e t a ha)

/-- The routing connectivity hypothesis is discharged for every edge by
the fixed box geometry, not supplied by a certificate or chosen input. -/
theorem edgeBox_connected {N : ℕ} (hN : 0 < N) (e : MeshEdge N) :
    (cubeGraph (cells (edgeBox hN e))).Connected :=
  RectangularCubeCluster.cubeGraph_connected (edgeBox hN e)

end FreudenthalSVLean.EdgeRoutingBox
