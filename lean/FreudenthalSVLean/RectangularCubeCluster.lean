import FreudenthalSVLean.CubeClusterGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Arbitrary-mesh face connectivity of rectangular cube clusters

For manuscript Lemma `routing`, fixed rectangular cube clusters are
face-connected: a path changes one coordinate at a time through the
integer interval in that coordinate.  This is a genuine arbitrary-`N`
geometric theorem, independent of mean data and of finite enumeration.
-/

open SimpleGraph
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MacroPatchAdjacency
open FreudenthalSVLean.CubeClusterGraph

noncomputable section

namespace FreudenthalSVLean.RectangularCubeCluster

structure Box (N : ℕ) where
  lower : Coordinate → ℕ
  upper : Coordinate → ℕ
  valid : ∀ j, lower j ≤ upper j ∧ upper j < N

def cells {N : ℕ} (B : Box N) : Finset (Cell N) := by
  classical
  exact Finset.univ.filter (fun c => ∀ j, B.lower j ≤ (c j).val ∧ (c j).val ≤ B.upper j)

theorem mem_cells {N : ℕ} (B : Box N) (c : Cell N) :
    c ∈ cells B ↔ ∀ j, B.lower j ≤ (c j).val ∧ (c j).val ≤ B.upper j := by
  classical
  simp [cells]

def width {N : ℕ} (B : Box N) (j : Coordinate) : ℕ := B.upper j - B.lower j + 1

theorem width_pos {N : ℕ} (B : Box N) (j : Coordinate) : 0 < width B j := by
  unfold width
  omega

def lowerCell {N : ℕ} (B : Box N) : ClusterCell (cells B) :=
  ⟨fun j => ⟨B.lower j, (B.valid j).1.trans_lt (B.valid j).2⟩,
    (mem_cells B _).mpr (fun j => ⟨le_rfl, (B.valid j).1⟩)⟩

def linePoint {N : ℕ} (B : Box N) (c : ClusterCell (cells B)) (j : Coordinate)
    (i : Fin (width B j)) : ClusterCell (cells B) :=
  ⟨Function.update c.val j ⟨B.lower j + i.val, by
    have hi := i.isLt
    have hj := B.valid j
    dsimp [width] at hi
    omega⟩, by
    rw [mem_cells]
    intro r
    by_cases hr : r = j
    · subst r
      simp only [Function.update_self]
      have hi := i.isLt
      have hj := B.valid j
      dsimp [width] at hi
      omega
    · simpa only [Function.update_of_ne hr] using (mem_cells B c.val).mp c.property r⟩

def lineHom {N : ℕ} (B : Box N) (c : ClusterCell (cells B)) (j : Coordinate) :
    pathGraph (width B j) →g cubeGraph (cells B) where
  toFun := linePoint B c j
  map_rel' {i k} h := by
    rcases pathGraph_adj.mp h with h | h
    · left
      refine ⟨j, ?_, ?_⟩
      · change (Function.update c.val j _ j).val = (Function.update c.val j _ j).val + 1
        simp only [Function.update_self]
        omega
      · intro r hr
        simp only [linePoint, Function.update_of_ne hr]
    · right
      refine ⟨j, ?_, ?_⟩
      · change (Function.update c.val j _ j).val = (Function.update c.val j _ j).val + 1
        simp only [Function.update_self]
        omega
      · intro r hr
        simp only [linePoint, Function.update_of_ne hr]

def coordinateIndex {N : ℕ} (B : Box N) (c : ClusterCell (cells B)) (j : Coordinate) :
    Fin (width B j) :=
  ⟨(c.val j).val - B.lower j, by
    have hc := (mem_cells B c.val).mp c.property j
    dsimp [width]
    omega⟩

theorem linePoint_self {N : ℕ} (B : Box N) (c : ClusterCell (cells B)) (j : Coordinate) :
    linePoint B c j (coordinateIndex B c j) = c := by
  apply Subtype.ext
  funext r
  by_cases hr : r = j
  · subst r
    apply Fin.ext
    simp only [linePoint, coordinateIndex, Function.update_self]
    have hc := (mem_cells B c.val).mp c.property j
    omega
  · simp [linePoint, hr]

/-- Elements differing in just one coordinate are joined by the integer
coordinate interval; every intermediate cube stays in the rectangle. -/
theorem coordinate_reachable {N : ℕ} (B : Box N) (c d : ClusterCell (cells B))
    (j : Coordinate) (h : ∀ r, r ≠ j → c.val r = d.val r) :
    (cubeGraph (cells B)).Reachable c d := by
  have hr := (pathGraph_preconnected (width B j)
    (coordinateIndex B c j) (coordinateIndex B d j)).map (lineHom B c j)
  have hd : linePoint B c j (coordinateIndex B d j) = d := by
    apply Subtype.ext
    funext r
    by_cases hj : r = j
    · subst r
      apply Fin.ext
      simp only [linePoint, coordinateIndex, Function.update_self]
      have hb := (mem_cells B d.val).mp d.property j
      omega
    · simpa only [linePoint, Function.update_of_ne hj] using h r hj
  change (cubeGraph (cells B)).Reachable (linePoint B c j (coordinateIndex B c j))
    (linePoint B c j (coordinateIndex B d j)) at hr
  rwa [linePoint_self, hd] at hr

def mixedCell {N : ℕ} (B : Box N) (c d : ClusterCell (cells B)) (s : Finset Coordinate) :
    ClusterCell (cells B) :=
  ⟨fun j => if j ∈ s then d.val j else c.val j, by
    rw [mem_cells]
    intro j
    split_ifs
    · exact (mem_cells B d.val).mp d.property j
    · exact (mem_cells B c.val).mp c.property j⟩

theorem mixed_reachable {N : ℕ} (B : Box N) (c d : ClusterCell (cells B))
    (s : Finset Coordinate) : (cubeGraph (cells B)).Reachable c (mixedCell B c d s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : mixedCell B c d ∅ = c := by ext j; simp [mixedCell]
    rw [he]
  | @insert j s hj ih =>
    apply ih.trans
    apply coordinate_reachable B _ _ j
    intro r hr
    simp [mixedCell, hr]

/-- Every nonempty rectangular cluster is face-connected on every
positive mesh size for which its bounds fit. -/
theorem cubeGraph_connected {N : ℕ} (B : Box N) : (cubeGraph (cells B)).Connected := by
  let : Nonempty (ClusterCell (cells B)) := ⟨lowerCell B⟩
  refine ⟨?_⟩
  intro c d
  have he : mixedCell B c d Finset.univ = d := by ext j; simp [mixedCell]
  simpa only [he] using mixed_reachable B c d Finset.univ

def boxIndex {N : ℕ} (B : Box N) (c : ClusterCell (cells B)) :
    (j : Coordinate) → Fin (width B j) := fun j => coordinateIndex B c j

theorem boxIndex_injective {N : ℕ} (B : Box N) : Function.Injective (boxIndex B) := by
  intro c d he
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hj := congrArg (fun i => (i j).val) he
  change (c.val j).val - B.lower j = (d.val j).val - B.lower j at hj
  have hc := (mem_cells B c.val).mp c.property j
  have hd := (mem_cells B d.val).mp d.property j
  omega

/-- An exact geometric size bound from coordinate interval widths. -/
theorem cells_card_bound {N : ℕ} (B : Box N) :
    (cells B).card ≤ ∏ j : Coordinate, width B j := by
  classical
  have h := Fintype.card_le_of_injective (boxIndex B) (boxIndex_injective B)
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using h

theorem cells_card_le_cube {N : ℕ} (B : Box N) (L : ℕ) (hL : ∀ j, width B j ≤ L) :
    (cells B).card ≤ L ^ 3 := by
  calc
    _ ≤ ∏ j : Coordinate, width B j := cells_card_bound B
    _ ≤ ∏ _j : Coordinate, L := Finset.prod_le_prod' (fun j _ => hL j)
    _ = L ^ 3 := by simp

end FreudenthalSVLean.RectangularCubeCluster
