import FreudenthalSVLean.FreudenthalMesh
import FreudenthalSVLean.GridNodalSupport

/-!
# Exact arbitrary-mesh vertex-star parameterization

For manuscript Lemma `vertex-coverage`, every actual vertex incidence is
encoded by a coordinate permutation and a position along its four-vertex
chain.  The incident cube origin is the grid node minus that permutation's
prefix indicator.  The admissibility inequalities state exactly that this
origin is a cell of the mesh.  They include lower boundary, upper boundary,
and interior nodes for every positive `N`, including `N=1,2`.

The equivalence below proves coverage by a universal set of twenty-four
states and a mesh-independent valence bound.  Reduction to six symmetry
classes, adjacency connectivity, and face-transfer support are separate
theorems and are not inferred from this parameterization alone.
-/

open scoped BigOperators Classical
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.VertexStarCoverage

abbrev GridVertex (N : ℕ) := Coordinate → Fin (N + 1)
abbrev State := Equiv.Perm Coordinate × Vertex

def prefixMask (s : State) (j : Coordinate) : ℕ :=
  if (s.1.symm j).val < s.2.val then 1 else 0

theorem prefix_le_one (s : State) (j : Coordinate) : prefixMask s j ≤ 1 := by
  unfold prefixMask
  split_ifs <;> omega

theorem state_count : Fintype.card State = 24 := by
  simp [State, Fintype.card_perm]
  norm_num

theorem prefix_sum (s : State) : (∑ j : Coordinate, prefixMask s j) = s.2.val := by
  rcases s with ⟨σ, a⟩
  rw [← Equiv.sum_comp σ]
  simp only [prefixMask, Equiv.symm_apply_apply]
  fin_cases a <;> simp only [Fin.sum_univ_three] <;> norm_num

def gridVertexOfTet {N : ℕ} (t : Tet N) (a : Vertex) : GridVertex N :=
  fun j => ⟨(t.1 j).val + prefixMask (t.2, a) j, by
    have ht := (t.1 j).isLt
    have hp := prefix_le_one (t.2, a) j
    omega⟩

def gridPoint {N : ℕ} (n : GridVertex N) : Space :=
  meshScale N • (fun j => ((n j).val : ℝ))

theorem gridVertexOfTet_point {N : ℕ} (t : Tet N) (a : Vertex) :
    gridPoint (gridVertexOfTet t a) = vertex t a := by
  funext j
  simp [gridPoint, gridVertexOfTet, vertex, scaledVertex, chainVertex,
    cellOrigin, prefixMask, Pi.smul_apply, smul_eq_mul]

theorem gridPoint_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (gridPoint (N := N)) := by
  intro n m he
  funext j
  apply Fin.ext
  have hv := congrArg (fun x : Space => x j) he
  change meshScale N * ((n j).val : ℝ) = meshScale N * ((m j).val : ℝ) at hv
  have hn := mul_left_cancel₀ (meshScale_pos N hN).ne' hv
  exact_mod_cast hn

theorem gridVertexOfTet_injective {N : ℕ} (t : Tet N) :
    Function.Injective (gridVertexOfTet t) := by
  intro a b he
  have hp : prefixMask (t.2, a) = prefixMask (t.2, b) := by
    funext j
    have hv := congrArg (fun n : GridVertex N => (n j).val) he
    change (t.1 j).val + prefixMask (t.2, a) j = (t.1 j).val + prefixMask (t.2, b) j at hv
    omega
  have hv := congrArg (fun f : Coordinate → ℕ => ∑ j : Coordinate, f j) hp
  rw [prefix_sum, prefix_sum] at hv
  exact Fin.ext hv

def admissible {N : ℕ} (n : GridVertex N) (s : State) : Prop :=
  ∀ j : Coordinate, prefixMask s j ≤ (n j).val ∧ (n j).val - prefixMask s j < N

/-- Lower, interior, and upper coordinates are encoded by `0,1,2`. -/
def boundaryTag {N : ℕ} (n : GridVertex N) (j : Coordinate) : Fin 3 :=
  if (n j).val = 0 then 0 else if (n j).val = N then 2 else 1

def tagAdmissible (b : Coordinate → Fin 3) (s : State) : Prop :=
  ∀ j : Coordinate, (b j = 0 → prefixMask s j = 0) ∧
    (b j = 2 → prefixMask s j = 1)

theorem boundaryTag_zero_iff {N : ℕ} (n : GridVertex N) (j : Coordinate) :
    boundaryTag n j = 0 ↔ (n j).val = 0 := by
  unfold boundaryTag
  split_ifs with hz hu
  · exact iff_of_true rfl hz
  · exact iff_of_false (by decide) hz
  · exact iff_of_false (by decide) hz

theorem boundaryTag_upper_iff {N : ℕ} (hN : 0 < N) (n : GridVertex N) (j : Coordinate) :
    boundaryTag n j = 2 ↔ (n j).val = N := by
  unfold boundaryTag
  by_cases hz : (n j).val = 0
  · rw [if_pos hz]
    have hn : (n j).val ≠ N := by omega
    exact iff_of_false (by decide) hn
  · rw [if_neg hz]
    split_ifs with hu
    · exact iff_of_true rfl hu
    · exact iff_of_false (by decide) hu

/-- All dependence on the mesh size is reduced exactly to three boundary
tags; this is the infinite-mesh implication for the finite state model. -/
theorem admissible_iff_boundaryTags {N : ℕ} (hN : 0 < N) (n : GridVertex N) (s : State) :
    admissible n s ↔ tagAdmissible (boundaryTag n) s := by
  constructor
  · intro ha j
    have hp := prefix_le_one s j
    have hj := ha j
    constructor
    · intro hb
      have hn := (boundaryTag_zero_iff n j).mp hb
      omega
    · intro hb
      have hn := (boundaryTag_upper_iff hN n j).mp hb
      omega
  · intro hb j
    have hp := prefix_le_one s j
    have hn := (n j).isLt
    by_cases hz : (n j).val = 0
    · have hm := (hb j).1 ((boundaryTag_zero_iff n j).mpr hz)
      omega
    · by_cases hu : (n j).val = N
      · have hm := (hb j).2 ((boundaryTag_upper_iff hN n j).mpr hu)
        omega
      · omega

abbrev VertexStar {N : ℕ} (n : GridVertex N) :=
  {ta : Tet N × Vertex // gridVertexOfTet ta.1 ta.2 = n}

theorem star_cell_equation {N : ℕ} (n : GridVertex N) (ta : VertexStar n)
    (j : Coordinate) :
    (n j).val = (ta.val.1.1 j).val + prefixMask (ta.val.1.2, ta.val.2) j := by
  have he := congrArg (fun n : GridVertex N => (n j).val) ta.property
  exact he.symm

theorem star_state_admissible {N : ℕ} (n : GridVertex N) (ta : VertexStar n) :
    admissible n (ta.val.1.2, ta.val.2) := by
  intro j
  rw [star_cell_equation n ta j]
  exact ⟨Nat.le_add_left _ _, by simp⟩

def stateTet {N : ℕ} (n : GridVertex N) (s : State) (hs : admissible n s) : Tet N :=
  (fun j => ⟨(n j).val - prefixMask s j, (hs j).2⟩, s.1)

theorem stateTet_vertex {N : ℕ} (n : GridVertex N) (s : State) (hs : admissible n s) :
    gridVertexOfTet (stateTet n s hs) s.2 = n := by
  funext j
  apply Fin.ext
  exact Nat.sub_add_cancel (hs j).1

/-- Exact finite-to-global parameterization: the mesh star and admissible
universal states are mutually inverse, with the cube recovered explicitly. -/
def starStateEquiv {N : ℕ} (n : GridVertex N) :
    VertexStar n ≃ {s : State // admissible n s} where
  toFun ta := ⟨(ta.val.1.2, ta.val.2), star_state_admissible n ta⟩
  invFun s := ⟨(stateTet n s.val s.property, s.val.2), stateTet_vertex n s.val s.property⟩
  left_inv ta := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · funext j
        apply Fin.ext
        change (n j).val - prefixMask (ta.val.1.2, ta.val.2) j = (ta.val.1.1 j).val
        rw [star_cell_equation n ta j]
        omega
      · rfl
    · rfl
  right_inv s := Subtype.ext rfl

theorem geometric_incidence_iff {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (t : Tet N) (a : Vertex) : vertex t a = gridPoint n ↔ gridVertexOfTet t a = n := by
  rw [← gridVertexOfTet_point]
  exact (gridPoint_injective hN).eq_iff

/-- The universal-state parameterization applies to actual geometric
vertices, not just to integer labels detached from the mesh geometry. -/
def geometricStarEquivState {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    {ta : Tet N × Vertex // vertex ta.1 ta.2 = gridPoint n} ≃
      {s : State // admissible n s} :=
  (Equiv.subtypeEquivRight (fun ta : Tet N × Vertex => geometric_incidence_iff hN n ta.1 ta.2)).trans
    (starStateEquiv n)

/-- Every interior and boundary vertex has at most twenty-four incident
tetrahedra, uniformly in the mesh size. -/
theorem geometric_star_valence_bound {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    Fintype.card {ta : Tet N × Vertex // vertex ta.1 ta.2 = gridPoint n} ≤ 24 := by
  calc
    _ = Fintype.card {s : State // admissible n s} := Fintype.card_congr (geometricStarEquivState hN n)
    _ ≤ Fintype.card State := Fintype.card_subtype_le _
    _ = 24 := state_count

end FreudenthalSVLean.VertexStarCoverage
