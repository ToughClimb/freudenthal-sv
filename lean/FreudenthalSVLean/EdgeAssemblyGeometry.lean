import FreudenthalSVLean.UniformEdgeLift

/-!
# Mesh-independent incidence and overlap for global edge assembly

For the manuscript's global edge stage and bounded-overlap estimate,
mesh edges are stored once, oriented increasingly along the chain.
Actual edge incidences are in explicit bijection with a tetrahedron and
one of its six local edges.  A field supported in its endpoint stars can
contribute to a fixed tetrahedron for at most fifty-six mesh edges:
four vertices, two endpoint roles, and seven positive directions.
All bounds are proved for the actual arbitrary-size mesh.
-/

open scoped BigOperators Classical
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalPressureLift

noncomputable section

namespace FreudenthalSVLean.EdgeAssemblyGeometry

abbrev MeshEdge (N : ℕ) := {ab : GridVertex N × GridVertex N //
  ab.1 ≠ ab.2 ∧ (∀ j, (ab.1 j).val ≤ (ab.2 j).val) ∧ Nonempty (ActualEdgeStar ab.1 ab.2)}

abbrev LocalEdge := {lm : Vertex × Vertex // lm.1.val < lm.2.val}

theorem local_edge_count : Fintype.card LocalEdge = 6 := by decide +kernel

def edgeDirection {N : ℕ} (e : MeshEdge N) : Fin 7 :=
  Classical.choose (increasing_edge_direction e.val.1 e.val.2 e.property.1
    e.property.2.1 (Classical.choice e.property.2.2))

theorem edgeDirection_eq {N : ℕ} (e : MeshEdge N) :
    displacement e.val.1 e.val.2 = positiveDirection (edgeDirection e) :=
  Classical.choose_spec (increasing_edge_direction e.val.1 e.val.2 e.property.1
    e.property.2.1 (Classical.choice e.property.2.2))

def localMeshEdge {N : ℕ} (t : Tet N) (lm : LocalEdge) : MeshEdge N :=
  ⟨(gridVertexOfTet t lm.val.1, gridVertexOfTet t lm.val.2),
    (gridVertexOfTet_injective t).ne (fun h => lm.property.ne (congrArg Fin.val h)),
    gridVertexOfTet_mono t lm.val.1 lm.val.2 lm.property.le,
    ⟨⟨(⟨(t, lm.val.1), rfl⟩, lm.val.2), rfl⟩⟩⟩

def localIncidence {N : ℕ} (t : Tet N) (lm : LocalEdge) :
    ActualEdgeStar (localMeshEdge t lm).val.1 (localMeshEdge t lm).val.2 :=
  ⟨(⟨(t, lm.val.1), rfl⟩, lm.val.2), rfl⟩

theorem incidence_indices_ordered {N : ℕ} (e : MeshEdge N)
    (x : ActualEdgeStar e.val.1 e.val.2) : x.val.1.val.2.val < x.val.2.val := by
  by_contra h
  have hm := gridVertexOfTet_mono x.val.1.val.1 x.val.2 x.val.1.val.2 (by omega)
  apply e.property.1
  funext j
  apply Fin.ext
  have hj := hm j
  rw [x.val.1.property, x.property] at hj
  exact Nat.le_antisymm (e.property.2.1 j) hj

def incidenceLocalEdge {N : ℕ} (e : MeshEdge N) (x : ActualEdgeStar e.val.1 e.val.2) : LocalEdge :=
  ⟨(x.val.1.val.2, x.val.2), incidence_indices_ordered e x⟩

def allEdgeIncidencesEquiv (N : ℕ) :
    (Σ e : MeshEdge N, ActualEdgeStar e.val.1 e.val.2) ≃ Tet N × LocalEdge where
  toFun p := (p.2.val.1.val.1, incidenceLocalEdge p.1 p.2)
  invFun p := ⟨localMeshEdge p.1 p.2, localIncidence p.1 p.2⟩
  left_inv p := by
    rcases p with ⟨⟨⟨a, b⟩, hab, horder, hne⟩, ⟨⟨⟨⟨t, l⟩, ha⟩, m⟩, hb⟩⟩
    change gridVertexOfTet t l = a at ha
    change gridVertexOfTet t m = b at hb
    subst a
    subst b
    rfl
  right_inv p := rfl

theorem edge_incidence_sum (N : ℕ) (f : Tet N → ℝ) :
    (∑ e : MeshEdge N, ∑ x : ActualEdgeStar e.val.1 e.val.2, f x.val.1.val.1) =
      6 * ∑ t : Tet N, f t := by
  calc
    _ = ∑ p : (Σ e : MeshEdge N, ActualEdgeStar e.val.1 e.val.2), f p.2.val.1.val.1 :=
      (Fintype.sum_sigma _).symm
    _ = ∑ p : Tet N × LocalEdge, f p.1 :=
      Equiv.sum_comp (allEdgeIncidencesEquiv N) (fun p : Tet N × LocalEdge => f p.1)
    _ = ∑ t : Tet N, ∑ _ : LocalEdge, f t := Fintype.sum_prod_type _
    _ = _ := by simp [local_edge_count, Finset.mul_sum]

theorem edge_star_energy_sum {N : ℕ} (q : BrokenPressure N) :
    (∑ e : MeshEdge N, starPressureEnergy e.val.1 e.val.2 q) = 6 * pressureEnergy q :=
  edge_incidence_sum N (fun t => ∫ y in tetrahedron t, (eval y (q t)) ^ 2)

theorem first_endpoint_determines_edge {N : ℕ} (e f : MeshEdge N)
    (ha : e.val.1 = f.val.1) (hd : edgeDirection e = edgeDirection f) : e = f := by
  apply Subtype.ext
  apply Prod.ext ha
  apply displacement_injective e.val.1
  rw [edgeDirection_eq, ha, edgeDirection_eq, hd]

theorem second_endpoint_determines_edge {N : ℕ} (e f : MeshEdge N)
    (hb : e.val.2 = f.val.2) (hd : edgeDirection e = edgeDirection f) : e = f := by
  have he : displacement e.val.1 e.val.2 = displacement f.val.1 f.val.2 := by
    rw [edgeDirection_eq, edgeDirection_eq, hd]
  apply Subtype.ext
  apply Prod.ext _ hb
  funext j
  apply Fin.ext
  have hj := congrFun he j
  rw [hb] at hj
  change ((f.val.2 j).val : ℤ) - ((e.val.1 j).val : ℤ) =
    ((f.val.2 j).val : ℤ) - ((f.val.1 j).val : ℤ) at hj
  omega

def nearTet {N : ℕ} (t : Tet N) : Finset (MeshEdge N) :=
  Finset.univ.filter (fun e => ∃ l : Vertex,
    gridVertexOfTet t l = e.val.1 ∨ gridVertexOfTet t l = e.val.2)

theorem nearTet_iff {N : ℕ} (t : Tet N) (e : MeshEdge N) : e ∈ nearTet t ↔
    ∃ l : Vertex, gridVertexOfTet t l = e.val.1 ∨ gridVertexOfTet t l = e.val.2 := by
  simp [nearTet]

def nearVertex {N : ℕ} (t : Tet N) (e : ↥(nearTet t)) : Vertex :=
  Classical.choose ((nearTet_iff t e.val).mp e.property)

def nearSide {N : ℕ} (t : Tet N) (e : ↥(nearTet t)) : Bool :=
  if gridVertexOfTet t (nearVertex t e) = e.val.val.1 then false else true

theorem nearNode {N : ℕ} (t : Tet N) (e : ↥(nearTet t)) :
    gridVertexOfTet t (nearVertex t e) = if nearSide t e then e.val.val.2 else e.val.val.1 := by
  have he := Classical.choose_spec ((nearTet_iff t e.val).mp e.property)
  change gridVertexOfTet t (nearVertex t e) = e.val.val.1 ∨
    gridVertexOfTet t (nearVertex t e) = e.val.val.2 at he
  by_cases h : gridVertexOfTet t (nearVertex t e) = e.val.val.1
  · simpa only [nearSide, if_pos h, Bool.false_eq_true, if_false] using h
  · simpa only [nearSide, if_neg h, if_true] using he.resolve_left h

def nearIndex {N : ℕ} (t : Tet N) (e : ↥(nearTet t)) : Vertex × Bool × Fin 7 :=
  (nearVertex t e, nearSide t e, edgeDirection e.val)

theorem nearIndex_injective {N : ℕ} (t : Tet N) : Function.Injective (nearIndex t) := by
  intro e f h
  have hl : nearVertex t e = nearVertex t f := congrArg Prod.fst h
  have hs : nearSide t e = nearSide t f := congrArg (fun p : Vertex × Bool × Fin 7 => p.2.1) h
  have hd : edgeDirection e.val = edgeDirection f.val :=
    congrArg (fun p : Vertex × Bool × Fin 7 => p.2.2) h
  have he := nearNode t e
  have hf := nearNode t f
  rw [hl, hs] at he
  apply Subtype.ext
  cases hside : nearSide t f
  · rw [hside] at he hf
    exact first_endpoint_determines_edge e.val f.val (he.symm.trans hf) hd
  · rw [hside] at he hf
    exact second_endpoint_determines_edge e.val f.val (he.symm.trans hf) hd

theorem nearTet_card {N : ℕ} (t : Tet N) : (nearTet t).card ≤ 56 := by
  have hc := Fintype.card_le_of_injective (nearIndex t) (nearIndex_injective t)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using hc

theorem meshEdge_pair_injective {N : ℕ} (e f : MeshEdge N)
    (he : ({e.val.1, e.val.2} : Finset (GridVertex N)) = {f.val.1, f.val.2}) : e = f := by
  have hs : ({e.val.1, e.val.2} : Set (GridVertex N)) = {f.val.1, f.val.2} := by
    simpa only [Finset.coe_pair] using
      congrArg (fun s : Finset (GridVertex N) => (s : Set (GridVertex N))) he
  rcases Set.pair_eq_pair_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Subtype.ext (Prod.ext ha hb)
  · exfalso
    apply e.property.1
    funext j
    apply Fin.ext
    have hr := f.property.2.1 j
    rw [← hb, ← ha] at hr
    exact Nat.le_antisymm (e.property.2.1 j) hr

end FreudenthalSVLean.EdgeAssemblyGeometry
