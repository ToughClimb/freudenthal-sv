import FreudenthalSVLean.LocalVolumeInterpolation
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Uniform overlap of actual interpolation neighborhoods

For the bounded-overlap assembly in manuscript Lemma `means` and
equation `SZ`, the radius-2h box centered at the fixed anchor of an
element is an actual Cartesian box.  If it contains a point x, its
cell origin has each integer coordinate in a six-point interval around
floor(x/h).  The three offsets and coordinate permutation determine the
tetrahedron injectively.  Thus at most 6^3 times 6 = 1296 neighborhoods
contain any point, uniformly for every positive N and every boundary
position.  The volume-integral implication is proved from actual
indicators, rather than inferred from a sampled-mesh count.
-/

open scoped BigOperators Topology Classical
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshAveragingBoxes
open FreudenthalSVLean.LocalVolumeInterpolation

noncomputable section

namespace FreudenthalSVLean.InterpolationBoxOverlap

set_option backward.isDefEq.respectTransparency false

def coordinateFloor (N : ℕ) (x : Space) (j : Fin 3) : ℤ :=
  Int.floor ((meshScale N)⁻¹ * x j)

theorem containing_box_cell_bounds {N : ℕ} (hN : 0 < N) (x : Space) (t : Tet N)
    (hx : x ∈ elementBox t (boxAnchor t)) (j : Fin 3) :
    coordinateFloor N x j - 3 ≤ ((t.1 j).val : ℤ) ∧
      ((t.1 j).val : ℤ) ≤ coordinateFloor N x j + 2 := by
  have hh := meshScale_pos N hN
  have hv := vertex_coordinate_bounds hN t (boxAnchor t) j
  have hl := hx.1 j
  have hu := hx.2 j
  change -2 * meshScale N + VertexStarCoverage.gridPoint
    (VertexStarCoverage.gridVertexOfTet t (boxAnchor t)) j ≤ x j at hl
  change x j ≤ 2 * meshScale N + VertexStarCoverage.gridPoint
    (VertexStarCoverage.gridVertexOfTet t (boxAnchor t)) j at hu
  have hpl : meshScale N * (((t.1 j).val : ℝ) - 2) ≤ x j := by
    have hvl := hv.1
    change meshScale N * ((t.1 j).val : ℝ) ≤ _ at hvl
    linarith
  have hpu : x j ≤ meshScale N * (((t.1 j).val : ℝ) + 3) := by
    have hvu := hv.2
    change VertexStarCoverage.gridPoint (VertexStarCoverage.gridVertexOfTet t (boxAnchor t)) j ≤
      meshScale N * ((t.1 j).val : ℝ) + meshScale N at hvu
    linarith
  have hsl := mul_le_mul_of_nonneg_left hpl (inv_nonneg.mpr hh.le)
  have hsu := mul_le_mul_of_nonneg_left hpu (inv_nonneg.mpr hh.le)
  simp only [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul] at hsl hsu
  have hf := Int.floor_le ((meshScale N)⁻¹ * x j)
  have hfu := Int.lt_floor_add_one ((meshScale N)⁻¹ * x j)
  have hLo : (coordinateFloor N x j : ℝ) - 3 ≤ ((t.1 j).val : ℝ) := by
    dsimp only [coordinateFloor]
    linarith
  have hUp : ((t.1 j).val : ℝ) < (coordinateFloor N x j : ℝ) + 3 := by
    dsimp only [coordinateFloor]
    linarith
  have hLi : coordinateFloor N x j - 3 ≤ ((t.1 j).val : ℤ) := by exact_mod_cast hLo
  have hUi : ((t.1 j).val : ℤ) < coordinateFloor N x j + 3 := by exact_mod_cast hUp
  exact ⟨hLi, by omega⟩

def containingElements (N : ℕ) (x : Space) : Finset (Tet N) :=
  Finset.univ.filter (fun t => x ∈ elementBox t (boxAnchor t))

theorem containingElements_mem {N : ℕ} (x : Space) (t : Tet N) :
    t ∈ containingElements N x ↔ x ∈ elementBox t (boxAnchor t) := by
  simp only [containingElements, Finset.mem_filter, Finset.mem_univ, true_and]

def boxOffsets {N : ℕ} (hN : 0 < N) (x : Space) (t : ↥(containingElements N x)) :
    Fin 3 → Fin 6 := fun j =>
  ⟨Int.toNat (((t.val.1 j).val : ℤ) - coordinateFloor N x j + 3), by
    have hb := containing_box_cell_bounds hN x t.val ((containingElements_mem x t.val).mp t.property) j
    omega⟩

def boxIndex {N : ℕ} (hN : 0 < N) (x : Space) (t : ↥(containingElements N x)) :
    (Fin 3 → Fin 6) × Equiv.Perm (Fin 3) := (boxOffsets hN x t, t.val.2)

theorem boxIndex_injective {N : ℕ} (hN : 0 < N) (x : Space) :
    Function.Injective (boxIndex hN x) := by
  intro t u he
  have hp : t.val.2 = u.val.2 :=
    congrArg (fun z : (Fin 3 → Fin 6) × Equiv.Perm (Fin 3) => z.2) he
  have hd : boxOffsets hN x t = boxOffsets hN x u :=
    congrArg (fun z : (Fin 3 → Fin 6) × Equiv.Perm (Fin 3) => z.1) he
  have hc : t.val.1 = u.val.1 := by
    funext j
    apply Fin.ext
    have hz := congrArg (fun d : Fin 3 → Fin 6 => (d j).val) hd
    change Int.toNat (((t.val.1 j).val : ℤ) - coordinateFloor N x j + 3) =
      Int.toNat (((u.val.1 j).val : ℤ) - coordinateFloor N x j + 3) at hz
    have ht := containing_box_cell_bounds hN x t.val ((containingElements_mem x t.val).mp t.property) j
    have hu := containing_box_cell_bounds hN x u.val ((containingElements_mem x u.val).mp u.property) j
    omega
  exact Subtype.ext (Prod.ext hc hp)

theorem containingElements_card {N : ℕ} (hN : 0 < N) (x : Space) :
    (containingElements N x).card ≤ 1296 := by
  have ht := Fintype.card_le_of_injective (boxIndex hN x) (boxIndex_injective hN x)
  norm_num only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_perm, Fintype.card_fin] at ht
  exact ht

theorem interpolation_indicator_sum_bound {N : ℕ} (hN : 0 < N) {F : Space → ℝ}
    (hF : ∀ x, 0 ≤ F x) (x : Space) :
    (∑ t : Tet N, (elementBox t (boxAnchor t)).indicator F x) ≤ 1296 * F x := by
  have hc : ((containingElements N x).card : ℝ) ≤ 1296 := by
    exact_mod_cast containingElements_card hN x
  calc
    _ = ∑ _t ∈ containingElements N x, F x := by
      simp only [containingElements, Finset.sum_filter, Set.indicator_apply]
    _ = ((containingElements N x).card : ℝ) * F x := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (hF x)

theorem interpolation_box_integral_sum_bound {N : ℕ} (hN : 0 < N) {F : Space → ℝ}
    (hi : Integrable F) (hF : ∀ x, 0 ≤ F x) :
    (∑ t : Tet N, ∫ x in elementBox t (boxAnchor t), F x) ≤ 1296 * ∫ x, F x := by
  have hm (t : Tet N) : MeasurableSet (elementBox t (boxAnchor t)) := measurableSet_Icc
  have hI (t : Tet N) : Integrable ((elementBox t (boxAnchor t)).indicator F) :=
    hi.indicator (hm t)
  calc
    _ = ∫ x, ∑ t : Tet N, (elementBox t (boxAnchor t)).indicator F x := by
      rw [integral_finsetSum _ (fun t _ => hI t)]
      apply Finset.sum_congr rfl
      intro t _
      exact (integral_indicator (hm t)).symm
    _ ≤ ∫ x, 1296 * F x :=
      integral_mono (integrable_finsetSum _ (fun t _ => hI t)) (hi.const_mul 1296)
        (interpolation_indicator_sum_bound hN hF)
    _ = _ := integral_const_mul _ _

theorem local_gradient_sum_bound {N : ℕ} (hN : 0 < N) {g : Fin 3 → Space → ℝ}
    (hg : ∀ j : Fin 3, MemLp (g j) 2 volume) :
    (∑ t : Tet N, localGradientIntegral g t) ≤
      1296 * ∑ j : Fin 3, ∫ x, (g j x) ^ 2 := by
  have hi (j : Fin 3) : Integrable (fun x => (g j x) ^ 2) := (hg j).integrable_sq
  have hs : Integrable (fun x => ∑ j : Fin 3, (g j x) ^ 2) :=
    integrable_finsetSum _ (fun j _ => hi j)
  calc
    _ = ∑ t : Tet N, ∫ x in elementBox t (boxAnchor t), ∑ j : Fin 3, (g j x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact (integral_finsetSum _ (fun j _ => (hi j).integrableOn)).symm
    _ ≤ 1296 * ∫ x, ∑ j : Fin 3, (g j x) ^ 2 :=
      interpolation_box_integral_sum_bound hN hs
        (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by rw [integral_finsetSum _ (fun j _ => hi j)]

end FreudenthalSVLean.InterpolationBoxOverlap
