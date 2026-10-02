import FreudenthalSVLean.FreudenthalMesh

/-!
# Coverage geometry for arbitrary Freudenthal mesh size

The manuscript defines each cube as the union of the six coordinate-chain
tetrahedra.  This module proves the coordinate ordering and one-dimensional
cell selection needed for a coverage proof for every `N`.  No sample mesh
is used to assert an infinite-mesh conclusion.
-/

open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.MeshCoverage

def orderMap (r : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2],
    ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] r

theorem orderMap_bijective : ∀ r : Fin 6, Function.Bijective (orderMap r) := by
  decide +kernel

def orderPerm (r : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (orderMap r) (orderMap_bijective r)

/-- Sorting three real coordinates supplies one of the six chain orders,
including every tie case. -/
theorem descending_order_exists (x : Space) :
    ∃ σ : Equiv.Perm (Fin 3), x (σ 1) ≤ x (σ 0) ∧ x (σ 2) ≤ x (σ 1) := by
  by_cases h01 : x 1 ≤ x 0
  · by_cases h12 : x 2 ≤ x 1
    · exact ⟨orderPerm 0, h01, h12⟩
    · by_cases h02 : x 2 ≤ x 0
      · exact ⟨orderPerm 1, h02, le_of_not_ge h12⟩
      · exact ⟨orderPerm 4, le_of_not_ge h02, h01⟩
  · by_cases h02 : x 2 ≤ x 0
    · exact ⟨orderPerm 2, le_of_not_ge h01, h02⟩
    · by_cases h12 : x 2 ≤ x 1
      · exact ⟨orderPerm 3, h12, le_of_not_ge h02⟩
      · exact ⟨orderPerm 5, le_of_not_ge h12, le_of_not_ge h01⟩

/-- Closed lattice unit intervals cover `[0,N]`, with the endpoint `N`
assigned to the last cell rather than to a nonexistent extra cell. -/
theorem unit_interval_exists (N : ℕ) (hN : 0 < N) (a : ℝ)
    (ha : 0 ≤ a) (hbound : a ≤ (N : ℝ)) :
    ∃ c : Fin N, (c.val : ℝ) ≤ a ∧ a ≤ (c.val : ℝ) + 1 := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases h : a ≤ (N : ℝ)
      · by_cases hpos : 0 < N
        · obtain ⟨c, hc⟩ := ih hpos h
          exact ⟨c.castSucc, hc⟩
        · have hzero : N = 0 := by omega
          subst N
          refine ⟨0, ?_, ?_⟩ <;> norm_num at h ⊢ <;> linarith
      · refine ⟨Fin.last N, ?_, ?_⟩
        · exact le_of_not_ge h
        · simpa [Nat.cast_add, Nat.cast_one] using hbound

theorem unitChainSet_mem_of_bounds (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hb : ∀ j, 0 ≤ x j - o j ∧ x j - o j ≤ 1)
    (h01 : x (σ 1) - o (σ 1) ≤ x (σ 0) - o (σ 0))
    (h12 : x (σ 2) - o (σ 2) ≤ x (σ 1) - o (σ 1)) :
    x ∈ unitChainSet σ o := by
  apply (coordinateChainSet_mem _).mpr
  simp only [unitNormalize_apply]
  exact ⟨(hb _).1, (hb _).2, (hb _).1, h01, (hb _).1, h12⟩

theorem unitChainSet_coordinate_bounds (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hx : x ∈ unitChainSet σ o) (j : Fin 3) :
    0 ≤ x j - o j ∧ x j - o j ≤ 1 := by
  have hp := (coordinateChainSet_mem (unitNormalize σ o x)).mp hx
  have hr (r : Fin 3) :
      0 ≤ unitNormalize σ o x r ∧ unitNormalize σ o x r ≤ 1 := by
    fin_cases r
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨hp.2.2.1, hp.2.2.2.1.trans hp.2.1⟩
    · exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2.trans (hp.2.2.2.1.trans hp.2.1)⟩
  obtain ⟨r, rfl⟩ := σ.surjective j
  simpa only [unitNormalize_apply] using hr r

/-- Every closed tetrahedron lies inside the physical cube. -/
theorem tetrahedron_subset_cube {N : ℕ} (hN : 0 < N) (t : Tet N) :
    tetrahedron t ⊆ cube := by
  intro x hx
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hb (j : Fin 3) :
      0 ≤ (N : ℝ) * x j - (t.1 j).val ∧
        (N : ℝ) * x j - (t.1 j).val ≤ 1 := by
    have h := unitChainSet_coordinate_bounds t.2 (cellOrigin t.1)
      ((meshScale N)⁻¹ • x) hx j
    simpa [meshScale, cellOrigin, Pi.smul_apply, smul_eq_mul] using h
  change (∀ j, 0 ≤ x j) ∧ ∀ j, x j ≤ 1
  constructor
  · intro j
    apply (mul_le_mul_iff_right₀ hn).mp
    have hc : (0 : ℝ) ≤ (t.1 j).val := Nat.cast_nonneg _
    nlinarith [(hb j).1]
  · intro j
    apply (mul_le_mul_iff_right₀ hn).mp
    have hc : ((t.1 j).val : ℝ) + 1 ≤ N := by
      exact_mod_cast Nat.succ_le_of_lt (t.1 j).isLt
    nlinarith [(hb j).2]

/-- Full mesh coverage for every positive integer `N`, including boundary
points and coordinate ties. -/
theorem cube_covered (N : ℕ) (hN : 0 < N) (x : Space) (hx : x ∈ cube) :
    ∃ t : Tet N, x ∈ tetrahedron t := by
  have hcell (j : Fin 3) :
      ∃ c : Fin N, (c.val : ℝ) ≤ (N : ℝ) * x j ∧
        (N : ℝ) * x j ≤ (c.val : ℝ) + 1 := by
    apply unit_interval_exists N hN ((N : ℝ) * x j)
    · exact mul_nonneg (Nat.cast_nonneg N) (hx.1 j)
    · simpa using mul_le_mul_of_nonneg_left (hx.2 j) (Nat.cast_nonneg N)
  choose c hc0 hc1 using hcell
  let y : Space := fun j => (N : ℝ) * x j - (c j).val
  have hy (j : Fin 3) : 0 ≤ y j ∧ y j ≤ 1 := by
    dsimp [y]
    constructor <;> linarith [hc0 j, hc1 j]
  obtain ⟨σ, h01, h12⟩ := descending_order_exists y
  refine ⟨(c, σ), ?_⟩
  apply unitChainSet_mem_of_bounds σ (cellOrigin c) ((meshScale N)⁻¹ • x)
  · intro j
    simpa [meshScale, cellOrigin, Pi.smul_apply, smul_eq_mul, y] using hy j
  · simpa [meshScale, cellOrigin, Pi.smul_apply, smul_eq_mul, y] using h01
  · simpa [meshScale, cellOrigin, Pi.smul_apply, smul_eq_mul, y] using h12

theorem tetrahedra_union_cube (N : ℕ) (hN : 0 < N) :
    (⋃ t : Tet N, tetrahedron t) = cube := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    exact tetrahedron_subset_cube hN t ht
  · intro hx
    obtain ⟨t, ht⟩ := cube_covered N hN x hx
    exact Set.mem_iUnion.mpr ⟨t, ht⟩

end FreudenthalSVLean.MeshCoverage
