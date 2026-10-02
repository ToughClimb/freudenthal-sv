import FreudenthalSVLean.MeshCoverage
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Face containment of actual mesh intersections

For manuscript Lemma `bubble` and the global bubble assembly, an actual
common point of two different Freudenthal tetrahedra lies on a barycentric
face of each.  Strict barycentric positivity determines the integer cell
and the unique coordinate order.  The proof uses uniqueness of sorted
tuples, not a finite list of mesh intersections.  Physical-boundary points
likewise lie on an actual barycentric face.  All statements hold for every
positive mesh size, including `N=1`.
-/

open MvPolynomial Set
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage

noncomputable section

namespace FreudenthalSVLean.MeshIntersectionFaces

set_option backward.isDefEq.respectTransparency false

theorem unit_barycentric_nonneg (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hx : x ∈ unitChainSet σ o) (a : Fin 4) :
    0 ≤ eval x (ChainGeometry.barycentric σ o a) := by
  have hp := (coordinateChainSet_mem _).mp hx
  simp only [unitNormalize_apply] at hp
  fin_cases a <;> simp [ChainGeometry.barycentric,
    ChainGeometry.chainCoordinate] <;> linarith

theorem unit_positive_chain (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hp : ∀ a, 0 < eval x (ChainGeometry.barycentric σ o a)) :
    x (σ 0) - o (σ 0) < 1 ∧
      x (σ 1) - o (σ 1) < x (σ 0) - o (σ 0) ∧
      x (σ 2) - o (σ 2) < x (σ 1) - o (σ 1) ∧
      0 < x (σ 2) - o (σ 2) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  simp [ChainGeometry.barycentric, ChainGeometry.chainCoordinate] at h0 h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem unit_positive_coordinate_bounds (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hp : ∀ a, 0 < eval x (ChainGeometry.barycentric σ o a)) (j : Fin 3) :
    0 < x j - o j ∧ x j - o j < 1 := by
  have hs := unit_positive_chain σ o x hp
  obtain ⟨r, rfl⟩ := σ.surjective j
  fin_cases r <;> dsimp <;> constructor <;> linarith [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]

theorem unit_positive_strictAnti (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hp : ∀ a, 0 < eval x (ChainGeometry.barycentric σ o a)) :
    StrictAnti ((fun j => x j - o j) ∘ σ) := by
  have hs := unit_positive_chain σ o x hp
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  fin_cases i
  · exact hs.2.1
  · exact hs.2.2.1

theorem unit_member_antitone (σ : Equiv.Perm (Fin 3)) (o x : Space)
    (hx : x ∈ unitChainSet σ o) : Antitone ((fun j => x j - o j) ∘ σ) := by
  have hp := (coordinateChainSet_mem _).mp hx
  simp only [unitNormalize_apply] at hp
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  fin_cases i
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2.2

theorem integer_interval_unique (a b : ℕ) (y : ℝ)
    (ha : (a : ℝ) < y ∧ y < (a : ℝ) + 1)
    (hb : (b : ℝ) ≤ y ∧ y ≤ (b : ℝ) + 1) : a = b := by
  have hab : a ≤ b := by
    by_contra h
    have hn : b + 1 ≤ a := by omega
    have hr : (b : ℝ) + 1 ≤ a := by exact_mod_cast hn
    linarith
  have hba : b ≤ a := by
    by_contra h
    have hn : a + 1 ≤ b := by omega
    have hr : (a : ℝ) + 1 ≤ b := by exact_mod_cast hn
    linarith
  omega

/-- Strict positivity on one owner determines both its cell and its
coordinate order, even when the other owner's membership is closed. -/
theorem positive_owner_unique {N : ℕ} (t u : Tet N) (x : Space)
    (hp : ∀ a, 0 < eval x (barycentric t a)) (hu : x ∈ tetrahedron u) : t = u := by
  let y : Space := (meshScale N)⁻¹ • x
  have hp' (a : Fin 4) : 0 < eval y (ChainGeometry.barycentric t.2 (cellOrigin t.1) a) := by
    simpa only [FreudenthalMesh.barycentric, scaledBarycentric_eval] using hp a
  have hc : t.1 = u.1 := by
    funext j
    apply Fin.ext
    have ht := unit_positive_coordinate_bounds t.2 (cellOrigin t.1) y hp' j
    have hu' := unitChainSet_coordinate_bounds u.2 (cellOrigin u.1) y hu j
    apply integer_interval_unique _ _ (y j)
    · change 0 < y j - ((t.1 j).val : ℝ) ∧ y j - ((t.1 j).val : ℝ) < 1 at ht
      constructor <;> linarith
    · change 0 ≤ y j - ((u.1 j).val : ℝ) ∧ y j - ((u.1 j).val : ℝ) ≤ 1 at hu'
      constructor <;> linarith
  let f : Fin 3 → ℝ := fun j => y j - cellOrigin t.1 j
  have hstrict : StrictAnti (f ∘ t.2) := unit_positive_strictAnti _ _ _ hp'
  have hother : Antitone (f ∘ u.2) := by
    have hm := unit_member_antitone u.2 (cellOrigin u.1) y hu
    simpa only [← hc] using hm
  have hsorted : f ∘ t.2 = f ∘ u.2 := Tuple.unique_antitone hstrict.antitone hother
  have hinj : Function.Injective f := by
    intro i j hij
    apply t.2.symm.injective
    apply hstrict.injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
  have hσ : t.2 = u.2 := by
    apply Equiv.ext
    intro r
    exact hinj (congrFun hsorted r)
  exact Prod.ext hc hσ

theorem barycentric_nonneg {N : ℕ} (t : Tet N) (x : Space)
    (hx : x ∈ tetrahedron t) (a : Fin 4) : 0 ≤ eval x (barycentric t a) := by
  rw [FreudenthalMesh.barycentric, scaledBarycentric_eval]
  exact unit_barycentric_nonneg _ _ _ hx a

/-- Every intersection of distinct actual elements lies in a face of
the first element.  Interchanging the owners gives the second face. -/
theorem common_point_face {N : ℕ} (t u : Tet N) (hne : t ≠ u) (x : Space)
    (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) :
    ∃ a : Fin 4, eval x (barycentric t a) = 0 := by
  by_contra h
  have hp (a : Fin 4) : 0 < eval x (barycentric t a) :=
    lt_of_le_of_ne (barycentric_nonneg t x ht a)
      (Ne.symm (fun he => h ⟨a, he⟩))
  exact hne (positive_owner_unique t u x hp hu)

theorem boundary_point_face {N : ℕ} (_hN : 0 < N) (t : Tet N) (x : Space)
    (ht : x ∈ tetrahedron t) (hx : x ∈ cubeBoundary) :
    ∃ a : Fin 4, eval x (barycentric t a) = 0 := by
  by_contra h
  have hp (a : Fin 4) : 0 < eval x (barycentric t a) :=
    lt_of_le_of_ne (barycentric_nonneg t x ht a)
      (Ne.symm (fun he => h ⟨a, he⟩))
  have hp' (a : Fin 4) : 0 < eval ((meshScale N)⁻¹ • x)
      (ChainGeometry.barycentric t.2 (cellOrigin t.1) a) := by
    simpa only [FreudenthalMesh.barycentric, scaledBarycentric_eval] using hp a
  obtain ⟨j, hj⟩ := hx.2
  have hb := unit_positive_coordinate_bounds t.2 (cellOrigin t.1)
    ((meshScale N)⁻¹ • x) hp' j
  simp only [meshScale, inv_inv, Pi.smul_apply, smul_eq_mul, cellOrigin] at hb
  have hc : ((t.1 j).val : ℝ) + 1 ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (t.1 j).isLt
  rcases hj with hj | hj
  · rw [hj, mul_zero] at hb
    have hn : (0 : ℝ) ≤ (t.1 j).val := Nat.cast_nonneg _
    linarith [hb.1]
  · rw [hj, mul_one] at hb
    linarith [hb.2]

end FreudenthalSVLean.MeshIntersectionFaces
