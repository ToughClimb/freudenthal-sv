import FreudenthalSVLean.GridNodal
import FreudenthalSVLean.PolynomialDegree

/-!
# Nodal support on the infinite lattice

For the manuscript's continuous nodal functions in `vertex-raw-bubble`,
this module proves the global hat vanishes on every Freudenthal
tetrahedron which does not contain its lattice node as a vertex.  The
argument uses arbitrary integer origins and nodes, rather than coverage
assertions from sample meshes.  Together with `GridNodal` this identifies
the global continuous function with the usual local barycentric data.
-/

open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.GridNodal

noncomputable section

namespace FreudenthalSVLean.GridNodalSupport

def intPoint (n : Fin 3 → ℤ) : Space := fun j => n j

theorem nodal_nonzero_coordinate (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ)
    (x : Space) (hx : x ∈ unitChainSet σ (intPoint c))
    (hn : nodal (intPoint n) x ≠ 0) (j : Fin 3) :
    n j = c j ∨ n j = c j + 1 := by
  have hb := unitChainSet_coordinate_bounds σ (intPoint c) x hx j
  change 0 ≤ x j - (c j : ℝ) ∧ x j - (c j : ℝ) ≤ 1 at hb
  by_cases hl : n j ≤ c j - 1
  · have hlr : (n j : ℝ) ≤ (c j : ℝ) - 1 := by exact_mod_cast hl
    have hd : 1 ≤ (x - intPoint n) j := by
      change 1 ≤ x j - (n j : ℝ)
      linarith
    exact False.elim (hn (hat_zero_of_ge_one _ j hd))
  · by_cases hu : c j + 2 ≤ n j
    · have hur : (c j : ℝ) + 2 ≤ (n j : ℝ) := by exact_mod_cast hu
      have hd : (x - intPoint n) j ≤ -1 := by
        change x j - (n j : ℝ) ≤ -1
        linarith
      exact False.elim (hn (hat_zero_of_le_neg_one _ j hd))
    · omega

theorem coordinateChain_antitone (x : Space) (hx : x ∈ coordinateChainSet)
    (i j : Fin 3) (hij : i ≤ j) : x j ≤ x i := by
  have hp := (coordinateChainSet_mem x).mp hx
  change i.val ≤ j.val at hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    linarith! [hp.2.2.2.1, hp.2.2.2.2.2]

theorem nodal_zero_of_reversed_corner (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ)
    (x : Space) (hx : x ∈ unitChainSet σ (intPoint c))
    (i j : Fin 3) (hij : i ≤ j) (hi : n (σ i) = c (σ i))
    (hj : n (σ j) = c (σ j) + 1) : nodal (intPoint n) x = 0 := by
  have ho := coordinateChain_antitone (unitNormalize σ (intPoint c) x) hx i j hij
  simp only [unitNormalize_apply, intPoint] at ho
  apply hat_zero_of_difference _ (σ i) (σ j)
  simp only [Pi.sub_apply, intPoint, hi, hj, Int.cast_add, Int.cast_one]
  linarith

theorem intPoint_eq_chainVertex (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ) (a : Fin 4)
    (hn : ∀ r : Fin 3, n (σ r) = c (σ r) + if r.val < a.val then 1 else 0) :
    intPoint n = ChainGeometry.chainVertex σ (intPoint c) a := by
  funext j
  obtain ⟨r, rfl⟩ := σ.surjective j
  simp only [intPoint, ChainGeometry.chainVertex, Equiv.symm_apply_apply, hn,
    Int.cast_add, apply_ite, Int.cast_one, Int.cast_zero]
  split_ifs <;> rfl

/-- Every lattice-node hat has zero restriction on each nonincident
closed tetrahedron; all boundary and tie cases are included. -/
theorem nodal_zero_of_not_vertex (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ)
    (x : Space) (hx : x ∈ unitChainSet σ (intPoint c))
    (hnot : ∀ a : Fin 4, intPoint n ≠ ChainGeometry.chainVertex σ (intPoint c) a) :
    nodal (intPoint n) x = 0 := by
  by_contra hn
  have h0 := nodal_nonzero_coordinate σ c n x hx hn (σ 0)
  have h1 := nodal_nonzero_coordinate σ c n x hx hn (σ 1)
  have h2 := nodal_nonzero_coordinate σ c n x hx hn (σ 2)
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · apply hnot 0
        apply intPoint_eq_chainVertex
        intro r
        fin_cases r
        · simpa using h0
        · simpa using h1
        · simpa using! h2
      · exact hn (nodal_zero_of_reversed_corner σ c n x hx 0 2 (by decide) h0 h2)
    · exact hn (nodal_zero_of_reversed_corner σ c n x hx 0 1 (by decide) h0 h1)
  · rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · apply hnot 1
        apply intPoint_eq_chainVertex
        intro r
        fin_cases r
        · simpa using h0
        · simpa using h1
        · simpa using! h2
      · exact hn (nodal_zero_of_reversed_corner σ c n x hx 1 2 (by decide) h1 h2)
    · rcases h2 with h2 | h2
      · apply hnot 2
        apply intPoint_eq_chainVertex
        intro r
        fin_cases r
        · simpa using h0
        · simpa using h1
        · simpa using! h2
      · apply hnot 3
        apply intPoint_eq_chainVertex
        intro r
        fin_cases r
        · simpa using h0
        · simpa using h1
        · simpa using! h2

theorem chainVertex_injective (σ : Equiv.Perm (Fin 3)) (o : Space) :
    Function.Injective (ChainGeometry.chainVertex σ o) := by
  intro a b hab
  by_contra hn
  have h := congrArg (fun x : Space => eval x (ChainGeometry.barycentric σ o a)) hab
  simp [ChainGeometry.barycentric_vertex, hn] at h

def nodalPolynomial (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ a : Fin 4, if intPoint n = ChainGeometry.chainVertex σ (intPoint c) a then
    ChainGeometry.barycentric σ (intPoint c) a else 0

/-- A lattice node outside one coordinate interval of the containing
unit cube has zero local polynomial, for every integer cube origin. -/
theorem nodalPolynomial_zero_of_outside_coordinate (σ : Equiv.Perm (Fin 3))
    (c n : Fin 3 → ℤ) (j : Fin 3) (h : n j < c j ∨ c j + 1 < n j) :
    nodalPolynomial σ c n = 0 := by
  unfold nodalPolynomial
  apply Finset.sum_eq_zero
  intro a _
  apply if_neg
  intro he
  have hj := congrFun he j
  change (n j : ℝ) = (c j : ℝ) + if (σ.symm j).val < a.val then 1 else 0 at hj
  have hb : (c j : ℝ) ≤ (n j : ℝ) ∧ (n j : ℝ) ≤ (c j : ℝ) + 1 := by
    split_ifs at hj <;> constructor <;> linarith
  rcases h with h | h
  · have hr : (n j : ℝ) < (c j : ℝ) := by exact_mod_cast h
    linarith
  · have hr : (c j : ℝ) + 1 < (n j : ℝ) := by exact_mod_cast h
    linarith

theorem nodalPolynomial_eq_barycentric (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ)
    (a : Fin 4) (ha : intPoint n = ChainGeometry.chainVertex σ (intPoint c) a) :
    nodalPolynomial σ c n = ChainGeometry.barycentric σ (intPoint c) a := by
  simp [nodalPolynomial, ha, (chainVertex_injective σ (intPoint c)).eq_iff]

/-- The global continuous hat has exactly the local piecewise-affine
polynomial representation on every closed lattice tetrahedron. -/
theorem nodalPolynomial_eval (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ)
    (x : Space) (hx : x ∈ unitChainSet σ (intPoint c)) :
    eval x (nodalPolynomial σ c n) = nodal (intPoint n) x := by
  by_cases hn : ∃ a : Fin 4, intPoint n = ChainGeometry.chainVertex σ (intPoint c) a
  · obtain ⟨a, ha⟩ := hn
    rw [nodalPolynomial_eq_barycentric σ c n a ha, ha]
    exact (nodal_eq_barycentric σ (intPoint c) x hx a).symm
  · have hnot : ∀ a : Fin 4, intPoint n ≠ ChainGeometry.chainVertex σ (intPoint c) a :=
      fun a h => hn ⟨a, h⟩
    rw [nodal_zero_of_not_vertex σ c n x hx hnot]
    simp [nodalPolynomial, hnot]

theorem barycentric_degree_le (σ : Equiv.Perm (Fin 3)) (o : Space) (a : Fin 4) :
    (ChainGeometry.barycentric σ o a).totalDegree ≤ 1 := by
  have hc (r : Fin 3) : (ChainGeometry.chainCoordinate σ o r).totalDegree ≤ 1 := by
    exact (PolynomialDegree.sub_degree_le _ _).trans (by simp)
  fin_cases a
  · exact (PolynomialDegree.sub_degree_le _ _).trans (by simpa using hc 0)
  · exact (PolynomialDegree.sub_degree_le _ _).trans (max_le (hc 0) (hc 1))
  · exact (PolynomialDegree.sub_degree_le _ _).trans (max_le (hc 1) (hc 2))
  · exact hc 2

theorem nodalPolynomial_degree_le (σ : Equiv.Perm (Fin 3)) (c n : Fin 3 → ℤ) :
    (nodalPolynomial σ c n).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro a _
  split_ifs
  · exact barycentric_degree_le σ (intPoint c) a
  · simp

end FreudenthalSVLean.GridNodalSupport
