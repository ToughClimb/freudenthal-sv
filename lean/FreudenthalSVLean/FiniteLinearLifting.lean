import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.Projective

/-!
# Fixed bounded right inverses on exact compatibility images

For manuscript equation `vertex-explicit-operator`, a fixed linear map
has a fixed bounded right inverse on its exact image when that image is
finite dimensional.  A finite family has one common bound.  No rank,
choice of columns, or field-dependent geometry enters this argument.
Applying it to the actual vertex compatibility maps requires their
separate geometric definition and trace-to-image equivalence.
-/

open scoped BigOperators

noncomputable section

namespace FreudenthalSVLean.FiniteLinearLifting

theorem bounded_range_lift {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) :
    ∃ (J : A.range →ₗ[ℝ] E) (C : ℝ), 0 < C ∧
      (∀ x : A.range, A (J x) = x.val) ∧ (∀ x : A.range, ‖J x‖ ≤ C * ‖x‖) := by
  obtain ⟨J, hJ⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  let T : A.range →L[ℝ] E := J.toContinuousLinearMap
  refine ⟨J, max 1 ‖T‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_⟩
  · intro x
    have he := LinearMap.congr_fun hJ x
    exact congrArg Subtype.val he
  · intro x
    exact (T.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))

/-- One constant is quantified before every member of the finite family.
Each chosen inverse is linear on the whole exact image of its map. -/
theorem finite_family_range_lifts {I : Type*} [Fintype I] (E F : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)] (A : ∀ i, E i →ₗ[ℝ] F i) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ∀ i, (A i).range →ₗ[ℝ] E i,
      (∀ i (x : (A i).range), A i (J i x) = x.val) ∧
      (∀ i (x : (A i).range), ‖J i x‖ ≤ C * ‖x‖) := by
  classical
  choose J C hC hright hbound using fun i => bounded_range_lift (A i)
  refine ⟨1 + ∑ i : I, C i, ?_, J, hright, ?_⟩
  · have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => (hC i).le)
    linarith
  · intro i x
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) => (hC j).le) (Finset.mem_univ i)
    have hc : C i ≤ 1 + ∑ j : I, C j := by linarith
    exact (hbound i x).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg x))

/-- For the local mean maps in manuscript `vertex-raw-properties`, a
finite family of fixed finite-dimensional operators has one common bound. -/
theorem finite_family_map_bounds {I : Type*} [Fintype I] (E F : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (A : ∀ i, E i →ₗ[ℝ] F i) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (x : E i), ‖A i x‖ ≤ C * ‖x‖ := by
  classical
  let T := fun i => (A i).toContinuousLinearMap
  refine ⟨1 + ∑ i : I, ‖T i‖, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => norm_nonneg (T i))
    linarith
  · intro i x
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) => norm_nonneg (T j)) (Finset.mem_univ i)
    have hc : ‖T i‖ ≤ 1 + ∑ j : I, ‖T j‖ := by linarith
    exact (T i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg x))

end FreudenthalSVLean.FiniteLinearLifting
