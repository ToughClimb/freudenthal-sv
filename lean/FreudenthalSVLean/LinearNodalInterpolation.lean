import FreudenthalSVLean.ActualFaceConformity

/-!
# Fixed homogeneous P1 nodal interpolation on the actual mesh

For the interpolation stage in manuscript Lemma `means` and equation
`SZ`, arbitrary vector nodal coefficients define one linear map into
the actual conforming homogeneous degree-one velocity space.  Boundary
coefficients are set to zero by the fixed geometric interior-node test.
Conformity and boundary values follow from the true global nodal fields.
Every element has its exact four-vertex barycentric expansion, even
though the initial definition sums over all actual grid vertices.
The coefficients will be supplied by volume averaging; no stability
bound or mean-preservation property is asserted by this module alone.
-/

open scoped BigOperators Classical
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity

noncomputable section

namespace FreudenthalSVLean.LinearNodalInterpolation

set_option backward.isDefEq.respectTransparency false

def interiorNode {N : ℕ} (n : GridVertex N) : Prop :=
  ∀ j : Fin 3, 0 < (n j).val ∧ (n j).val < N

def nodalCoefficient {N : ℕ} (c : GridVertex N → Space) (n : GridVertex N) (j : Fin 3) : ℝ :=
  if interiorNode n then c n j else 0

def nodalInterpolation {N : ℕ} (c : GridVertex N → Space) : BrokenVelocity N :=
  fun t j => ∑ n : GridVertex N,
    C (nodalCoefficient c n j) * meshNodalPolynomial t (integerGrid n)

theorem nodalInterpolation_add {N : ℕ} (c d : GridVertex N → Space) :
    nodalInterpolation (c + d) = nodalInterpolation c + nodalInterpolation d := by
  funext t j
  simp only [nodalInterpolation, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : interiorNode n
  · simp only [nodalCoefficient, if_pos hn, Pi.add_apply, map_add, add_mul]
  · simp only [nodalCoefficient, if_neg hn, map_zero, zero_mul, add_zero]

theorem nodalInterpolation_smul {N : ℕ} (s : ℝ) (c : GridVertex N → Space) :
    nodalInterpolation (s • c) = s • nodalInterpolation c := by
  funext t j
  simp only [nodalInterpolation, Pi.smul_apply, smul_eq_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : interiorNode n
  · simp only [nodalCoefficient, if_pos hn, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  · simp only [nodalCoefficient, if_neg hn, map_zero, zero_mul, mul_zero]

def nodalInterpolationLinear (N : ℕ) : (GridVertex N → Space) →ₗ[ℝ] BrokenVelocity N where
  toFun := nodalInterpolation
  map_add' := nodalInterpolation_add
  map_smul' := nodalInterpolation_smul

theorem interiorNode_integer_lower {N : ℕ} {n : GridVertex N} (hn : interiorNode n)
    (j : Fin 3) : integerGrid n j ≠ 0 := by
  change ((n j).val : ℤ) ≠ 0
  exact_mod_cast (hn j).1.ne'

theorem interiorNode_integer_upper {N : ℕ} {n : GridVertex N} (hn : interiorNode n)
    (j : Fin 3) : integerGrid n j ≠ (N : ℤ) := by
  change ((n j).val : ℤ) ≠ (N : ℤ)
  exact_mod_cast (hn j).2.ne

theorem nodalInterpolation_mem {N : ℕ} (hN : 0 < N) (c : GridVertex N → Space) :
    nodalInterpolation c ∈ velocitySpace N 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    apply totalDegree_finsetSum_le
    intro n _
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using meshNodalPolynomial_degree_le t (integerGrid n))
  · intro t u x ht hu j
    simp only [nodalInterpolation, map_sum, map_mul, eval_C,
      meshNodalPolynomial_conforming t u _ x ht hu]
  · intro t x ht hx j
    simp only [nodalInterpolation, map_sum, map_mul, eval_C]
    apply Finset.sum_eq_zero
    intro n _
    by_cases hn : interiorNode n
    · rw [meshNodalPolynomial_eval t _ x ht]
      obtain ⟨i, hi⟩ := hx.2
      rcases hi with hi | hi
      · rw [meshNodal_zero_lower _ (gridNode_inBox n) x i hi (interiorNode_integer_lower hn i),
          mul_zero]
      · rw [meshNodal_zero_upper hN _ (gridNode_inBox n) x i hi
          (interiorNode_integer_upper hn i), mul_zero]
    · simp only [nodalCoefficient, if_neg hn, zero_mul]

/-- A single linear map, with geometry fixed before any nodal input. -/
def homogeneousNodalInterpolation {N : ℕ} (hN : 0 < N) :
    (GridVertex N → Space) →ₗ[ℝ] velocitySpace N 1 :=
  (nodalInterpolationLinear N).codRestrict _ (nodalInterpolation_mem hN)

theorem nodalInterpolation_on_element {N : ℕ} (c : GridVertex N → Space)
    (t : Tet N) (j : Fin 3) :
    nodalInterpolation c t j = ∑ a : Fin 4,
      C (nodalCoefficient c (gridVertexOfTet t a) j) * FreudenthalMesh.barycentric t a := by
  have hs : (∑ n : GridVertex N,
      C (nodalCoefficient c n j) * meshNodalPolynomial t (integerGrid n)) =
      ∑ n ∈ gridVertices t,
        C (nodalCoefficient c n j) * meshNodalPolynomial t (integerGrid n) := by
    apply (Finset.sum_subset (Finset.subset_univ (gridVertices t)) ?_).symm
    intro n _ hn
    rw [node_polynomial_zero_of_missing t n hn, mul_zero]
  rw [nodalInterpolation, hs, gridVertices, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a _
    rw [meshNodalPolynomial_eq_barycentric t _ a (gridVertex_intPoint t a)]
  · intro a _ b _ he
    exact gridVertexOfTet_injective t he

end FreudenthalSVLean.LinearNodalInterpolation
