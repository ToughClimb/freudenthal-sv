import FreudenthalSVLean.QuarticNodalRealization
import FreudenthalSVLean.QuarticVolume

/-!
# Actual conformity and rectangular zero trace of the quartic macro fields

For manuscript Lemma `macro`, the eleven displayed vector fields are
restrictions of one global continuous nodal-product function per field.
Conformity is proved on every actual shared point of the twelve closed
tetrahedra, not only on a list of face labels.  Positive-exponent nodes
away from each rectangular boundary plane give zero exterior trace.
The existing edge-divergence and genuine-volume mean formulas therefore
apply to actual conforming fields.  Scaling, general-mesh extension and
the uniform macro right inverse are separate subsequent obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticPolynomial
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.QuarticNodalRealization
open FreudenthalSVLean.GridNodalSupport

noncomputable section

namespace FreudenthalSVLean.QuarticMacroConformity

def nodalVector (w : FieldIndex) (σ : Equiv.Perm SpatialIndex) (c : ScaledPoint)
    (j : SpatialIndex) : MvPolynomial SpatialIndex ℝ :=
  ∑ r : TermIndex, if (macroTerms w r).component = j then
    C ((macroTerms w r).coefficient : ℝ) * nodalProduct w r σ c else 0

def globalVector (w : FieldIndex) (x : Space) (j : SpatialIndex) : ℝ :=
  ∑ r : TermIndex, if (macroTerms w r).component = j then
    ((macroTerms w r).coefficient : ℝ) * globalProduct w r x else 0

theorem localVectorPolynomial_eq_products (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    localVectorPolynomial t w j = ∑ r : TermIndex,
      if (macroTerms w r).component = j then
        C (macroTerms w r).coefficient * localNodalProduct t w r else 0 := by
  unfold localVectorPolynomial
  apply Finset.sum_congr rfl
  intro r _
  rw [local_product_identity]
  by_cases hp : pointInTet t (macroTerms w r).point = true <;>
    by_cases hc : (macroTerms w r).component = j <;>
    simp [hp, hc, smul_eq_C_mul]

theorem realSpatialVector_eq_substitution (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    realSpatialVector t w j = eval₂Hom C
      (ChainGeometry.barycentric (tetEquiv t) (realCellCorner t))
      (map (Rat.castHom ℝ) (localVectorPolynomial t w j)) := by
  simp only [realSpatialVector, spatialVector, coe_eval₂Hom, map_eval₂, Function.comp_def]
  congr 1
  funext i
  exact ChainGeometry.map_barycentric (Rat.castHom ℝ) (tetEquiv t) (cellCorner t) i

theorem realSpatialVector_eq_nodalVector (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    realSpatialVector t w j = nodalVector w (tetEquiv t) (integerCorner t) j := by
  rw [realSpatialVector_eq_substitution, localVectorPolynomial_eq_products]
  simp only [map_sum, apply_ite, map_mul, map_C, map_zero, eval₂Hom_C, nodalVector]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : (macroTerms w r).component = j
  · simp only [hc, if_true]
    rw [← nodalProduct_spatial]
    rfl
  · simp only [hc, if_false]

theorem nodalVector_eval (w : FieldIndex) (σ : Equiv.Perm SpatialIndex) (c : ScaledPoint)
    (x : Space) (hx : x ∈ unitChainSet σ (intPoint c)) (j : SpatialIndex) :
    eval x (nodalVector w σ c j) = globalVector w x j := by
  simp only [nodalVector, map_sum, apply_ite, map_mul, eval_C, map_zero,
    nodalProduct_eval w _ σ c x hx, globalVector]

theorem nodalProduct_degree (w : FieldIndex) (r : TermIndex)
    (σ : Equiv.Perm SpatialIndex) (c : ScaledPoint) :
    (nodalProduct w r σ c).totalDegree ≤ 4 := by
  unfold nodalProduct
  calc
    _ ≤ (∏ a : LocalVertex,
        nodalPolynomial σ c (referenceNode (hostTet w r) a) ^ hostExponent w r a).totalDegree :=
      by
        simpa only [totalDegree_C, zero_add] using totalDegree_mul
          (C ((BernsteinPolynomial.normalization (R := ℚ) 4 (hostExponent w r) : ℚ) : ℝ))
          (∏ a : LocalVertex,
            nodalPolynomial σ c (referenceNode (hostTet w r) a) ^ hostExponent w r a)
    _ ≤ ∑ a : LocalVertex,
        (nodalPolynomial σ c (referenceNode (hostTet w r) a) ^ hostExponent w r a).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ a : LocalVertex, hostExponent w r a := by
      apply Finset.sum_le_sum
      intro a _
      exact (totalDegree_pow _ _).trans (by
        simpa only [mul_one] using Nat.mul_le_mul_left (hostExponent w r a)
          (nodalPolynomial_degree_le σ c _))
    _ = 4 := by rw [← Finsupp.degree_eq_sum, host_degree]

theorem nodalVector_degree (w : FieldIndex) (σ : Equiv.Perm SpatialIndex)
    (c : ScaledPoint) (j : SpatialIndex) : (nodalVector w σ c j).totalDegree ≤ 4 := by
  unfold nodalVector
  apply totalDegree_finsetSum_le
  intro r _
  split_ifs
  · exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using nodalProduct_degree w r σ c)
  · simp

theorem realSpatialVector_degree (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    (realSpatialVector t w j).totalDegree ≤ 4 := by
  rw [realSpatialVector_eq_nodalVector]
  exact nodalVector_degree w _ _ j

theorem realSpatialVector_eval (t : TetIndex) (w : FieldIndex) (x : Space)
    (hx : x ∈ unitChainSet (tetEquiv t) (realCellCorner t)) (j : SpatialIndex) :
    eval x (realSpatialVector t w j) = globalVector w x j := by
  rw [realSpatialVector_eq_nodalVector]
  exact nodalVector_eval w _ _ x (by simpa only [integerCorner_cast] using hx) j

/-- Conformity on all actual intersections, including faces, edges and
vertices, follows from evaluation against a single global function. -/
theorem realSpatialVector_conforming (t u : TetIndex) (w : FieldIndex) (x : Space)
    (ht : x ∈ unitChainSet (tetEquiv t) (realCellCorner t))
    (hu : x ∈ unitChainSet (tetEquiv u) (realCellCorner u)) (j : SpatialIndex) :
    eval x (realSpatialVector t w j) = eval x (realSpatialVector u w j) := by
  rw [realSpatialVector_eval t w x ht j, realSpatialVector_eval u w x hu j]

theorem globalProduct_continuous (w : FieldIndex) (r : TermIndex) :
    Continuous (globalProduct w r) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro a _
  exact (GridNodal.nodal_continuous _).pow _

theorem globalVector_continuous (w : FieldIndex) (j : SpatialIndex) :
    Continuous (fun x => globalVector w x j) := by
  apply continuous_finsetSum
  intro r _
  by_cases hc : (macroTerms w r).component = j
  · simp only [hc, if_true]
    exact continuous_const.mul (globalProduct_continuous w r)
  · simp only [hc, if_false]
    exact continuous_const

def upperCorner (j : SpatialIndex) : ℤ := if j = 0 then 2 else 1

/-- Every term has an active nodal factor away from each of the six
rectangular boundary planes.  These are integer/natural geometric checks. -/
theorem boundary_node_certificate : ∀ (w : FieldIndex) (r : TermIndex) (j : SpatialIndex),
    (∃ a : LocalVertex,
      0 < (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat ∧
      0 < referenceNode (hostTet w r) a j) ∧
    (∃ a : LocalVertex,
      0 < (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat ∧
      referenceNode (hostTet w r) a j < upperCorner j) := by
  decide +kernel

/-- Zero polynomial on every lattice tetrahedron in a cube outside the
two-cube rectangle.  The origin is arbitrary, not a sampled mesh case. -/
theorem nodalProduct_zero_off_rectangle (w : FieldIndex) (r : TermIndex)
    (σ : Equiv.Perm SpatialIndex) (c : ScaledPoint)
    (hc : ∃ j, c j < 0 ∨ upperCorner j ≤ c j) : nodalProduct w r σ c = 0 := by
  obtain ⟨j, hj⟩ := hc
  have hz : ∃ a : LocalVertex, 0 < hostExponent w r a ∧
      nodalPolynomial σ c (referenceNode (hostTet w r) a) = 0 := by
    rcases hj with hj | hj
    · obtain ⟨a, ha, hn⟩ := (boundary_node_certificate w r j).1
      refine ⟨a, ha, nodalPolynomial_zero_of_outside_coordinate σ c _ j (Or.inr ?_)⟩
      omega
    · obtain ⟨a, ha, hn⟩ := (boundary_node_certificate w r j).2
      refine ⟨a, ha, nodalPolynomial_zero_of_outside_coordinate σ c _ j (Or.inl ?_)⟩
      omega
  obtain ⟨a, ha, hz⟩ := hz
  unfold nodalProduct
  have hprod : (∏ b : LocalVertex,
      nodalPolynomial σ c (referenceNode (hostTet w r) b) ^ hostExponent w r b) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [hz]
    exact zero_pow (Nat.ne_of_gt ha)
  rw [hprod, mul_zero]

theorem nodalVector_zero_off_rectangle (w : FieldIndex) (σ : Equiv.Perm SpatialIndex)
    (c : ScaledPoint) (hc : ∃ j, c j < 0 ∨ upperCorner j ≤ c j) (j : SpatialIndex) :
    nodalVector w σ c j = 0 := by
  unfold nodalVector
  apply Finset.sum_eq_zero
  intro r _
  rw [nodalProduct_zero_off_rectangle w r σ c hc]
  simp

theorem globalProduct_lower_zero (w : FieldIndex) (r : TermIndex) (x : Space)
    (j : SpatialIndex) (hx : x j = 0) : globalProduct w r x = 0 := by
  obtain ⟨a, ha, hn⟩ := (boundary_node_certificate w r j).1
  have hn' : (1 : ℝ) ≤ (referenceNode (hostTet w r) a j : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ referenceNode (hostTet w r) a j by omega)
  unfold globalProduct
  have hz : GridNodal.nodal (intPoint (referenceNode (hostTet w r) a)) x = 0 := by
    apply GridNodal.hat_zero_of_le_neg_one _ j
    change x j - (referenceNode (hostTet w r) a j : ℝ) ≤ -1
    rw [hx]
    linarith
  have hprod : (∏ b : LocalVertex,
      GridNodal.nodal (intPoint (referenceNode (hostTet w r) b)) x ^ hostExponent w r b) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [hz]
    exact zero_pow (Nat.ne_of_gt ha)
  rw [hprod, mul_zero]

theorem globalProduct_upper_zero (w : FieldIndex) (r : TermIndex) (x : Space)
    (j : SpatialIndex) (hx : x j = (upperCorner j : ℝ)) : globalProduct w r x = 0 := by
  obtain ⟨a, ha, hn⟩ := (boundary_node_certificate w r j).2
  have hn' : (referenceNode (hostTet w r) a j : ℝ) + 1 ≤ (upperCorner j : ℝ) := by
    exact_mod_cast (show referenceNode (hostTet w r) a j + 1 ≤ upperCorner j by omega)
  unfold globalProduct
  have hz : GridNodal.nodal (intPoint (referenceNode (hostTet w r) a)) x = 0 := by
    apply GridNodal.hat_zero_of_ge_one _ j
    change 1 ≤ x j - (referenceNode (hostTet w r) a j : ℝ)
    rw [hx]
    linarith
  have hprod : (∏ b : LocalVertex,
      GridNodal.nodal (intPoint (referenceNode (hostTet w r) b)) x ^ hostExponent w r b) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [hz]
    exact zero_pow (Nat.ne_of_gt ha)
  rw [hprod, mul_zero]

theorem globalVector_boundary_zero (w : FieldIndex) (x : Space)
    (hb : ∃ i : SpatialIndex, x i = 0 ∨ x i = (upperCorner i : ℝ)) (j : SpatialIndex) :
    globalVector w x j = 0 := by
  obtain ⟨i, hi⟩ := hb
  unfold globalVector
  apply Finset.sum_eq_zero
  intro r _
  have hz : globalProduct w r x = 0 := by
    rcases hi with hi | hi
    · exact globalProduct_lower_zero w r x i hi
    · exact globalProduct_upper_zero w r x i hi
  simp [hz]

/-- Actual zero trace on the full rectangular exterior of the two-cube
patch, including every edge and corner of that exterior. -/
theorem realSpatialVector_boundary_zero (t : TetIndex) (w : FieldIndex) (x : Space)
    (ht : x ∈ unitChainSet (tetEquiv t) (realCellCorner t))
    (hb : ∃ i : SpatialIndex, x i = 0 ∨ x i = (upperCorner i : ℝ)) (j : SpatialIndex) :
    eval x (realSpatialVector t w j) = 0 := by
  rw [realSpatialVector_eval t w x ht j]
  exact globalVector_boundary_zero w x hb j

end FreudenthalSVLean.QuarticMacroConformity
