import FreudenthalSVLean.QuarticMacro
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Bernstein realization of the quartic macro fields

This module closes the finite coefficient-level bridge between the eleven
global Bernstein fields displayed in the proof of the quartic two-cube macro
lift and the matrix certified in `QuarticMacro.lean`.  The source is
`overleaf_single_file/manuscript.tex`, lines 1295--1365, in particular
equations `bernstein-divergence`, `bernstein-mean`, and
`quartic-mean-matrix`.

The two-cube patch is `[0,2] × [0,1] × [0,1]`, with tetrahedra ordered first
by cube and then by `(xyz,xzy,yxz,yzx,zxy,zyx)`.  Physical Bernstein control
points are stored after multiplication by four.  Thus all geometry and all
coefficient calculations remain over `ℤ` and `ℚ`.

The module proves, without an external oracle, that:

* every displayed control point is strictly inside the two-cube patch;
* every edge-carried cubic Bernstein coefficient of the divergence of each
  of the eleven fields is zero on each of the twelve tetrahedra;
* consequently the explicitly defined Bernstein edge restrictions vanish;
* the first eleven scaled element means computed from the displayed fields
  are exactly the paper matrix `A`; and
* the twelfth mean is the negative sum of the first eleven means.

The precise scope of this module is the finite Bernstein coefficient
calculus just described.  `QuarticPolynomial`, `QuarticSpatial` and
`QuarticVolume` derive its actual polynomial differentiation, real edge
traces and Lebesgue means.  `QuarticNodalRealization` and
`QuarticMacroConformity` prove the global nodal-product realization and
actual conformity and exterior zero trace; `PhysicalMacroLift` proves the
fixed mean inverse and uniform energy estimate on arbitrary physical patches.
-/

open scoped BigOperators
open Matrix

namespace FreudenthalSVLean.QuarticBernstein

abbrev SpatialIndex := Fin 3
abbrev LocalVertex := Fin 4
abbrev LocalTetIndex := Fin 6
abbrev TetIndex := Fin 12
abbrev FieldIndex := Fin 11
abbrev TermIndex := Fin 3

/-- A physical point after multiplying all coordinates by four. -/
abbrev ScaledPoint := SpatialIndex → ℤ

/-- A cubic multi-index.  Each entry lies in `0,1,2,3`; the separate degree
predicate below enforces total degree three. -/
abbrev CubicMultiIndex := LocalVertex → Fin 4

/-- The six coordinate orders `(xyz,xzy,yxz,yzx,zxy,zyx)` used in each cube. -/
def chainPermutation : LocalTetIndex → SpatialIndex → SpatialIndex :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2],
    ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- The local tetrahedron number inside the host cube. -/
def localTetIndex (t : TetIndex) : LocalTetIndex :=
  ⟨t.val % 6, Nat.mod_lt _ (by decide)⟩

/-- The coordinate permutation of a tetrahedron in the fixed paper order. -/
def tetPermutation (t : TetIndex) : SpatialIndex → SpatialIndex :=
  chainPermutation (localTetIndex t)

/-- The scaled lower corner of the host cube. -/
def scaledCellCorner (t : TetIndex) : ScaledPoint := fun j =>
  if j = 0 ∧ 6 ≤ t.val then 4 else 0

/-- Four times the barycentric coordinates of a physical quartic control
point on a translated unit Freudenthal tetrahedron.  Negative entries mean
that the point is outside the tetrahedron. -/
def scaledBarycentric (t : TetIndex) (p : ScaledPoint) : LocalVertex → ℤ :=
  let σ := tetPermutation t
  let ξ : SpatialIndex → ℤ := fun j => p j - scaledCellCorner t j
  ![4 - ξ (σ 0),
    ξ (σ 0) - ξ (σ 1),
    ξ (σ 1) - ξ (σ 2),
    ξ (σ 2)]

/-- Coordinate unit vector, represented over `ℚ`. -/
def coordinateUnit (i : SpatialIndex) : SpatialIndex → ℚ := fun j =>
  if j = i then 1 else 0

/-- Exact gradients of the four barycentric coordinates on a unit
Freudenthal tetrahedron; compare manuscript equation `chain-gradients`. -/
def barycentricGradient (t : TetIndex) : LocalVertex → SpatialIndex → ℚ :=
  let σ := tetPermutation t
  ![fun j => -coordinateUnit (σ 0) j,
    fun j => coordinateUnit (σ 0) j - coordinateUnit (σ 1) j,
    fun j => coordinateUnit (σ 1) j - coordinateUnit (σ 2) j,
    fun j => coordinateUnit (σ 2) j]

/-- One nonzero vector-valued global Bernstein coefficient. -/
structure MacroTerm where
  point : ScaledPoint
  component : SpatialIndex
  coefficient : ℚ

/-- Constructor using the manuscript's scaled point notation. -/
def macroTerm (x y z : ℤ) (component : SpatialIndex) (coefficient : ℚ) :
    MacroTerm where
  point := ![x, y, z]
  component := component
  coefficient := coefficient

/-- The eleven three-coefficient fields `w₁,...,w₁₁` from the manuscript.
Each point `(i,j,k)` denotes the global Bernstein basis function `B_ijk`. -/
def macroTerms : FieldIndex → TermIndex → MacroTerm :=
  ![![macroTerm 4 2 2 2 (-1), macroTerm 4 2 1 1 1, macroTerm 4 2 3 1 1],
    ![macroTerm 2 2 1 1 1, macroTerm 2 1 1 0 (-1), macroTerm 2 1 2 2 1],
    ![macroTerm 4 3 2 0 1, macroTerm 3 3 2 0 1, macroTerm 2 3 2 0 1],
    ![macroTerm 2 2 1 0 1, macroTerm 1 2 1 1 (-1), macroTerm 1 2 2 2 1],
    ![macroTerm 4 2 3 0 1, macroTerm 3 2 3 0 1, macroTerm 2 2 3 0 1],
    ![macroTerm 6 2 1 1 1, macroTerm 6 1 1 0 (-1), macroTerm 6 1 2 2 1],
    ![macroTerm 7 3 2 2 (-1), macroTerm 7 2 2 1 1, macroTerm 6 3 2 0 1],
    ![macroTerm 4 3 1 0 1, macroTerm 3 3 1 0 1, macroTerm 5 3 1 0 1],
    ![macroTerm 4 2 1 0 1, macroTerm 6 2 1 0 1, macroTerm 5 2 1 0 1],
    ![macroTerm 7 2 2 2 1, macroTerm 7 2 3 1 (-1), macroTerm 6 2 3 0 1],
    ![macroTerm 4 1 3 0 1, macroTerm 3 1 3 0 1, macroTerm 5 1 3 0 1]]

/-- Strict interior of the scaled patch `[0,8] × [0,4] × [0,4]`. -/
def IsPatchInterior (p : ScaledPoint) : Prop :=
  0 < p 0 ∧ p 0 < 8 ∧ 0 < p 1 ∧ p 1 < 4 ∧ 0 < p 2 ∧ p 2 < 4

/-- Every coefficient used by the eleven displayed fields is attached to an
interior Bernstein control point, the coefficient-level zero-boundary-trace
condition for the global basis. -/
theorem macroTerms_interior :
    ∀ w : FieldIndex, ∀ r : TermIndex, IsPatchInterior (macroTerms w r).point := by
  unfold IsPatchInterior
  decide +kernel

/-- Raise a cubic multi-index by the `i`th unit multi-index, represented in
the integer coordinates used by `scaledBarycentric`. -/
def raisedIndex (β : CubicMultiIndex) (i : LocalVertex) : LocalVertex → ℤ :=
  fun j => (β j).val + if j = i then 1 else 0

/-- Computable componentwise equality for local multi-indices.  Keeping this
test explicit avoids introducing a classical decision procedure for function
equality into the finite certificate. -/
def sameLocalIndex (α β : LocalVertex → ℤ) : Bool :=
  decide (∀ i : LocalVertex, α i = β i)

/-- The local vector Bernstein coefficient at a quartic multi-index. -/
def localVectorCoefficient (t : TetIndex) (w : FieldIndex)
    (α : LocalVertex → ℤ) (component : SpatialIndex) : ℚ :=
  ∑ r : TermIndex,
    if (macroTerms w r).component == component &&
        sameLocalIndex (scaledBarycentric t (macroTerms w r).point) α then
      (macroTerms w r).coefficient
    else 0

/-- Cubic Bernstein coefficient of the divergence obtained from
manuscript equation `bernstein-divergence`:

`4 * ∑ᵢ c_(β+εᵢ) · ∇λᵢ`.
-/
def divergenceCoefficient (t : TetIndex) (w : FieldIndex)
    (β : CubicMultiIndex) : ℚ :=
  4 * ∑ i : LocalVertex, ∑ component : SpatialIndex,
    localVectorCoefficient t w (raisedIndex β i) component *
      barycentricGradient t i component

/-- Total degree of a bounded cubic multi-index. -/
def cubicDegree (β : CubicMultiIndex) : Nat :=
  ∑ i : LocalVertex, (β i).val

/-- Number of nonzero barycentric entries. -/
def cubicSupportSize (β : CubicMultiIndex) : Nat :=
  ∑ i : LocalVertex, if β i = 0 then 0 else 1

/-- The cubic Bernstein indices carried by tetrahedron edges are precisely
the total-degree-three indices with at most two nonzero entries. -/
def IsEdgeCubicIndex (β : CubicMultiIndex) : Prop :=
  cubicDegree β = 3 ∧ cubicSupportSize β ≤ 2

/-- An explicit enumeration of all sixteen distinct edge-carried cubic
Bernstein indices. -/
def edgeCubicIndex : Fin 16 → CubicMultiIndex :=
  ![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3],
    ![2, 1, 0, 0], ![1, 2, 0, 0], ![2, 0, 1, 0], ![1, 0, 2, 0],
    ![2, 0, 0, 1], ![1, 0, 0, 2], ![0, 2, 1, 0], ![0, 1, 2, 0],
    ![0, 2, 0, 1], ![0, 1, 0, 2], ![0, 0, 2, 1], ![0, 0, 1, 2]]

/-- The enumeration contains only edge-carried total-degree-three indices. -/
theorem edgeCubicIndex_valid :
    ∀ i : Fin 16, IsEdgeCubicIndex (edgeCubicIndex i) := by
  unfold IsEdgeCubicIndex cubicDegree cubicSupportSize
  decide +kernel

/-- The sixteen-entry enumeration is complete.  This finite theorem prevents
the subsequent edge check from silently omitting a cubic edge coefficient. -/
theorem edgeCubicIndex_complete :
    ∀ β : CubicMultiIndex, IsEdgeCubicIndex β →
      ∃ i : Fin 16, ∀ j : LocalVertex, edgeCubicIndex i j = β j := by
  unfold IsEdgeCubicIndex cubicDegree cubicSupportSize
  decide +kernel

/-- Direct kernel evaluation of all `12 × 11 × 16` coefficient identities. -/
theorem displayedFields_edge_coefficients_zero :
    ∀ t : TetIndex, ∀ w : FieldIndex, ∀ i : Fin 16,
      divergenceCoefficient t w (edgeCubicIndex i) = 0 := by
  decide +kernel

/-- Every edge-carried cubic Bernstein coefficient of every displayed field
vanishes on every tetrahedron. -/
theorem displayedFields_all_edge_coefficients_zero
    (t : TetIndex) (w : FieldIndex) (β : CubicMultiIndex)
    (hβ : IsEdgeCubicIndex β) : divergenceCoefficient t w β = 0 := by
  obtain ⟨i, hi⟩ := edgeCubicIndex_complete β hβ
  have hfun : edgeCubicIndex i = β := funext hi
  rw [← hfun]
  exact displayedFields_edge_coefficients_zero t w i

/-- The six local tetrahedron edges, in lexicographic endpoint order. -/
def localEdge : Fin 6 → LocalVertex × LocalVertex :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The degree-three multi-index with exponents `3-r` and `r` at the two
endpoints of a local edge. -/
def localEdgeIndex (e : Fin 6) (r : Fin 4) : CubicMultiIndex := fun i =>
  if i = (localEdge e).1 then
    ⟨3 - r.val, by omega⟩
  else if i = (localEdge e).2 then r
  else 0

theorem localEdgeIndex_valid :
    ∀ e : Fin 6, ∀ r : Fin 4, IsEdgeCubicIndex (localEdgeIndex e r) := by
  unfold IsEdgeCubicIndex cubicDegree cubicSupportSize
  decide +kernel

/-- The univariate cubic Bernstein restriction represented by the four local
edge coefficients.  This is the restriction of manuscript equation
`bernstein-divergence` to the edge. -/
def divergenceEdgeRestriction (t : TetIndex) (w : FieldIndex)
    (e : Fin 6) (s : ℚ) : ℚ :=
  ∑ r : Fin 4,
    divergenceCoefficient t w (localEdgeIndex e r) *
      (Nat.choose 3 r.val : ℚ) * (1 - s) ^ (3 - r.val) * s ^ r.val

/-- The divergence trace of each displayed field vanishes identically on
every tetrahedron edge. -/
theorem displayedFields_divergenceEdgeRestriction_zero
    (t : TetIndex) (w : FieldIndex) (e : Fin 6) (s : ℚ) :
    divergenceEdgeRestriction t w e s = 0 := by
  simp only [divergenceEdgeRestriction]
  apply Finset.sum_eq_zero
  intro r _
  rw [displayedFields_all_edge_coefficients_zero t w (localEdgeIndex e r)
    (localEdgeIndex_valid e r)]
  ring

/-- Whether a scaled physical quartic control point belongs to a tetrahedron. -/
def pointInTet (t : TetIndex) (p : ScaledPoint) : Bool :=
  decide (∀ i : LocalVertex, 0 ≤ scaledBarycentric t p i)

/-- Thirty times the tetrahedron integral of the divergence, computed from
manuscript equation `bernstein-mean`. -/
def scaledDivergenceMean (t : TetIndex) (w : FieldIndex) : ℚ :=
  ∑ r : TermIndex,
    if pointInTet t (macroTerms w r).point then
      (macroTerms w r).coefficient *
        ∑ i : LocalVertex,
          if 0 < scaledBarycentric t (macroTerms w r).point i then
            barycentricGradient t i (macroTerms w r).component
          else 0
    else 0

/-- The exact element mean represented by the coefficient formula. -/
def divergenceMean (t : TetIndex) (w : FieldIndex) : ℚ :=
  scaledDivergenceMean t w / 30

/-- Embed the first eleven tetrahedron indices into all twelve tetrahedra. -/
def firstElevenTet (i : FieldIndex) : TetIndex :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

/-- The scaled first-eleven-mean matrix generated from the actual displayed
Bernstein control points and vector coefficients. -/
def bernsteinScaledMeanMatrix : Matrix FieldIndex FieldIndex ℚ := fun i j =>
  scaledDivergenceMean (firstElevenTet i) j

/-- The displayed Bernstein fields produce exactly the independently encoded
paper matrix.  This is the principal semantic transcription check. -/
theorem bernsteinScaledMeanMatrix_eq_quarticMeanMatrix :
    bernsteinScaledMeanMatrix =
      FreudenthalSVLean.QuarticMacro.quarticMeanMatrix := by
  decide +kernel

/-- Entrywise form of the exact mean identity `μ(w_j)_i = A_ij / 30`. -/
theorem divergenceMean_eq_matrix_div_thirty (i j : FieldIndex) :
    divergenceMean (firstElevenTet i) j =
      FreudenthalSVLean.QuarticMacro.quarticMeanMatrix i j / 30 := by
  change bernsteinScaledMeanMatrix i j / 30 = _
  rw [bernsteinScaledMeanMatrix_eq_quarticMeanMatrix]

/-- The twelve means of each displayed zero-boundary field sum to zero. -/
theorem scaledDivergenceMean_sum_zero :
    ∀ w : FieldIndex, ∑ t : TetIndex, scaledDivergenceMean t w = 0 := by
  decide +kernel

/-- Consequently the twelfth scaled mean is the negative sum of the first
eleven means. -/
theorem twelfth_scaledDivergenceMean :
    ∀ w : FieldIndex, scaledDivergenceMean 11 w =
      -∑ i : FieldIndex, scaledDivergenceMean (firstElevenTet i) w := by
  decide +kernel

end FreudenthalSVLean.QuarticBernstein
