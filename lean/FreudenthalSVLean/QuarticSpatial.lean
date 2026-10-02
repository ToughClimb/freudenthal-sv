import FreudenthalSVLean.QuarticPolynomial
import Mathlib.Data.Real.Basic

/-!
# Actual spatial edge traces of the quartic macro fields

The manuscript's quartic two-cube lemma requires zero divergence on every
tetrahedron edge.  Here the previously certified control points are
substituted into the actual affine barycentric coordinates of the twelve
tetrahedra.  We prove zero restriction on an arbitrary real edge parameter,
and identify spatial polynomial divergence with the trace of the actual
Fréchet derivative.

This module supplies the local differentiation/edge-trace bridge.
`QuarticVolume` proves the genuine volume means; `QuarticMacroConformity`
proves all-point conformity and exterior zero trace; `PhysicalMacroLift`
proves the uniform actual gradient-energy bound.  The weak Sobolev
identification remains a separate obligation.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticPolynomial

noncomputable section

namespace FreudenthalSVLean.QuarticSpatial

theorem chainPermutation_bijective :
    ∀ t : LocalTetIndex, Function.Bijective (chainPermutation t) := by
  decide +kernel

def tetEquiv (t : TetIndex) : Equiv.Perm SpatialIndex :=
  Equiv.ofBijective (tetPermutation t) (chainPermutation_bijective (localTetIndex t))

def cellCorner (t : TetIndex) : SpatialIndex → ℚ :=
  fun j => (scaledCellCorner t j : ℚ) / 4

def realCellCorner (t : TetIndex) : SpatialIndex → ℝ :=
  fun j => (cellCorner t j : ℝ)

def tetBarycentric (t : TetIndex) : LocalVertex → MvPolynomial SpatialIndex ℚ :=
  ChainGeometry.barycentric (tetEquiv t) (cellCorner t)

theorem tetGradient_eq_table (t : TetIndex) (i : LocalVertex) (j : SpatialIndex) :
    ChainGeometry.barycentricGradient (R := ℚ) (tetEquiv t) i j =
      barycentricGradient t i j := by
  rfl

theorem pderiv_tetBarycentric (t : TetIndex) (i : LocalVertex) (j : SpatialIndex) :
    pderiv j (tetBarycentric t i) = C (barycentricGradient t i j) := by
  exact ChainGeometry.pderiv_barycentric (tetEquiv t) (cellCorner t) i j

/-- Actual spatial vector components on each unit-size tetrahedron. -/
def spatialVector (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    MvPolynomial SpatialIndex ℚ :=
  eval₂Hom C (tetBarycentric t) (localVectorPolynomial t w j)

def spatialDivergence (t : TetIndex) (w : FieldIndex) : MvPolynomial SpatialIndex ℚ :=
  ∑ j : SpatialIndex, pderiv j (spatialVector t w j)

theorem spatialDivergence_eq_substitution (t : TetIndex) (w : FieldIndex) :
    spatialDivergence t w = eval₂Hom C (tetBarycentric t) (localDivergencePolynomial t w) := by
  exact BernsteinPolynomial.spatial_divergence_eq_substitution
    (tetBarycentric t) (barycentricGradient t) (pderiv_tetBarycentric t)
    (localVectorPolynomial t w)

def realSpatialVector (t : TetIndex) (w : FieldIndex) (j : SpatialIndex) :
    MvPolynomial SpatialIndex ℝ :=
  map (Rat.castHom ℝ) (spatialVector t w j)

def realSpatialDivergence (t : TetIndex) (w : FieldIndex) :
    MvPolynomial SpatialIndex ℝ := map (Rat.castHom ℝ) (spatialDivergence t w)

theorem realSpatialDivergence_eq_substitution (t : TetIndex) (w : FieldIndex) :
    realSpatialDivergence t w = eval₂Hom C
      (ChainGeometry.barycentric (tetEquiv t) (realCellCorner t))
      (map (Rat.castHom ℝ) (localDivergencePolynomial t w)) := by
  simp only [realSpatialDivergence, spatialDivergence_eq_substitution,
    coe_eval₂Hom, map_eval₂, Function.comp_def]
  congr 1
  funext i
  exact ChainGeometry.map_barycentric (Rat.castHom ℝ) (tetEquiv t) (cellCorner t) i

theorem realSpatialDivergence_eq_derivatives (t : TetIndex) (w : FieldIndex) :
    realSpatialDivergence t w = ∑ j : SpatialIndex, pderiv j (realSpatialVector t w j) := by
  simp [realSpatialDivergence, spatialDivergence, realSpatialVector, pderiv_map]

/-- The actual real divergence is the trace of the field's Fréchet derivative. -/
theorem realSpatialDivergence_eval (t : TetIndex) (w : FieldIndex) (x : SpatialIndex → ℝ) :
    eval x (realSpatialDivergence t w) =
      ∑ j : SpatialIndex,
        fderiv ℝ (fun y => eval y (realSpatialVector t w j)) x (Pi.single j 1) := by
  rw [realSpatialDivergence_eq_derivatives]
  exact PolynomialCalculus.polynomialDivergence_eval (realSpatialVector t w) x

/-- The rational certificate implies zero actual evaluation over `ℝ` on
any barycentric skeleton with at most two vertices. -/
theorem realLocalDivergence_eval_zero_on_edge (t : TetIndex) (w : FieldIndex)
    (s : Finset LocalVertex) (hs : s.card ≤ 2) (x : LocalVertex → ℝ)
    (hx : ∀ j, j ∉ s → x j = 0) :
    eval x (map (Rat.castHom ℝ) (localDivergencePolynomial t w)) = 0 := by
  apply PolynomialSkeletonTrace.eval_zero_on_edge _ 3
    ((localDivergencePolynomial_homogeneous t w).map (Rat.castHom ℝ)) s hs x hx
  intro α hd hα
  rw [coeff_map, localDivergencePolynomial_edge_monomial_coefficients_zero t w α hd hα]
  simp

/-- Zero restriction of the actual spatial divergence to every real
tetrahedron edge; the edge parameter is arbitrary, not sampled. -/
theorem realSpatialDivergence_edge (t : TetIndex) (w : FieldIndex)
    (a b : LocalVertex) (s : ℝ) :
    eval (ChainGeometry.segmentPoint
      (ChainGeometry.chainVertex (tetEquiv t) (realCellCorner t) a)
      (ChainGeometry.chainVertex (tetEquiv t) (realCellCorner t) b) s)
      (realSpatialDivergence t w) = 0 := by
  let x := ChainGeometry.segmentPoint
    (ChainGeometry.chainVertex (tetEquiv t) (realCellCorner t) a)
    (ChainGeometry.chainVertex (tetEquiv t) (realCellCorner t) b) s
  change eval x (realSpatialDivergence t w) = 0
  rw [realSpatialDivergence_eq_substitution, coe_eval₂Hom, eval_eval₂]
  have hC : (eval x).comp (C : ℝ →+* MvPolynomial SpatialIndex ℝ) = RingHom.id ℝ := by
    ext c
    simp
  rw [hC, eval₂_id]
  apply realLocalDivergence_eval_zero_on_edge t w {a, b} Finset.card_le_two
  intro i hi
  have hia : i ≠ a := fun h => hi (by simp [h])
  have hib : i ≠ b := fun h => hi (by simp [h])
  simp [x, ChainGeometry.barycentric_edge, hia, hib]

end FreudenthalSVLean.QuarticSpatial
