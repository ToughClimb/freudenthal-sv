import FreudenthalSVLean.PolynomialCalculus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Affine geometry of a Freudenthal coordinate-chain tetrahedron

The manuscript's mesh definition and equation `chain-gradients` describe
each translated unit tetrahedron by a permutation of three coordinates.
Here its vertices and barycentric polynomials are defined directly from
that permutation.  We prove the Kronecker vertex values, partition of unity,
and the actual partial derivatives of the barycentric polynomials.

This module concerns a single reference-size tetrahedron.  Mesh incidences,
global conformity, and metric scaling are separate obligations.
-/

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace FreudenthalSVLean.ChainGeometry

abbrev Coordinate := Fin 3
abbrev Vertex := Fin 4

variable {R : Type*} [CommRing R]

/-- The `i`th vertex of the translated coordinate chain. -/
def chainVertex (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (i : Vertex) : Coordinate → R := fun j =>
  o j + if (σ.symm j).val < i.val then 1 else 0

/-- Translated coordinate polynomial in the `r`th coordinate order. -/
def chainCoordinate (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (r : Coordinate) : MvPolynomial Coordinate R :=
  X (σ r) - C (o (σ r))

/-- The four actual affine barycentric polynomials. -/
def barycentric (σ : Equiv.Perm Coordinate) (o : Coordinate → R) :
    Vertex → MvPolynomial Coordinate R :=
  ![1 - chainCoordinate σ o 0,
    chainCoordinate σ o 0 - chainCoordinate σ o 1,
    chainCoordinate σ o 1 - chainCoordinate σ o 2,
    chainCoordinate σ o 2]

def coordinateUnit (i : Coordinate) : Coordinate → R := fun j =>
  if j = i then 1 else 0

/-- The gradient vectors claimed in manuscript equation `chain-gradients`. -/
def barycentricGradient (σ : Equiv.Perm Coordinate) : Vertex → Coordinate → R :=
  ![fun j => -coordinateUnit (σ 0) j,
    fun j => coordinateUnit (σ 0) j - coordinateUnit (σ 1) j,
    fun j => coordinateUnit (σ 1) j - coordinateUnit (σ 2) j,
    fun j => coordinateUnit (σ 2) j]

/-- The affine formulas have exactly the required vertex interpolation data. -/
theorem barycentric_vertex (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (i l : Vertex) :
    eval (chainVertex σ o l) (barycentric σ o i) = if i = l then 1 else 0 := by
  fin_cases i <;> fin_cases l <;>
    simp [barycentric, chainCoordinate, chainVertex]

/-- A point on the affine line joining two vertices.  No restriction on the
parameter is needed for the polynomial identity. -/
def segmentPoint (x y : Coordinate → R) (s : R) : Coordinate → R :=
  fun j => (1 - s) * x j + s * y j

theorem barycentric_segment (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (x y : Coordinate → R) (s : R) (i : Vertex) :
    eval (segmentPoint x y s) (barycentric σ o i) =
      (1 - s) * eval x (barycentric σ o i) + s * eval y (barycentric σ o i) := by
  fin_cases i <;> simp [barycentric, chainCoordinate, segmentPoint] <;> ring

/-- The actual barycentric coordinates on a vertex-to-vertex edge have no
components outside its two endpoints. -/
theorem barycentric_edge (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b : Vertex) (s : R) (i : Vertex) :
    eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) s)
      (barycentric σ o i) =
      (1 - s) * (if i = a then 1 else 0) + s * (if i = b then 1 else 0) := by
  rw [barycentric_segment, barycentric_vertex, barycentric_vertex]

/-- Affine barycentric formulas commute with a change of scalar ring. -/
theorem map_barycentric {S : Type*} [CommRing S] (f : R →+* S)
    (σ : Equiv.Perm Coordinate) (o : Coordinate → R) (i : Vertex) :
    map f (barycentric σ o i) = barycentric σ (fun j => f (o j)) i := by
  fin_cases i <;> simp [barycentric, chainCoordinate, map_sub]

/-- The affine polynomials form a partition of unity. -/
theorem barycentric_sum (σ : Equiv.Perm Coordinate) (o : Coordinate → R) :
    ∑ i : Vertex, barycentric σ o i = 1 := by
  simp [Fin.sum_univ_succ, barycentric]

/-- The encoded gradients are obtained by differentiating the actual affine
polynomials, not assumed as geometric input. -/
theorem pderiv_barycentric (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (i : Vertex) (j : Coordinate) :
    pderiv j (barycentric σ o i) = C (barycentricGradient σ i j) := by
  obtain ⟨r, rfl⟩ := σ.surjective j
  fin_cases i <;> fin_cases r <;>
    simp [barycentric, chainCoordinate, barycentricGradient, coordinateUnit,
      pderiv_X, map_sub, σ.injective.eq_iff]

/-- The four barycentric gradients sum to zero. -/
theorem barycentricGradient_sum (σ : Equiv.Perm Coordinate) (j : Coordinate) :
    ∑ i : Vertex, barycentricGradient (R := R) σ i j = 0 := by
  simp [Fin.sum_univ_succ, barycentricGradient]

/-- Euclidean directional derivative of a barycentric coordinate on a real
tetrahedron, connected to the generic Fréchet-calculus theorem. -/
theorem fderiv_barycentric (σ : Equiv.Perm Coordinate) (o x : Coordinate → ℝ)
    (i : Vertex) (j : Coordinate) :
    fderiv ℝ (fun y => eval y (barycentric σ o i)) x (Pi.single j 1) =
      barycentricGradient σ i j := by
  rw [PolynomialCalculus.fderiv_eval_single, pderiv_barycentric, eval_C]

end FreudenthalSVLean.ChainGeometry
