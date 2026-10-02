import FreudenthalSVLean.MeshIntersectionFaces
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Almost-everywhere disjointness of the actual tetrahedra

For the manuscript's mesh-integral and Sobolev identifications, every
actual barycentric face is a proper affine subspace and has zero Lebesgue
volume.  The structural common-point face theorem gives zero-volume
intersection of any two distinct actual elements.  Together with the
proved full cube coverage, this supplies the actual finite volume
partition for every positive mesh size.  No mesh intersection catalogue
is assumed.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.MeshIntersectionFaces

noncomputable section

namespace FreudenthalSVLean.MeshMeasurePartition

set_option backward.isDefEq.respectTransparency false

def coordinateAffine {N : ℕ} (t : Tet N) (r : Fin 3) : Space →ᵃ[ℝ] ℝ :=
  (meshScale N)⁻¹ • (LinearMap.proj (t.2 r) : Space →ₗ[ℝ] ℝ).toAffineMap -
    AffineMap.const ℝ Space (cellOrigin t.1 (t.2 r))

def barycentricAffine {N : ℕ} (t : Tet N) : Fin 4 → Space →ᵃ[ℝ] ℝ :=
  ![AffineMap.const ℝ Space 1 - coordinateAffine t 0,
    coordinateAffine t 0 - coordinateAffine t 1,
    coordinateAffine t 1 - coordinateAffine t 2,
    coordinateAffine t 2]

theorem barycentricAffine_apply {N : ℕ} (t : Tet N) (a : Fin 4) (x : Space) :
    barycentricAffine t a x = eval x (barycentric t a) := by
  fin_cases a <;> simp [barycentricAffine, coordinateAffine,
    FreudenthalMesh.barycentric, scaledBarycentric_eval,
    ChainGeometry.barycentric, ChainGeometry.chainCoordinate, Pi.smul_apply, smul_eq_mul]

def facePlane {N : ℕ} (t : Tet N) (a : Fin 4) : AffineSubspace ℝ Space :=
  (affineSpan ℝ ({0} : Set ℝ)).comap (barycentricAffine t a)

theorem mem_facePlane {N : ℕ} (t : Tet N) (a : Fin 4) (x : Space) :
    x ∈ facePlane t a ↔ eval x (barycentric t a) = 0 := by
  simp only [facePlane, AffineSubspace.mem_comap,
    AffineSubspace.mem_affineSpan_singleton, barycentricAffine_apply]

theorem facePlane_ne_top {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Fin 4) :
    facePlane t a ≠ ⊤ := by
  intro he
  have hm : vertex t a ∈ facePlane t a := by rw [he]; trivial
  have hz := (mem_facePlane t a (vertex t a)).mp hm
  rw [barycentric_vertex hN, if_pos rfl] at hz
  norm_num at hz

theorem facePlane_volume_zero {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Fin 4) :
    volume (facePlane t a : Set Space) = 0 :=
  Measure.addHaar_affineSubspace volume (facePlane t a) (facePlane_ne_top hN t a)

theorem tetrahedron_intersection_volume_zero {N : ℕ} (hN : 0 < N)
    (t u : Tet N) (hne : t ≠ u) : volume (tetrahedron t ∩ tetrahedron u) = 0 := by
  apply measure_mono_null (t := ⋃ a : Fin 4, (facePlane t a : Set Space))
  · intro x hx
    obtain ⟨a, ha⟩ := common_point_face t u hne x hx.1 hx.2
    exact mem_iUnion.mpr ⟨a, (mem_facePlane t a x).mpr ha⟩
  · exact measure_iUnion_null (fun a => facePlane_volume_zero hN t a)

/-- Closed element sets may share faces, but are pairwise disjoint in
Lebesgue volume for every positive mesh size. -/
theorem tetrahedra_pairwise_aeDisjoint {N : ℕ} (hN : 0 < N) :
    Pairwise (fun t u : Tet N => AEDisjoint volume (tetrahedron t) (tetrahedron u)) := by
  intro t u hne
  exact tetrahedron_intersection_volume_zero hN t u hne

end FreudenthalSVLean.MeshMeasurePartition
