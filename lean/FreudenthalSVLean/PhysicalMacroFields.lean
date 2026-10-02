import FreudenthalSVLean.QuarticReferenceLift
import FreudenthalSVLean.LatticeAffineTransport
import FreudenthalSVLean.SkeletonField

/-!
# Conforming quartic fields on arbitrary physical two-cube patches

For manuscript Lemma `macro` and equation `macro-scale`, a patch is fixed
by an integer lower corner and a coordinate permutation.  Its eleven
fields use the translated physical nodes of the reference nodal products.
They belong to the actual arbitrary-`N` homogeneous velocity space.
An identity of spatial polynomials identifies their restrictions with
the affine and scaled reference fields; off-patch support and mean/energy
recovery are proved in subsequent modules.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GridNodalSupport
open FreudenthalSVLean.NodalMesh
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticNodalRealization
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.QuarticMacroConformity
open FreudenthalSVLean.LatticeAffineTransport
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialScaling

noncomputable section

namespace FreudenthalSVLean.PhysicalMacroFields

def patchFits (N : ℕ) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ) : Prop :=
  ∀ j, 0 ≤ o j ∧ o j + upperCorner (π.symm j) ≤ (N : ℤ)

def termNodes (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (w : FieldIndex) (r : TermIndex) (a : LocalVertex) : Coordinate → ℤ :=
  affineNode π o (referenceNode (hostTet w r) a)

def termAmplitude (π : Equiv.Perm Coordinate) (w : FieldIndex) (r : TermIndex) : Space :=
  fun j => if (macroTerms w r).component = π.symm j then
    ((macroTerms w r).coefficient : ℝ) *
      ((BernsteinPolynomial.normalization (R := ℚ) 4 (hostExponent w r) : ℚ) : ℝ)
    else 0

def field (N : ℕ) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (w : FieldIndex) (amplitude : ℝ) : BrokenVelocity N :=
  amplitude • ∑ r : TermIndex,
    SkeletonField.vectorField N (termNodes π o w r) (hostExponent w r) (termAmplitude π w r)

theorem termNodes_inBox {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (w : FieldIndex) (r : TermIndex) (a : LocalVertex) :
    nodeInBox N (termNodes π o w r a) := by
  intro j
  have hn := reference_node_bounds (hostTet w r) a (π.symm j)
  have hj := hf j
  change 0 ≤ referenceNode (hostTet w r) a (π.symm j) + o j ∧
    referenceNode (hostTet w r) a (π.symm j) + o j ≤ (N : ℤ)
  change 0 ≤ referenceNode (hostTet w r) a (π.symm j) ∧
    referenceNode (hostTet w r) a (π.symm j) ≤ upperCorner (π.symm j) at hn
  omega

theorem termNodes_active {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (w : FieldIndex) (r : TermIndex) :
    SkeletonField.activeSkeleton N (termNodes π o w r) (hostExponent w r) := by
  intro j
  have hj := hf j
  obtain ⟨⟨a, ha, hn⟩, ⟨b, hb, hm⟩⟩ := boundary_node_certificate w r (π.symm j)
  constructor
  · refine ⟨a, ha, ?_⟩
    change referenceNode (hostTet w r) a (π.symm j) + o j ≠ 0
    omega
  · refine ⟨b, hb, ?_⟩
    change referenceNode (hostTet w r) b (π.symm j) + o j ≠ (N : ℤ)
    omega

/-- Each physical field is conforming and has homogeneous cube boundary
values, even when the chosen rectangular patch touches that boundary. -/
theorem field_mem_velocitySpace {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (w : FieldIndex) (amplitude : ℝ) :
    field N π o w amplitude ∈ velocitySpace N 4 := by
  apply (velocitySpace N 4).smul_mem amplitude
  apply (velocitySpace N 4).sum_mem
  intro r _
  apply SkeletonField.vectorField_mem_velocitySpace hN _ _
    (termNodes_inBox π o hf w r) (termNodes_active π o hf w r)
  rw [← Finsupp.degree_eq_sum, host_degree]

theorem patch_corner_bounds {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) (j : Coordinate) :
    0 ≤ affineNode π o (integerCorner i) j ∧ affineNode π o (integerCorner i) j < (N : ℤ) := by
  have hi := reference_corner_bounds i (π.symm j)
  have hj := hf j
  change 0 ≤ integerCorner i (π.symm j) ∧
    integerCorner i (π.symm j) < upperCorner (π.symm j) at hi
  simp only [affineNode]
  omega

def patchTet {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) : Tet N :=
  (fun j => ⟨(affineNode π o (integerCorner i) j).toNat, by
    have hb := patch_corner_bounds π o hf i j
    have he := Int.toNat_of_nonneg hb.1
    omega⟩, (tetEquiv i).trans π)

theorem patchTet_origin {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) :
    cellIntOrigin (patchTet π o hf i).1 = affineNode π o (integerCorner i) := by
  funext j
  exact Int.toNat_of_nonneg (patch_corner_bounds π o hf i j).1

theorem patchTet_corner {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) :
    cellOrigin (patchTet π o hf i).1 =
      (unitNormalize π (intPoint o)).symm (realCellCorner i) := by
  rw [← intPoint_cellIntOrigin, patchTet_origin, affineNode_intPoint, integerCorner_cast]

theorem patchTet_permutation {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) : (patchTet π o hf i).2 = (tetEquiv i).trans π := rfl

theorem patchTet_injective {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) : Function.Injective (patchTet π o hf) := by
  intro i j he
  apply reference_label_injective
  have hc := congrArg (fun t : Tet N => cellIntOrigin t.1) he
  rw [patchTet_origin, patchTet_origin] at hc
  have hc' := affineNode_injective π o hc
  have hp := congrArg (fun t : Tet N => t.2) he
  change (tetEquiv i).trans π = (tetEquiv j).trans π at hp
  have hp' : tetEquiv i = tetEquiv j := by
    apply Equiv.ext
    intro r
    have hr := Equiv.congr_fun hp r
    exact π.injective hr
  exact Prod.ext hc' (congrArg (fun e : Equiv.Perm Coordinate => e.toFun) hp')

/-- The whole-mesh polynomial field has the affine reference nodal formula
on every actual element, including all nonowners. -/
theorem field_representation {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (w : FieldIndex) (amplitude : ℝ) (t : Tet N) (j : Coordinate) :
    field N π o w amplitude t j = rescale (meshScale N) amplitude
      (pushVector π (intPoint o)
        (nodalVector w (t.2.trans π.symm) (inverseNode π o (cellIntOrigin t.1))) j) := by
  simp only [field, Pi.smul_apply, Finset.sum_apply, SkeletonField.vectorField,
    SkeletonField.scalarField, termNodes, meshNodalPolynomial, rescale, C_1, one_mul,
    nodalPolynomial_inverse_affine, pushVector, nodalVector, forward, map_sum,
    apply_ite, map_zero, map_mul, eval₂Hom_C,
    smul_eq_C_mul, termAmplitude]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : (macroTerms w r).component = π.symm j
  · simp only [hc, if_true, nodalProduct, map_mul, eval₂Hom_C, map_prod, map_pow]
    ring
  · simp only [hc, if_false, zero_mul, mul_zero]

/-- On each of the twelve actual owners, the physical field is exactly
the affine/scaled displayed reference field. -/
theorem field_on_patchTet {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (w : FieldIndex) (amplitude : ℝ) (i : TetIndex) (j : Coordinate) :
    field N π o w amplitude (patchTet π o hf i) j =
      rescale (meshScale N) amplitude (pushVector π (intPoint o) (realSpatialVector i w) j) := by
  rw [field_representation, patchTet_origin, inverseNode_affine]
  have hp : ((tetEquiv i).trans π).trans π.symm = tetEquiv i := by ext r; simp
  change rescale _ _ (pushVector π (intPoint o)
    (nodalVector w (((tetEquiv i).trans π).trans π.symm) (integerCorner i)) j) = _
  have hv : nodalVector w (tetEquiv i) (integerCorner i) = realSpatialVector i w :=
    funext (fun l => (realSpatialVector_eq_nodalVector i w l).symm)
  rw [hp, hv]

end FreudenthalSVLean.PhysicalMacroFields
