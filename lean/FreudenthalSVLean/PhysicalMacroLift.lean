import FreudenthalSVLean.QuarticPatchCoverage

/-!
# Uniform physical quartic two-cube mean lifting

For manuscript Lemma `macro` and equation `macro-scale`, the fixed
reference coefficient inverse is applied to the actual translated,
permuted, scaled conforming fields on every admissible two-cube patch.
The mean equations are actual volume integrals; every nonowner carries
the zero polynomial.  The stability constant precedes all mesh sizes,
patches, coordinate permutations and mean inputs.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticSpatial
open FreudenthalSVLean.QuarticMacroConformity
open FreudenthalSVLean.QuarticReferenceLift
open FreudenthalSVLean.QuarticPatchCoverage
open FreudenthalSVLean.PhysicalMacroFields
open FreudenthalSVLean.LatticeAffineTransport
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.StarMeanRouting

noncomputable section

namespace FreudenthalSVLean.PhysicalMacroLift

set_option backward.isDefEq.respectTransparency false

def macroAmplitude (N : ℕ) : ℝ := ((meshScale N) ^ 2)⁻¹

def physicalBasis {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (w : FieldIndex) : velocitySpace N 4 :=
  ⟨field N π o w (macroAmplitude N), field_mem_velocitySpace hN π o hf w _⟩

def physicalCombination {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) : (FieldIndex → ℝ) →ₗ[ℝ] velocitySpace N 4 where
  toFun c := ∑ w : FieldIndex, c w • physicalBasis hN π o hf w
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def physicalLift {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) : CompatibleMeans →ₗ[ℝ] velocitySpace N 4 :=
  (physicalCombination hN π o hf).comp (weights.comp CompatibleMeans.subtype)

theorem physicalCombination_apply {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (c : FieldIndex → ℝ) :
    (physicalCombination hN π o hf c).val =
      ∑ w : FieldIndex, c w • field N π o w (macroAmplitude N) := by
  simp only [physicalCombination, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul, physicalBasis]

theorem field_divergence_on_patch {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (w : FieldIndex) (i : TetIndex) :
    divergence N (field N π o w (macroAmplitude N)) (patchTet π o hf i) =
      rescale (meshScale N) (macroAmplitude N * (meshScale N)⁻¹)
        (forward π (GridNodalSupport.intPoint o) (realSpatialDivergence i w)) := by
  have hv : field N π o w (macroAmplitude N) (patchTet π o hf i) =
      fun j => rescale (meshScale N) (macroAmplitude N)
        (pushVector π (GridNodalSupport.intPoint o) (realSpatialVector i w) j) :=
    funext (fun j => field_on_patchTet π o hf w _ i j)
  change PolynomialCalculus.polynomialDivergence
    (field N π o w (macroAmplitude N) (patchTet π o hf i)) = _
  rw [hv, divergence_rescale, divergence_pushVector]
  change rescale _ _ (forward π _ (∑ j : Coordinate, pderiv j (realSpatialVector i w j))) = _
  rw [← realSpatialDivergence_eq_derivatives]

/-- The physically scaled field has exactly its certified genuine mean
on each actual owner, without a coefficient-defined integral. -/
theorem field_mean_on_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (w : FieldIndex) (i : TetIndex) :
    tetIntegral hN (patchTet π o hf i)
      (divergence N (field N π o w (macroAmplitude N)) (patchTet π o hf i)) =
        (divergenceMean i w : ℝ) := by
  have hv : field N π o w (macroAmplitude N) (patchTet π o hf i) =
      fun j => rescale (meshScale N) ((meshScale N) ^ 2)⁻¹
        (pushVector π (GridNodalSupport.intPoint o) (realSpatialVector i w) j) :=
    funext (fun j => field_on_patchTet π o hf w _ i j)
  change (∫ x in tetrahedron (patchTet π o hf i), eval x
    (PolynomialCalculus.polynomialDivergence
      (field N π o w (macroAmplitude N) (patchTet π o hf i)))) = _
  rw [hv]
  simp only [tetrahedron, patchTet_permutation, patchTet_corner]
  rw [mean_preserving_divergence_scaling _ _ _ (meshScale_pos N hN),
    divergence_pushVector, affine_polynomial_integral]
  unfold PolynomialCalculus.polynomialDivergence
  rw [← realSpatialDivergence_eq_derivatives]
  exact QuarticVolume.spatialDivergence_volume_mean i w

theorem physicalCombination_means {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (c : FieldIndex → ℝ) (i : TetIndex) :
    tetIntegral hN (patchTet π o hf i)
      (divergence N (physicalCombination hN π o hf c).val (patchTet π o hf i)) =
        means (combinationLinear c) i := by
  rw [physicalCombination_apply, means_combination]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    field_mean_on_patch hN π o hf, smul_eq_mul]

/-- Fixed linear recovery of every compatible twelve-vector of actual
element means on every admissible physical patch. -/
theorem physicalLift_means {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (m : CompatibleMeans) (i : TetIndex) :
    tetIntegral hN (patchTet π o hf i)
      (divergence N (physicalLift hN π o hf m).val (patchTet π o hf i)) = m.val i := by
  change tetIntegral hN _ (divergence N (physicalCombination hN π o hf (weights m.val)).val _) = _
  rw [physicalCombination_means]
  exact congrFun (referenceLift_means m) i

theorem physicalCombination_zero_off_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (c : FieldIndex → ℝ)
    (t : Tet N) (ht : ¬ inPatch π o t) : (physicalCombination hN π o hf c).val t = 0 := by
  rw [physicalCombination_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, field_zero_off_patch π o _ _ t ht,
    smul_zero, Finset.sum_const_zero]

theorem patchTet_vertex {N : ℕ} (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (i : TetIndex) (a : Vertex) :
    vertex (patchTet π o hf i) a = meshScale N •
      (unitNormalize π (GridNodalSupport.intPoint o)).symm
        (chainVertex (tetEquiv i) (realCellCorner i) a) := by
  simp only [vertex, scaledVertex, patchTet_permutation, patchTet_corner, affine_vertex]

theorem normalize_scaled_patch_segment {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (i : TetIndex) (a b : Vertex) (s : ℝ) :
    unitNormalize π (GridNodalSupport.intPoint o)
      ((meshScale N)⁻¹ • segmentPoint (vertex (patchTet π o hf i) a)
        (vertex (patchTet π o hf i) b) s) =
      segmentPoint (chainVertex (tetEquiv i) (realCellCorner i) a)
        (chainVertex (tetEquiv i) (realCellCorner i) b) s := by
  have hh := (meshScale_pos N hN).ne'
  have he : (meshScale N)⁻¹ • segmentPoint (vertex (patchTet π o hf i) a)
        (vertex (patchTet π o hf i) b) s =
      (unitNormalize π (GridNodalSupport.intPoint o)).symm
        (segmentPoint (chainVertex (tetEquiv i) (realCellCorner i) a)
          (chainVertex (tetEquiv i) (realCellCorner i) b) s) := by
    rw [patchTet_vertex, patchTet_vertex, normalize_symm_segment]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, segmentPoint]
    field_simp [hh]
  rw [he, MeasurableEquiv.apply_symm_apply]

/-- Actual polynomial divergence vanishes on every whole local edge of
every mesh element, including elements outside the patch. -/
theorem field_all_edges_zero {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (w : FieldIndex)
    (t : Tet N) (a b : Vertex) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (field N π o w (macroAmplitude N)) t) = 0 := by
  classical
  by_cases ht : inPatch π o t
  · obtain ⟨i, rfl⟩ := patchTet_surjective_on_patch π o hf t ht
    rw [field_divergence_on_patch, rescale_eval, forward_eval,
      normalize_scaled_patch_segment hN π o hf, realSpatialDivergence_edge, mul_zero]
  · change eval _ (PolynomialCalculus.polynomialDivergence
      (field N π o w (macroAmplitude N) t)) = 0
    rw [field_zero_off_patch π o _ _ t ht]
    simp [PolynomialCalculus.polynomialDivergence]

theorem physicalLift_all_edges_zero {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (m : CompatibleMeans)
    (t : Tet N) (a b : Vertex) (s : ℝ) :
    eval (segmentPoint (vertex t a) (vertex t b) s)
      (divergence N (physicalLift hN π o hf m).val t) = 0 := by
  change eval _ (divergence N (physicalCombination hN π o hf (weights m.val)).val t) = 0
  rw [physicalCombination_apply]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_C_mul,
    map_mul, eval_C, field_all_edges_zero hN π o hf, mul_zero, Finset.sum_const_zero]

theorem physicalLift_zero_off_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (m : CompatibleMeans)
    (t : Tet N) (ht : ¬ inPatch π o t) : (physicalLift hN π o hf m).val t = 0 :=
  physicalCombination_zero_off_patch hN π o hf (weights m.val) t ht

theorem physicalLift_mean_zero_off_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (m : CompatibleMeans)
    (t : Tet N) (ht : ¬ inPatch π o t) :
    tetIntegral hN t (divergence N (physicalLift hN π o hf m).val t) = 0 := by
  change tetIntegral hN t (PolynomialCalculus.polynomialDivergence
    ((physicalLift hN π o hf m).val t)) = 0
  rw [physicalLift_zero_off_patch hN π o hf m t ht]
  simp [PolynomialCalculus.polynomialDivergence]

theorem field_energy_on_patch {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (w : FieldIndex) (i : TetIndex) :
    localEnergy (patchTet π o hf i) (field N π o w (macroAmplitude N) (patchTet π o hf i)) =
      ((meshScale N) ^ 3)⁻¹ * elementEnergy i (realSpatialVector i w) := by
  rw [localEnergy_eq_sum hN]
  simp only [field_on_patchTet, macroAmplitude, tetrahedron,
    patchTet_permutation, patchTet_corner]
  simp only [macro_derivative_energy_scaling _ _ _ (meshScale_pos N hN), ← Finset.mul_sum]
  rw [← unitGradientIntegral_eq_sum, affine_vector_energy]
  rfl

theorem field_global_energy {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate)
    (o : Coordinate → ℤ) (hf : patchFits N π o) (w : FieldIndex) :
    velocityEnergy (field N π o w (macroAmplitude N)) =
      ((meshScale N) ^ 3)⁻¹ * referenceEnergy (basis w) := by
  classical
  let S := Finset.univ.image (patchTet π o hf)
  have hs : (∑ t ∈ S, localEnergy t (field N π o w (macroAmplitude N) t)) =
      ∑ t : Tet N, localEnergy t (field N π o w (macroAmplitude N) t) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro t _ ht
    have hn : ¬ inPatch π o t := by
      intro hn
      obtain ⟨i, hi⟩ := patchTet_surjective_on_patch π o hf t hn
      exact ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [field_zero_off_patch π o _ _ t hn, localEnergy_zero]
  rw [velocityEnergy_eq_sum, ← hs]
  change (∑ t ∈ Finset.univ.image (patchTet π o hf),
    localEnergy t (field N π o w (macroAmplitude N) t)) = _
  rw [Finset.sum_image (fun _ _ _ _ he => patchTet_injective π o hf he)]
  simp only [field_energy_on_patch hN π o hf, ← Finset.mul_sum, referenceEnergy, basis]

/-- The constant is independent of mesh size, physical boundary contact,
translation, coordinate permutation and all prescribed mean data. -/
theorem physicalLift_uniform_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
      (hf : patchFits N π o) (m : CompatibleMeans),
      velocityEnergy (physicalLift hN π o hf m).val ≤
        C * ((meshScale N) ^ 3)⁻¹ * ∑ i : TetIndex, (m.val i) ^ 2 := by
  obtain ⟨C, hC, hc⟩ := weights_square_bound
  refine ⟨11 * basisEnergyBound * C, by positivity [basisEnergyBound_pos], ?_⟩
  intro N hN π o hf m
  change velocityEnergy (physicalCombination hN π o hf (weights m.val)).val ≤ _
  rw [physicalCombination_apply]
  have hscale : 0 ≤ ((meshScale N) ^ 3)⁻¹ := by positivity [meshScale_pos N hN]
  calc
    _ ≤ 11 * ∑ w : FieldIndex,
        velocityEnergy (weights m.val w • field N π o w (macroAmplitude N)) := by
      simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using
        velocityEnergy_sum hN (Finset.univ : Finset FieldIndex)
          (fun w => weights m.val w • field N π o w (macroAmplitude N))
    _ = 11 * ∑ w : FieldIndex,
        (weights m.val w) ^ 2 * (((meshScale N) ^ 3)⁻¹ * referenceEnergy (basis w)) := by
      simp only [velocityEnergy_smul, field_global_energy hN π o hf]
    _ ≤ 11 * ∑ w : FieldIndex,
        (weights m.val w) ^ 2 * (((meshScale N) ^ 3)⁻¹ * basisEnergyBound) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (basis_energy_le w) hscale) (sq_nonneg _))
    _ = (11 * basisEnergyBound * ((meshScale N) ^ 3)⁻¹) *
        ∑ w : FieldIndex, (weights m.val w) ^ 2 := by rw [← Finset.sum_mul]; ring
    _ ≤ (11 * basisEnergyBound * ((meshScale N) ^ 3)⁻¹) *
        (C * ∑ i : TetIndex, (m.val i) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hc m.val) (by positivity [basisEnergyBound_pos])
    _ = _ := by ring

/-- Complete discrete macro specification.  Its members are actual
homogeneous conforming velocities; all trace, mean and energy clauses use
the defined physical tetrahedra and genuine real-volume integrals. -/
structure MacroLiftSpec {N : ℕ} (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
    (hf : patchFits N π o) (R : CompatibleMeans →ₗ[ℝ] velocitySpace N 4) (C : ℝ) : Prop where
  means : ∀ m i, tetIntegral hN (patchTet π o hf i)
    (divergence N (R m).val (patchTet π o hf i)) = m.val i
  off_patch : ∀ m t, ¬ inPatch π o t → (R m).val t = 0
  zero_edges : ∀ m t a b s, eval (segmentPoint (vertex t a) (vertex t b) s)
    (divergence N (R m).val t) = 0
  energy : ∀ m, velocityEnergy (R m).val ≤
    C * ((meshScale N) ^ 3)⁻¹ * ∑ i : TetIndex, (m.val i) ^ 2

/-- One uniform constant is chosen before every actual mesh and patch;
each chosen operator is linear on the whole compatible-mean space. -/
theorem uniform_physical_macro_stage : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ)
      (hf : patchFits N π o), ∃ R : CompatibleMeans →ₗ[ℝ] velocitySpace N 4,
      MacroLiftSpec hN π o hf R C := by
  obtain ⟨C, hC, hb⟩ := physicalLift_uniform_energy
  refine ⟨C, hC, ?_⟩
  intro N hN π o hf
  refine ⟨physicalLift hN π o hf, ?_⟩
  exact ⟨physicalLift_means hN π o hf, physicalLift_zero_off_patch hN π o hf,
    physicalLift_all_edges_zero hN π o hf, hb N hN π o hf⟩

end FreudenthalSVLean.PhysicalMacroLift
