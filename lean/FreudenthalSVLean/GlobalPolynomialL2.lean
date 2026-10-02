import FreudenthalSVLean.MeshMeasurePartition
import FreudenthalSVLean.FixedMeshRightInverse

/-!
# Actual global L2 representatives and integral energies

For the manuscript's pressure norm and global gradient-energy statements,
broken spatial polynomials define actual functions on Euclidean space by
finite indicator assembly and zero extension.  Shared-face multiplicity
affects only the proved volume-zero mesh interfaces.  Genuine integration
identifies their means and squared L2 norms with the defined element sums.
The actual L2 representation is injective.  Applying it to polynomial
gradient components identifies the gradient energy as a sum of true L2
norms, but does not yet prove those components are weak derivatives.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshMeasurePartition
open FreudenthalSVLean.PolynomialL2
open FreudenthalSVLean.PolynomialInverseEstimate
open FreudenthalSVLean.FixedMeshRightInverse
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.GlobalPolynomialL2

set_option backward.isDefEq.respectTransparency false

def piecewisePressure {N : ℕ} (q : BrokenPressure N) (x : Space) : ℝ :=
  ∑ t : Tet N, (tetrahedron t).indicator (fun y => eval y (q t)) x

theorem piecewisePressure_zero_off_cube {N : ℕ} (hN : 0 < N)
    (q : BrokenPressure N) (x : Space) (hx : x ∉ cube) : piecewisePressure q x = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  exact indicator_of_notMem (fun ht => hx (tetrahedron_subset_cube hN t ht)) _

theorem ae_unique_owner {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x : Space ∂volume, ∀ t u : Tet N,
      x ∈ tetrahedron t → x ∈ tetrahedron u → t = u := by
  classical
  apply ae_all_iff.mpr
  intro t
  apply ae_all_iff.mpr
  intro u
  by_cases he : t = u
  · exact Filter.Eventually.of_forall (fun _ _ _ => he)
  · have hp := measure_eq_zero_iff_ae_notMem.mp
      (tetrahedron_intersection_volume_zero hN t u he)
    filter_upwards [hp] with x hx
    intro ht hu
    exact False.elim (hx ⟨ht, hu⟩)

theorem piecewisePressure_on_unique {N : ℕ} (q : BrokenPressure N)
    (t : Tet N) (x : Space) (ht : x ∈ tetrahedron t)
    (hu : ∀ u, x ∈ tetrahedron u → u = t) : piecewisePressure q x = eval x (q t) := by
  classical
  rw [piecewisePressure, Finset.sum_eq_single t]
  · exact indicator_of_mem ht _
  · intro u _ hut
    exact indicator_of_notMem (fun hx => hut (hu u hx)) _
  · simp

def piecewisePressureLinear (N : ℕ) : BrokenPressure N →ₗ[ℝ] (Space → ℝ) where
  toFun := piecewisePressure
  map_add' q r := by
    funext x
    change piecewisePressure (q + r) x = piecewisePressure q x + piecewisePressure r x
    simp only [piecewisePressure, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : x ∈ tetrahedron t <;> simp [ht]
  map_smul' c q := by
    funext x
    simp only [piecewisePressure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : x ∈ tetrahedron t <;> simp [ht]

theorem indicator_integrable {N : ℕ} (hN : 0 < N)
    (q : BrokenPressure N) (t : Tet N) :
    Integrable ((tetrahedron t).indicator (fun x => eval x (q t))) := by
  apply (integrable_indicator_iff (tetrahedron_isCompact hN t).measurableSet).mpr
  exact (continuous_eval _).continuousOn.integrableOn_compact
    (μ := volume) (tetrahedron_isCompact hN t)

theorem square_indicator_integrable {N : ℕ} (hN : 0 < N)
    (q : BrokenPressure N) (t : Tet N) :
    Integrable ((tetrahedron t).indicator (fun x => (eval x (q t)) ^ 2)) := by
  apply (integrable_indicator_iff (tetrahedron_isCompact hN t).measurableSet).mpr
  exact ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
    (μ := volume) (tetrahedron_isCompact hN t)

theorem piecewisePressure_integrable {N : ℕ} (hN : 0 < N)
    (q : BrokenPressure N) : Integrable (piecewisePressure q) :=
  integrable_finsetSum Finset.univ (fun t _ => indicator_integrable hN q t)

theorem piecewisePressure_mean {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    (∫ x, piecewisePressure q x) = ∑ t : Tet N, StarMeanRouting.tetIntegral hN t (q t) := by
  simp only [piecewisePressure]
  rw [integral_finsetSum _ (fun t _ => indicator_integrable hN q t)]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_indicator (tetrahedron_isCompact hN t).measurableSet

theorem piecewisePressure_square_ae {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    (fun x => (piecewisePressure q x) ^ 2) =ᵐ[volume]
      (fun x => ∑ t : Tet N, (tetrahedron t).indicator (fun y => (eval y (q t)) ^ 2) x) := by
  classical
  filter_upwards [ae_unique_owner hN] with x hx
  by_cases ho : ∃ t : Tet N, x ∈ tetrahedron t
  · obtain ⟨t, ht⟩ := ho
    rw [piecewisePressure_on_unique q t x ht (fun u hu => (hx t u ht hu).symm)]
    rw [Finset.sum_eq_single t]
    · exact (indicator_of_mem ht (fun y : Space => (eval y (q t)) ^ 2)).symm
    · intro u _ hut
      exact indicator_of_notMem (fun hu => hut (hx u t hu ht)) _
    · simp
  · have hn (t : Tet N) : x ∉ tetrahedron t := fun ht => ho ⟨t, ht⟩
    simp [piecewisePressure, hn]

theorem piecewisePressure_square_integrable {N : ℕ} (hN : 0 < N)
    (q : BrokenPressure N) : Integrable (fun x => (piecewisePressure q x) ^ 2) :=
  (integrable_finsetSum Finset.univ (fun t _ => square_indicator_integrable hN q t)).congr
    (piecewisePressure_square_ae hN q).symm

theorem piecewisePressure_square_integral {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    (∫ x, (piecewisePressure q x) ^ 2) = pressureEnergy q := by
  rw [integral_congr_ae (piecewisePressure_square_ae hN q),
    integral_finsetSum _ (fun t _ => square_indicator_integrable hN q t), pressureEnergy]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_indicator (tetrahedron_isCompact hN t).measurableSet

theorem piecewisePressure_memLp {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    MemLp (piecewisePressure q) 2 volume :=
  (memLp_two_iff_integrable_sq (piecewisePressure_integrable hN q).aestronglyMeasurable).mpr
    (piecewisePressure_square_integrable hN q)

def toMeshL2 {N : ℕ} (hN : 0 < N) : BrokenPressure N →ₗ[ℝ] Lp ℝ 2 (volume : Measure Space) where
  toFun q := (piecewisePressure_memLp hN q).toLp (piecewisePressure q)
  map_add' q r := by
    have he := (piecewisePressureLinear N).map_add q r
    exact (MemLp.toLp_congr (piecewisePressure_memLp hN (q + r))
      ((piecewisePressure_memLp hN q).add (piecewisePressure_memLp hN r))
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_add (piecewisePressure_memLp hN q) (piecewisePressure_memLp hN r))
  map_smul' c q := by
    have he := (piecewisePressureLinear N).map_smul c q
    exact (MemLp.toLp_congr (piecewisePressure_memLp hN (c • q))
      ((piecewisePressure_memLp hN q).const_smul c)
      (Filter.Eventually.of_forall (congrFun he))).trans
      (MemLp.toLp_const_smul c (piecewisePressure_memLp hN q))

theorem toMeshL2_norm_square {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    ‖toMeshL2 hN q‖ ^ 2 = pressureEnergy q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, (piecewisePressure q x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (piecewisePressure_memLp hN q)] with x hx
      simp [toMeshL2, hx, pow_two]
    _ = _ := piecewisePressure_square_integral hN q

theorem pressureEnergy_eq_zero_iff {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    pressureEnergy q = 0 ↔ q = 0 := by
  constructor
  · intro he
    have ht (t : Tet N) : (∫ x in tetrahedron t, (eval x (q t)) ^ 2) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun u _ => integral_nonneg (fun _ => sq_nonneg _))).mp he t (Finset.mem_univ t)
    funext t
    have hp := pullback_square_integral t.2 (cellOrigin t.1) (meshScale N)
      (meshScale_pos N hN) (q t)
    change (∫ x in tetrahedron t, (eval x (q t)) ^ 2) =
      (meshScale N) ^ 3 * referenceSquareIntegral
        (pullback t.2 (cellOrigin t.1) (meshScale N) (q t)) at hp
    rw [ht t] at hp
    have hr := (mul_eq_zero.mp hp.symm).resolve_left
      (pow_ne_zero 3 (meshScale_pos N hN).ne')
    have hz := (referenceSquareIntegral_eq_zero_iff _).mp hr
    apply pullback_injective t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN).ne'
    simpa only [pullback, Pi.zero_apply, map_zero] using hz
  · rintro rfl
    simp [pressureEnergy]

theorem toMeshL2_injective {N : ℕ} (hN : 0 < N) : Function.Injective (toMeshL2 hN) := by
  intro q r he
  have hz : toMeshL2 hN (q - r) = 0 := by rw [map_sub, he, sub_self]
  have hp : pressureEnergy (q - r) = 0 := by rw [← toMeshL2_norm_square hN, hz]; simp
  exact sub_eq_zero.mp ((pressureEnergy_eq_zero_iff hN (q - r)).mp hp)

theorem velocityEnergy_eq_sum_L2 {N : ℕ} (hN : 0 < N) (v : BrokenVelocity N) :
    velocityEnergy v = ∑ j : Fin 3, ∑ i : Fin 3,
      ‖toMeshL2 hN (fun t => pderiv i (v t j))‖ ^ 2 := by
  simp only [toMeshL2_norm_square, pressureEnergy]
  rw [velocityEnergy_eq_sum]
  simp only [localEnergy_eq_sum hN]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

end FreudenthalSVLean.GlobalPolynomialL2
