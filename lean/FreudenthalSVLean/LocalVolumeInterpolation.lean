import FreudenthalSVLean.BarycentricInterpolationEstimate

/-!
# Actual local H1 estimates for volume nodal interpolation

For manuscript Lemma `means` and equation `SZ`, the true nodal volume
averages are bounded on a fixed radius-2h neighborhood of each element.
The anchor is selected from mesh geometry before the input: a boundary
vertex when one exists, otherwise vertex zero.  Interior elements are
normalized by the actual neighborhood mean; boundary elements by zero.
Both cases give uniform coefficient and local integral estimates from
the proved box Poincare bounds and explicit barycentric calculus.
Global overlap assembly and the continuous divergence inverse are
separate obligations.
-/

open scoped BigOperators Topology Classical
open MvPolynomial MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.TranslatedBoxH1Estimate
open FreudenthalSVLean.BoundaryHalfBoxGeometry
open FreudenthalSVLean.LinearNodalInterpolation
open FreudenthalSVLean.VolumeNodalInterpolation
open FreudenthalSVLean.MeshAveragingBoxes
open FreudenthalSVLean.BarycentricInterpolationEstimate

noncomputable section

namespace FreudenthalSVLean.LocalVolumeInterpolation

set_option backward.isDefEq.respectTransparency false

def boundaryElement {N : ℕ} (t : Tet N) : Prop :=
  ∃ a : Fin 4, ¬ interiorNode (gridVertexOfTet t a)

def boxAnchor {N : ℕ} (t : Tet N) : Fin 4 :=
  if ht : boundaryElement t then Classical.choose ht else 0

theorem boxAnchor_boundary {N : ℕ} (t : Tet N) (ht : boundaryElement t) :
    ¬ interiorNode (gridVertexOfTet t (boxAnchor t)) := by
  simp only [boxAnchor, dif_pos ht]
  exact Classical.choose_spec ht

def normalization {N : ℕ} (f : Space → ℝ) (t : Tet N) : ℝ :=
  if boundaryElement t then 0 else elementMean f t (boxAnchor t)

def localCoefficient {N : ℕ} (f : Space → ℝ) (t : Tet N) (a : Fin 4) : ℝ :=
  if interiorNode (gridVertexOfTet t a) then nodeMean f (gridVertexOfTet t a) else 0

def scalarInterpolation {N : ℕ} (f : Space → ℝ) (t : Tet N) : MvPolynomial (Fin 3) ℝ :=
  affineCombination t (localCoefficient f t)

def localGradientIntegral {N : ℕ} (g : Fin 3 → Space → ℝ) (t : Tet N) : ℝ :=
  ∑ j : Fin 3, ∫ x in elementBox t (boxAnchor t), (g j x) ^ 2

theorem localGradientIntegral_nonneg {N : ℕ} (g : Fin 3 → Space → ℝ) (t : Tet N) :
    0 ≤ localGradientIntegral g t :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

theorem volumeInterpolation_scalar {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space) (t : Tet N) (j : Fin 3) :
    (volumeNodalInterpolation hN v).val t j = scalarInterpolation (v j).val.1 t := by
  rw [volumeNodalInterpolation_on_element]
  rfl

theorem local_coefficient_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) (a : Fin 4) :
    meshScale N * (localCoefficient f t a - normalization f t) ^ 2 ≤
      36 * localGradientIntegral g t := by
  have hG := localGradientIntegral_nonneg g t
  by_cases ht : boundaryElement t
  · simp only [normalization, if_pos ht, sub_zero]
    by_cases ha : interiorNode (gridVertexOfTet t a)
    · simp only [localCoefficient, if_pos ha]
      exact boundary_nodeMean_bound hN hf t (boxAnchor t) a (boxAnchor_boundary t ht)
    · simp only [localCoefficient, if_neg ha, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
  · have ha : interiorNode (gridVertexOfTet t a) := by
      by_contra hna
      exact ht ⟨a, hna⟩
    simp only [normalization, if_neg ht, localCoefficient, if_pos ha]
    have hb := nodeMean_difference_bound hN (inH1ZeroCube_has_smoothApproximation hf)
      t (boxAnchor t) a
    exact hb.trans (by change 6 * localGradientIntegral g t ≤ 36 * localGradientIntegral g t; linarith)

theorem local_coefficient_sum_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    meshScale N * (∑ a : Fin 4, (localCoefficient f t a - normalization f t) ^ 2) ≤
      144 * localGradientIntegral g t := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => local_coefficient_bound hN hf t a)
  calc
    _ ≤ ∑ _a : Fin 4, 36 * localGradientIntegral g t := by
      simpa only [← Finset.mul_sum] using ht
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem local_normalized_value_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    (∫ x in elementBox t (boxAnchor t), (f x - normalization f t) ^ 2) ≤
      288 * (meshScale N) ^ 2 * localGradientIntegral g t := by
  have hh := meshScale_pos N hN
  have hG := localGradientIntegral_nonneg g t
  by_cases ht : boundaryElement t
  · simp only [normalization, if_pos ht, sub_zero]
    have hb := boundary_centered_box_poincare hf (by positivity : 0 < 2 * meshScale N)
      (gridPoint (gridVertexOfTet t (boxAnchor t)))
      (not_interiorNode_boundary hN (boxAnchor_boundary t ht))
    simp only [← neg_mul] at hb
    change (∫ x in elementBox t (boxAnchor t), (f x) ^ 2) ≤
      72 * (2 * meshScale N) ^ 2 * localGradientIntegral g t at hb
    calc
      _ ≤ _ := hb
      _ = _ := by ring
  · simp only [normalization, if_neg ht]
    have hb := weak_translated_box_mean_poincare (inH1ZeroCube_has_smoothApproximation hf)
      (by linarith : -2 * meshScale N < 2 * meshScale N)
      (gridPoint (gridVertexOfTet t (boxAnchor t)))
    change (∫ x in elementBox t (boxAnchor t), (f x - elementMean f t (boxAnchor t)) ^ 2) ≤
      3 * (2 * meshScale N - -2 * meshScale N) ^ 2 * localGradientIntegral g t at hb
    calc
      _ ≤ _ := hb
      _ = 48 * (meshScale N) ^ 2 * localGradientIntegral g t := by ring
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (meshScale N)) hG]

theorem local_interpolation_gradient_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    (∑ i : Fin 3, ∫ x in tetrahedron t,
      (eval x (pderiv i (scalarInterpolation f t))) ^ 2) ≤
        288 * localGradientIntegral g t := by
  have ht := affineCombination_gradient_integral_bound hN t
    (fun a => localCoefficient f t a - normalization f t)
  simp only [affineCombination_partial_shift] at ht
  calc
    _ ≤ 2 * (meshScale N * ∑ a : Fin 4,
        (localCoefficient f t a - normalization f t) ^ 2) := by
      simpa only [scalarInterpolation, mul_assoc] using ht
    _ ≤ 2 * (144 * localGradientIntegral g t) :=
      mul_le_mul_of_nonneg_left (local_coefficient_sum_bound hN hf t) (by norm_num)
    _ = _ := by ring

theorem local_interpolation_center_value_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    (∫ x in tetrahedron t, (eval x (scalarInterpolation f t) - normalization f t) ^ 2) ≤
      96 * (meshScale N) ^ 2 * localGradientIntegral g t := by
  have ht := affineCombination_value_integral_bound hN t
    (fun a => localCoefficient f t a - normalization f t)
  rw [affineCombination_shift] at ht
  simp only [map_sub, eval_C] at ht
  calc
    _ ≤ (2 / 3 : ℝ) * (meshScale N) ^ 2 *
        (meshScale N * ∑ a : Fin 4, (localCoefficient f t a - normalization f t) ^ 2) := by
      calc
        _ ≤ (2 / 3 : ℝ) * (meshScale N) ^ 3 *
            ∑ a : Fin 4, (localCoefficient f t a - normalization f t) ^ 2 := ht
        _ = _ := by ring
    _ ≤ (2 / 3 : ℝ) * (meshScale N) ^ 2 * (144 * localGradientIntegral g t) :=
      mul_le_mul_of_nonneg_left (local_coefficient_sum_bound hN hf t) (by positivity)
    _ = _ := by ring

theorem local_normalized_element_value_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    (∫ x in tetrahedron t, (f x - normalization f t) ^ 2) ≤
      288 * (meshScale N) ^ 2 * localGradientIntegral g t := by
  let : IsFiniteMeasure (volume.restrict (elementBox t (boxAnchor t))) :=
    isFiniteMeasure_restrict.mpr
      (isCompact_Icc : IsCompact (elementBox t (boxAnchor t))).measure_ne_top
  have hi : IntegrableOn (fun x => (f x - normalization f t) ^ 2)
      (elementBox t (boxAnchor t)) := by
    simpa only [Pi.sub_apply] using!
      ((hf.1.1.restrict (elementBox t (boxAnchor t))).sub
        (memLp_const (normalization f t))).integrable_sq
  exact (setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (tetrahedron_subset_elementBox hN t (boxAnchor t)))).trans
      (local_normalized_value_bound hN hf t)

theorem local_interpolation_error_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g) (t : Tet N) :
    (∫ x in tetrahedron t, (f x - eval x (scalarInterpolation f t)) ^ 2) ≤
      768 * (meshScale N) ^ 2 * localGradientIntegral g t := by
  let : IsFiniteMeasure (volume.restrict (tetrahedron t)) :=
    isFiniteMeasure_restrict.mpr (tetrahedron_isCompact hN t).measure_ne_top
  have hp : MemLp (fun x => eval x (scalarInterpolation f t)) 2
      (volume.restrict (tetrahedron t)) := by
    apply (memLp_two_iff_integrable_sq (continuous_eval _).aestronglyMeasurable.restrict).mpr
    exact ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
      (tetrahedron_isCompact hN t)
  have hiErr : IntegrableOn (fun x => (f x - eval x (scalarInterpolation f t)) ^ 2)
      (tetrahedron t) := by
    simpa only [Pi.sub_apply] using! ((hf.1.1.restrict (tetrahedron t)).sub hp).integrable_sq
  have hiF : IntegrableOn (fun x => (f x - normalization f t) ^ 2) (tetrahedron t) := by
    simpa only [Pi.sub_apply] using!
      ((hf.1.1.restrict (tetrahedron t)).sub (memLp_const (normalization f t))).integrable_sq
  have hiJ : IntegrableOn (fun x => (eval x (scalarInterpolation f t) - normalization f t) ^ 2)
      (tetrahedron t) := by
    simpa only [Pi.sub_apply] using! (hp.sub (memLp_const (normalization f t))).integrable_sq
  have hiSum : IntegrableOn (fun x => (f x - normalization f t) ^ 2 +
      (eval x (scalarInterpolation f t) - normalization f t) ^ 2) (tetrahedron t) := by
    simpa only [Pi.add_apply] using! hiF.add hiJ
  have ht : (∫ x in tetrahedron t, (f x - eval x (scalarInterpolation f t)) ^ 2) ≤
      2 * ((∫ x in tetrahedron t, (f x - normalization f t) ^ 2) +
        ∫ x in tetrahedron t, (eval x (scalarInterpolation f t) - normalization f t) ^ 2) := by
    calc
      _ ≤ ∫ x in tetrahedron t, 2 * ((f x - normalization f t) ^ 2 +
          (eval x (scalarInterpolation f t) - normalization f t) ^ 2) :=
        setIntegral_mono_on hiErr (hiSum.const_mul 2) (tetrahedron_isCompact hN t).measurableSet
          (fun x _ => by nlinarith [sq_nonneg (f x - normalization f t +
            (eval x (scalarInterpolation f t) - normalization f t))])
      _ = _ := by
        have he : (∫ x in tetrahedron t, (f x - normalization f t) ^ 2 +
            (eval x (scalarInterpolation f t) - normalization f t) ^ 2) =
            (∫ x in tetrahedron t, (f x - normalization f t) ^ 2) +
              ∫ x in tetrahedron t, (eval x (scalarInterpolation f t) - normalization f t) ^ 2 :=
          integral_add hiF hiJ
        rw [integral_const_mul, he]
  calc
    _ ≤ _ := ht
    _ ≤ 2 * (288 * (meshScale N) ^ 2 * localGradientIntegral g t +
        96 * (meshScale N) ^ 2 * localGradientIntegral g t) :=
      mul_le_mul_of_nonneg_left (add_le_add (local_normalized_element_value_bound hN hf t)
        (local_interpolation_center_value_bound hN hf t)) (by norm_num)
    _ = _ := by ring

end FreudenthalSVLean.LocalVolumeInterpolation
