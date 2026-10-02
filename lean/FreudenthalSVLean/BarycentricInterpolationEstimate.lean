import FreudenthalSVLean.MeshAveragingBoxes
import FreudenthalSVLean.ElementMeanEnergy
import FreudenthalSVLean.MeshIntersectionFaces

/-!
# Explicit P1 interpolation energy on actual Freudenthal tetrahedra

For the interpolation stage in manuscript Lemma `means` and equation
`SZ`, an actual affine barycentric combination has explicit volume and
gradient bounds in terms of its four coefficients.  Partition of unity
allows subtraction of any constant without changing its derivative.
The bounds use nonnegative barycentric coordinates, their unit sum,
the explicit coordinate-chain gradients and genuine tetrahedron volume.
They do not use an assumed finite-element inverse estimate or a rank
certificate, and their coefficients are independent of N.
-/

open scoped BigOperators Topology
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshIntersectionFaces
open FreudenthalSVLean.ElementMeanEnergy

noncomputable section

namespace FreudenthalSVLean.BarycentricInterpolationEstimate

set_option backward.isDefEq.respectTransparency false

theorem physical_barycentric_sum {N : ℕ} (t : Tet N) :
    (∑ a : Fin 4, FreudenthalMesh.barycentric t a) = 1 :=
  scaledBarycentric_sum t.2 (cellOrigin t.1) (meshScale N)

theorem physical_barycentric_eval_sum {N : ℕ} (t : Tet N) (x : Space) :
    (∑ a : Fin 4, eval x (FreudenthalMesh.barycentric t a)) = 1 := by
  rw [← map_sum, physical_barycentric_sum, map_one]

theorem physical_barycentric_eval_le_one {N : ℕ} (t : Tet N) (x : Space)
    (hx : x ∈ tetrahedron t) (a : Fin 4) : eval x (FreudenthalMesh.barycentric t a) ≤ 1 := by
  rw [← physical_barycentric_eval_sum t x]
  exact Finset.single_le_sum (fun b _ => barycentric_nonneg t x hx b) (Finset.mem_univ a)

theorem physical_barycentric_square_sum_bound {N : ℕ} (t : Tet N) (x : Space)
    (hx : x ∈ tetrahedron t) :
    (∑ a : Fin 4, (eval x (FreudenthalMesh.barycentric t a)) ^ 2) ≤ 4 := by
  have h : (∑ a : Fin 4, (eval x (FreudenthalMesh.barycentric t a)) ^ 2) ≤
      ∑ _a : Fin 4, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro a _
    have hl := barycentric_nonneg t x hx a
    have hu := physical_barycentric_eval_le_one t x hx a
    nlinarith
  simpa using h

theorem chain_gradient_square_bound (σ : Equiv.Perm (Fin 3)) (a : Fin 4) (j : Fin 3) :
    (ChainGeometry.barycentricGradient (R := ℝ) σ a j) ^ 2 ≤ 1 := by
  fin_cases a
  · change (- (if j = σ 0 then (1 : ℝ) else 0)) ^ 2 ≤ 1
    split_ifs <;> norm_num
  · change ((if j = σ 0 then (1 : ℝ) else 0) - (if j = σ 1 then 1 else 0)) ^ 2 ≤ 1
    split_ifs <;> norm_num
  · change ((if j = σ 1 then (1 : ℝ) else 0) - (if j = σ 2 then 1 else 0)) ^ 2 ≤ 1
    split_ifs <;> norm_num
  · change (if j = σ 2 then (1 : ℝ) else 0) ^ 2 ≤ 1
    split_ifs <;> norm_num

theorem chain_gradient_square_sum_bound (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (∑ a : Fin 4, (ChainGeometry.barycentricGradient (R := ℝ) σ a j) ^ 2) ≤ 4 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ => chain_gradient_square_bound σ a j)
  simpa using h

def affineCombination {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ a : Fin 4, C (c a) * FreudenthalMesh.barycentric t a

theorem affineCombination_eval {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ) (x : Space) :
    eval x (affineCombination t c) =
      ∑ a : Fin 4, c a * eval x (FreudenthalMesh.barycentric t a) := by
  simp only [affineCombination, map_sum, map_mul, eval_C]

theorem affineCombination_shift {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ) (m : ℝ) :
    affineCombination t (fun a => c a - m) = affineCombination t c - C m := by
  simp only [affineCombination, map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, physical_barycentric_sum, mul_one]

theorem affineCombination_partial {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ)
    (i : Fin 3) (x : Space) :
    eval x (pderiv i (affineCombination t c)) =
      (meshScale N)⁻¹ * ∑ a : Fin 4, c a * ChainGeometry.barycentricGradient t.2 a i := by
  simp only [affineCombination, map_sum, pderiv_mul, pderiv_C, zero_mul, zero_add,
    FreudenthalMesh.barycentric, pderiv_scaledBarycentric, map_mul, eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem affineCombination_partial_shift {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ)
    (m : ℝ) (i : Fin 3) :
    pderiv i (affineCombination t (fun a => c a - m)) = pderiv i (affineCombination t c) := by
  rw [affineCombination_shift, map_sub, pderiv_C, sub_zero]

theorem affineCombination_value_square_bound {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ)
    (x : Space) (hx : x ∈ tetrahedron t) :
    (eval x (affineCombination t c)) ^ 2 ≤ 4 * ∑ a : Fin 4, (c a) ^ 2 := by
  rw [affineCombination_eval]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c
    (fun a => eval x (FreudenthalMesh.barycentric t a))
  have hn : 0 ≤ ∑ a : Fin 4, (c a) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact hcs.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (physical_barycentric_square_sum_bound t x hx) hn)

theorem affineCombination_partial_square_bound {N : ℕ} (t : Tet N) (c : Fin 4 → ℝ)
    (i : Fin 3) (x : Space) :
    (eval x (pderiv i (affineCombination t c))) ^ 2 ≤
      4 * ((meshScale N)⁻¹) ^ 2 * ∑ a : Fin 4, (c a) ^ 2 := by
  rw [affineCombination_partial, mul_pow]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c
    (fun a => ChainGeometry.barycentricGradient (R := ℝ) t.2 a i)
  have hn : 0 ≤ ∑ a : Fin 4, (c a) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht := mul_le_mul_of_nonneg_left
    (hcs.trans (mul_le_mul_of_nonneg_left (chain_gradient_square_sum_bound t.2 i) hn))
    (sq_nonneg ((meshScale N)⁻¹))
  calc
    _ ≤ ((meshScale N)⁻¹) ^ 2 * ((∑ a : Fin 4, (c a) ^ 2) * 4) := ht
    _ = _ := by ring

theorem tetrahedron_volume {N : ℕ} (hN : 0 < N) (t : Tet N) :
    volume.real (tetrahedron t) = (meshScale N) ^ 3 / 6 := by
  have h := tetrahedron_integral_one hN t
  rw [setIntegral_const] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem affineCombination_value_integral_bound {N : ℕ} (hN : 0 < N)
    (t : Tet N) (c : Fin 4 → ℝ) :
    (∫ x in tetrahedron t, (eval x (affineCombination t c)) ^ 2) ≤
      (2 / 3 : ℝ) * (meshScale N) ^ 3 * ∑ a : Fin 4, (c a) ^ 2 := by
  have hi : IntegrableOn (fun x => (eval x (affineCombination t c)) ^ 2) (tetrahedron t) :=
    ((continuous_eval _).pow 2).continuousOn.integrableOn_compact (tetrahedron_isCompact hN t)
  have hc : IntegrableOn (fun _ : Space => 4 * ∑ a : Fin 4, (c a) ^ 2) (tetrahedron t) :=
    continuous_const.continuousOn.integrableOn_compact (tetrahedron_isCompact hN t)
  calc
    _ ≤ ∫ _x in tetrahedron t, 4 * ∑ a : Fin 4, (c a) ^ 2 :=
      setIntegral_mono_on hi hc (tetrahedron_isCompact hN t).measurableSet
        (fun x hx => affineCombination_value_square_bound t c x hx)
    _ = _ := by
      rw [setIntegral_const, tetrahedron_volume hN]
      simp only [smul_eq_mul]
      ring

theorem affineCombination_partial_integral_bound {N : ℕ} (hN : 0 < N)
    (t : Tet N) (c : Fin 4 → ℝ) (i : Fin 3) :
    (∫ x in tetrahedron t, (eval x (pderiv i (affineCombination t c))) ^ 2) ≤
      (2 / 3 : ℝ) * meshScale N * ∑ a : Fin 4, (c a) ^ 2 := by
  have hi : IntegrableOn (fun x => (eval x (pderiv i (affineCombination t c))) ^ 2)
      (tetrahedron t) :=
    ((continuous_eval _).pow 2).continuousOn.integrableOn_compact (tetrahedron_isCompact hN t)
  have hc : IntegrableOn (fun _ : Space =>
      4 * ((meshScale N)⁻¹) ^ 2 * ∑ a : Fin 4, (c a) ^ 2) (tetrahedron t) :=
    continuous_const.continuousOn.integrableOn_compact (tetrahedron_isCompact hN t)
  calc
    _ ≤ ∫ _x in tetrahedron t, 4 * ((meshScale N)⁻¹) ^ 2 * ∑ a : Fin 4, (c a) ^ 2 :=
      setIntegral_mono_on hi hc (tetrahedron_isCompact hN t).measurableSet
        (fun x _ => affineCombination_partial_square_bound t c i x)
    _ = _ := by
      rw [setIntegral_const, tetrahedron_volume hN]
      simp only [smul_eq_mul]
      field_simp [(meshScale_pos N hN).ne']
      ring

theorem affineCombination_gradient_integral_bound {N : ℕ} (hN : 0 < N)
    (t : Tet N) (c : Fin 4 → ℝ) :
    (∑ i : Fin 3, ∫ x in tetrahedron t, (eval x (pderiv i (affineCombination t c))) ^ 2) ≤
      2 * meshScale N * ∑ a : Fin 4, (c a) ^ 2 := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => affineCombination_partial_integral_bound hN t c i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat,
    nsmul_eq_mul, show (3 : ℝ) * ((2 / 3 : ℝ) * meshScale N *
      ∑ a : Fin 4, (c a) ^ 2) = 2 * meshScale N * ∑ a : Fin 4, (c a) ^ 2 by ring] using ht

end FreudenthalSVLean.BarycentricInterpolationEstimate
