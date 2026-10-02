import FreudenthalSVLean.MacroMeanTransfer
import FreudenthalSVLean.DivergenceEnergy

/-!
# Actual element-mean bounds from genuine gradient energy

For manuscript Lemma `routing` and its stability estimate, the square of
an actual divergence integral is bounded by `h^3/6` times its element
pressure energy.  The proof integrates a nonnegative polynomial square
and uses the proved physical tetrahedron volume.  Summing and applying
the pointwise divergence estimate yields `sum m_T^2 <= h^3/2 energy(v)`
without any polynomial-degree or mesh enumeration hypothesis.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MacroMeanTransfer

noncomputable section

namespace FreudenthalSVLean.ElementMeanEnergy

theorem tetrahedron_integral_one {N : ℕ} (hN : 0 < N) (t : Tet N) :
    (∫ _x in tetrahedron t, (1 : ℝ)) = (meshScale N) ^ 3 / 6 := by
  have h := scaled_bernstein_integral t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN) 0 (0 : Fin 4 →₀ ℕ)
  norm_num [BernsteinPolynomial.bernstein, normalization, factorialProduct, tetrahedron] at h ⊢
  exact h

theorem tetIntegral_C {N : ℕ} (hN : 0 < N) (t : Tet N) (c : ℝ) :
    tetIntegral hN t (C c) = c * ((meshScale N) ^ 3 / 6) := by
  change (∫ x in tetrahedron t, eval x (C c)) = _
  simp only [eval_C]
  rw [← tetrahedron_integral_one hN t, ← integral_const_mul]
  simp

/-- Cauchy--Schwarz for every actual element polynomial, derived here
from the integral of a square rather than a coefficient norm. -/
theorem polynomial_mean_square_bound {N : ℕ} (hN : 0 < N) (t : Tet N)
    (p : MvPolynomial (Fin 3) ℝ) :
    (tetIntegral hN t p) ^ 2 ≤ ((meshScale N) ^ 3 / 6) * tetIntegral hN t (p ^ 2) := by
  let V : ℝ := (meshScale N) ^ 3 / 6
  let M : ℝ := tetIntegral hN t p
  let P : ℝ := tetIntegral hN t (p ^ 2)
  have hV : 0 < V := by dsimp [V]; positivity [meshScale_pos N hN]
  have hnon (c : ℝ) : 0 ≤ P - 2 * c * M + c ^ 2 * V := by
    have h : 0 ≤ tetIntegral hN t ((p - C c) ^ 2) := by
      change 0 ≤ ∫ x in tetrahedron t, eval x ((p - C c) ^ 2)
      simp only [map_pow]
      exact integral_nonneg (fun _ => sq_nonneg _)
    have he : (p - C c) ^ 2 = p ^ 2 - C (2 * c) * p + C (c ^ 2) := by
      simp only [map_mul, map_pow, map_ofNat]
      ring
    rw [he, map_add, map_sub, ← smul_eq_C_mul, map_smul, tetIntegral_C] at h
    exact h
  have hn := mul_nonneg (hnon (M / V)) (sq_nonneg V)
  have he : (P - 2 * (M / V) * M + (M / V) ^ 2 * V) * V ^ 2 =
      V * (V * P - M ^ 2) := by
    field_simp [hV.ne']
    ring
  rw [he] at hn
  have hres : 0 ≤ V * P - M ^ 2 := (mul_nonneg_iff_of_pos_left hV).mp hn
  exact sub_nonneg.mp hres

theorem globalMeans_square_sum_bound {N : ℕ} (hN : 0 < N) (k : ℕ)
    (v : velocitySpace N k) :
    (∑ t : Tet N, (elementMeans hN k v t) ^ 2) ≤
      ((meshScale N) ^ 3 / 2) * velocityEnergy v.val := by
  have hscale : 0 ≤ (meshScale N) ^ 3 / 6 := by positivity [meshScale_pos N hN]
  calc
    _ ≤ ∑ t : Tet N, ((meshScale N) ^ 3 / 6) *
        tetIntegral hN t ((divergence N v.val t) ^ 2) :=
      Finset.sum_le_sum (fun t _ => polynomial_mean_square_bound hN t _)
    _ = ((meshScale N) ^ 3 / 6) * pressureEnergy (divergence N v.val) := by
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp [tetIntegral]
    _ ≤ ((meshScale N) ^ 3 / 6) * (3 * velocityEnergy v.val) :=
      mul_le_mul_of_nonneg_left (DivergenceEnergy.divergence_energy_bound hN v.val) hscale
    _ = _ := by ring

end FreudenthalSVLean.ElementMeanEnergy
