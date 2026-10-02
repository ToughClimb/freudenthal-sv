import FreudenthalSVLean.WeakVelocityGradient
import FreudenthalSVLean.DivergenceMean

/-!
# Zero total mean of the actual divergence image

For the manuscript's definition Q_h,k = div V_h,k and the compatibility
needed by the initial mean lift, the genuine volume integral of every
conforming velocity divergence is zero.  A concrete smooth compactly
supported cutoff is one on a neighborhood of the closed cube.  Testing
the proved weak-derivative identities against this cutoff gives zero for
each coordinate integral and hence for their sum.  This also verifies
zero total mean for every pressure in the actual divergence image, with
no assumed divergence theorem or mesh-specific imported compatibility.
-/

open scoped BigOperators ContDiff Topology
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.DivergenceMean

noncomputable section

namespace FreudenthalSVLean.ConformingDivergenceMean

set_option backward.isDefEq.respectTransparency false

def cubeCutoff : ContDiffBump (0 : Space) := ⟨2, 3, by norm_num, by norm_num⟩

theorem cube_norm_le_one (x : Space) (hx : x ∈ cube) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  rw [Real.norm_of_nonneg (hx.1 j)]
  exact hx.2 j

theorem cubeCutoff_eventually_one (x : Space) (hx : x ∈ cube) :
    (cubeCutoff : Space → ℝ) =ᶠ[𝓝 x] (fun _ => 1) := by
  apply cubeCutoff.eventuallyEq_one_of_mem_ball
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (cube_norm_le_one x hx) (by norm_num [cubeCutoff])

theorem cubeCutoff_one (x : Space) (hx : x ∈ cube) : cubeCutoff x = 1 :=
  (cubeCutoff_eventually_one x hx).eq_of_nhds

theorem cubeCutoff_fderiv_zero (x : Space) (hx : x ∈ cube) :
    fderiv ℝ (cubeCutoff : Space → ℝ) x = 0 := by
  rw [(cubeCutoff_eventually_one x hx).fderiv_eq]
  simp

theorem velocityFunction_hasCompactSupport {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) : HasCompactSupport (velocityFunction hN v j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact cube)
  intro x hx
  by_contra hc
  exact hx (velocityFunction_zero_off_cube hN v j x hc)

theorem velocity_partial_integral_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    (∫ x, piecewisePressure (fun t => pderiv i (v.val t j)) x) = 0 := by
  have hw := velocityFunction_hasWeakPartial hN v j i
    (cubeCutoff : Space → ℝ) cubeCutoff.contDiff cubeCutoff.hasCompactSupport
  have hl : (fun x => piecewisePressure (fun t => pderiv i (v.val t j)) x * cubeCutoff x) =
      piecewisePressure (fun t => pderiv i (v.val t j)) := by
    funext x
    by_cases hc : x ∈ cube
    · rw [cubeCutoff_one x hc, mul_one]
    · rw [piecewisePressure_zero_off_cube hN _ x hc, zero_mul]
  have hr : (fun x => velocityFunction hN v j x *
      fderiv ℝ (cubeCutoff : Space → ℝ) x (Pi.single i 1)) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hc : x ∈ cube
    · rw [cubeCutoff_fderiv_zero x hc]
      simp
    · rw [velocityFunction_zero_off_cube hN v j x hc, zero_mul]
  rw [hl, hr] at hw
  simpa only [integral_zero, neg_zero] using hw

theorem conforming_totalMean_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) : totalMean hN v.val = 0 := by
  rw [totalMean_apply]
  change (∑ t : Tet N, tetIntegral hN t (∑ j : Fin 3, pderiv j (v.val t j))) = 0
  simp only [map_sum]
  rw [Finset.sum_comm]
  have hj (j : Fin 3) : (∑ t : Tet N, tetIntegral hN t (pderiv j (v.val t j))) = 0 := by
    rw [← piecewisePressure_mean hN]
    exact velocity_partial_integral_zero hN v j j
  simp only [hj, Finset.sum_const_zero]

theorem pressureSpace_mean_zero {N k : ℕ} (hN : 0 < N) (q : pressureSpace N k) :
    (∑ t : Tet N, tetIntegral hN t (q.val t)) = 0 := by
  obtain ⟨v, hv, he⟩ := q.property
  rw [← he]
  simpa only [totalMean_apply] using conforming_totalMean_zero hN ⟨v, hv⟩

theorem pressureSpace_integral_zero {N k : ℕ} (hN : 0 < N) (q : pressureSpace N k) :
    (∫ x, piecewisePressure q.val x) = 0 := by
  rw [piecewisePressure_mean hN]
  exact pressureSpace_mean_zero hN q

end FreudenthalSVLean.ConformingDivergenceMean
