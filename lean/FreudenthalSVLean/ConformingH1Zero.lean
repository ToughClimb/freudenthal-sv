import FreudenthalSVLean.InteriorMollificationL2

/-!
# Actual H1_0 membership by interior smooth approximation

For the manuscript's definition V_h,k subset H1_0(Omega)^3, every actual
velocity component has L2 weak derivatives and is a genuine H1 limit of
infinitely smooth functions with compact support strictly in the open
cube.  The single explicit sequence is normalized convolution followed
by the proved support-compressing homothety.  Both its function error and
all three actual derivative errors converge in squared L2 norm.  Thus
zero boundary values are connected to the standard closure definition
of H1_0 by a proved density statement, rather than a stipulated trace
convention.  The definition below spells out that closure criterion on
actual functions and derivatives; no Fourier/Bessel-potential Sobolev
space identification is asserted.
-/

open scoped BigOperators ContDiff Topology
open MvPolynomial MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingDivergenceMean
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.BoundedMeshFunctions
open FreudenthalSVLean.InteriorMollification
open FreudenthalSVLean.InteriorMollificationL2

noncomputable section

namespace FreudenthalSVLean.ConformingH1Zero

set_option backward.isDefEq.respectTransparency false

/-- The standard H1_0 closure criterion, with actual L2 weak derivatives
and actual smooth compactly supported approximating functions. -/
def InH1ZeroCube (f : Space → ℝ) (g : Fin 3 → Space → ℝ) : Prop :=
  HasL2WeakGradient f g ∧ ∃ u : ℕ → Space → ℝ,
    (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n) ∧ tsupport (u n) ⊆ openCube ∧
      MemLp (u n) 2 volume ∧ ∀ i : Fin 3,
        MemLp (fun x => fderiv ℝ (u n) x (Pi.single i 1)) 2 volume) ∧
    Tendsto (fun n => (∫ x, (u n x - f x) ^ 2) + ∑ i : Fin 3,
      ∫ x, (fderiv ℝ (u n) x (Pi.single i 1) - g i x) ^ 2) atTop (𝓝 0)

theorem velocityFunction_smooth_value_error {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    Tendsto (fun n => ∫ x,
      (interiorMollify n (velocityFunction hN v j) x - velocityFunction hN v j x) ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := velocityFunction_uniform_bound hN v j
  have hs : Function.support (velocityFunction hN v j) ⊆ cube := by
    intro x hx
    by_contra hc
    exact hx (velocityFunction_zero_off_cube hN v j x hc)
  exact interiorMollify_square_error_tendsto
    ((velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)) hM.le hb hs
    (Filter.Eventually.of_forall (fun x => (velocityFunction_continuous hN v j).continuousAt))

theorem velocityFunction_smooth_gradient_error {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    Tendsto (fun n => ∫ x,
      (fderiv ℝ (interiorMollify n (velocityFunction hN v j)) x (Pi.single i 1) -
        piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2) atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := piecewisePressure_uniform_bound hN (fun t => pderiv i (v.val t j))
  have hf := (velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)
  simp only [interiorMollify_partial _ hf i (velocityFunction_hasWeakPartial hN v j i)]
  exact interior_scaled_square_error_tendsto
    ((piecewisePressure_memLp hN _).locallyIntegrable (by norm_num)) hM.le hb
    (piecewisePressure_support_cube hN _) (piecewisePressure_ae_continuousAt hN _) factor
    factor_tendsto (fun n => ⟨(factor_pos n).le, factor_le_five n⟩)

theorem velocityFunction_inH1ZeroCube {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    InH1ZeroCube (velocityFunction hN v j)
      (fun i => piecewisePressure (fun t => pderiv i (v.val t j))) := by
  have hf := (velocityFunction_memLp hN v j).locallyIntegrable (by norm_num)
  have hs : Function.support (velocityFunction hN v j) ⊆ cube := by
    intro x hx
    by_contra hc
    exact hx (velocityFunction_zero_off_cube hN v j x hc)
  refine ⟨velocityFunction_hasL2WeakGradient hN v j,
    (fun n => interiorMollify n (velocityFunction hN v j)), ?_, ?_⟩
  · intro n
    have hd := interiorMollify_contDiff n hf
    have hc := interiorMollify_hasCompactSupport n hs
    refine ⟨hd, hc, interiorMollify_tsupport_subset_openCube n hs,
      hd.continuous.memLp_of_hasCompactSupport hc, fun i => ?_⟩
    have hi : Continuous (fun x => fderiv ℝ (interiorMollify n (velocityFunction hN v j))
        x (Pi.single i 1)) := (hd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hci : HasCompactSupport (fun x =>
        fderiv ℝ (interiorMollify n (velocityFunction hN v j)) x (Pi.single i 1)) := by
      simpa only [Function.comp_def] using (hc.fderiv ℝ).comp_left
        (g := fun L : Space →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)
    exact hi.memLp_of_hasCompactSupport hci
  · have hd := tendsto_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ => velocityFunction_smooth_gradient_error hN v j i)
    simpa only [Finset.sum_const_zero, add_zero] using
      (velocityFunction_smooth_value_error hN v j).add hd

end FreudenthalSVLean.ConformingH1Zero
