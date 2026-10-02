import FreudenthalSVLean.ConformingDivergenceMean

/-!
# Bounded compactly supported representatives on each actual mesh

For the manuscript's Sobolev approximation interface, every actual broken
polynomial assembly is globally bounded and supported in the closed cube.
The statement also applies to its genuine polynomial gradient components.
The constants here may depend on the fixed input and mesh: they establish
membership and dominated convergence, not a uniform lifting estimate.
-/

open scoped BigOperators
open scoped Topology
open MvPolynomial MeasureTheory Set Metric
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.ConformingDivergenceMean
open FreudenthalSVLean.ClassicalVelocityGradient
open FreudenthalSVLean.MeshIntersectionFaces
open FreudenthalSVLean.MeshCoverage

noncomputable section

namespace FreudenthalSVLean.BoundedMeshFunctions

set_option backward.isDefEq.respectTransparency false

theorem piecewisePressure_support_cube {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    Function.support (piecewisePressure q) ⊆ cube := by
  intro x hx
  by_contra hc
  exact hx (piecewisePressure_zero_off_cube hN q x hc)

theorem piecewisePressure_support_ball {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    Function.support (piecewisePressure q) ⊆ closedBall 0 1 := by
  intro x hx
  simpa only [mem_closedBall, dist_zero_right] using
    cube_norm_le_one x (piecewisePressure_support_cube hN q hx)

theorem piecewisePressure_uniform_bound {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Space, ‖piecewisePressure q x‖ ≤ M := by
  classical
  choose K hK using fun t : Tet N => (tetrahedron_isCompact hN t).exists_bound_of_continuousOn
    (continuous_eval (q t)).continuousOn
  let M : ℝ := 1 + ∑ t : Tet N, max 0 (K t)
  have hs : 0 ≤ ∑ t : Tet N, max 0 (K t) :=
    Finset.sum_nonneg (fun t _ => le_max_left _ _)
  refine ⟨M, by dsimp [M]; linarith, fun x => ?_⟩
  have hi (t : Tet N) : ‖(tetrahedron t).indicator (fun y => eval y (q t)) x‖ ≤ max 0 (K t) := by
    by_cases ht : x ∈ tetrahedron t
    · rw [indicator_of_mem ht]
      exact (hK t x ht).trans (le_max_right _ _)
    · rw [indicator_of_notMem ht, norm_zero]
      exact le_max_left _ _
  calc
    ‖piecewisePressure q x‖ ≤ ∑ t : Tet N,
        ‖(tetrahedron t).indicator (fun y => eval y (q t)) x‖ := norm_sum_le _ _
    _ ≤ ∑ t : Tet N, max 0 (K t) := Finset.sum_le_sum (fun t _ => hi t)
    _ ≤ M := by dsimp [M]; linarith

theorem velocityFunction_support_ball {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    Function.support (velocityFunction hN v j) ⊆ closedBall 0 1 := by
  intro x hx
  have hc : x ∈ cube := by
    by_contra ho
    exact hx (velocityFunction_zero_off_cube hN v j x ho)
  simpa only [mem_closedBall, dist_zero_right] using cube_norm_le_one x hc

theorem velocityFunction_uniform_bound {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Space, ‖velocityFunction hN v j x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (velocityFunction_hasCompactSupport hN v j).exists_bound_of_continuous
    (velocityFunction_continuous hN v j)
  refine ⟨1 + max 0 C, by positivity, fun x => ?_⟩
  exact (hC x).trans (by linarith [le_max_right (0 : ℝ) C])

theorem piecewisePressure_continuousAt_on_positive {N : ℕ} (q : BrokenPressure N)
    (t : Tet N) (x : Space) (hx : x ∈ positiveRegion t) :
    ContinuousAt (piecewisePressure q) x := by
  have he : piecewisePressure q =ᶠ[𝓝 x] (fun y => eval y (q t)) := by
    filter_upwards [(positiveRegion_isOpen t).mem_nhds hx] with y hy
    exact piecewisePressure_on_unique q t y (positiveRegion_subset_tetrahedron t hy)
      (fun u hu => (positive_owner_unique t u y ((mem_positiveRegion t y).mp hy) hu).symm)
  exact (continuousAt_congr he).mpr (continuous_eval (q t)).continuousAt

theorem piecewisePressure_ae_continuousAt {N : ℕ} (hN : 0 < N) (q : BrokenPressure N) :
    ∀ᵐ x : Space ∂volume, ContinuousAt (piecewisePressure q) x := by
  filter_upwards [ae_no_face_planes hN] with x hx
  by_cases hc : x ∈ cube
  · let t := owner hN x hc
    have ht := owner_mem hN x hc
    apply piecewisePressure_continuousAt_on_positive q t x
    exact (mem_positiveRegion t x).mpr (fun a =>
      lt_of_le_of_ne (MeshIntersectionFaces.barycentric_nonneg t x ht a) (Ne.symm (hx t a)))
  · have he : piecewisePressure q =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_Icc : IsClosed cube).isOpen_compl.mem_nhds hc] with y hy
      exact piecewisePressure_zero_off_cube hN q y hy
    exact (continuousAt_congr he).mpr continuousAt_const

end FreudenthalSVLean.BoundedMeshFunctions
