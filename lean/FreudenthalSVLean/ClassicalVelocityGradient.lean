import FreudenthalSVLean.ConformingVelocityFunction

/-!
# Genuine almost-everywhere classical gradients

For the manuscript's physical gradient norm, the continuous zero extension
of every actual conforming velocity agrees locally with its polynomial
on each positive-barycentric element interior.  The proved null affine
face planes leave only a volume-zero exceptional set.  Thus its actual
Frechet derivative components agree almost everywhere with the assembled
polynomial derivatives, belong to L2, and have exactly the defined gradient
energy.  This module does not infer weak differentiability from mere
almost-everywhere classical differentiation; that implication and H1_0
membership remain separate obligations.
-/

open scoped BigOperators Topology
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshIntersectionFaces
open FreudenthalSVLean.MeshMeasurePartition
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingVelocityFunction

noncomputable section

namespace FreudenthalSVLean.ClassicalVelocityGradient

set_option backward.isDefEq.respectTransparency false

def positiveRegion {N : ℕ} (t : Tet N) : Set Space :=
  ⋂ a : Fin 4, {x | 0 < eval x (barycentric t a)}

theorem mem_positiveRegion {N : ℕ} (t : Tet N) (x : Space) :
    x ∈ positiveRegion t ↔ ∀ a, 0 < eval x (barycentric t a) := by
  simp [positiveRegion]

theorem positiveRegion_isOpen {N : ℕ} (t : Tet N) : IsOpen (positiveRegion t) :=
  isOpen_iInter_of_finite (fun a => isOpen_lt continuous_const (continuous_eval (barycentric t a)))

theorem positiveRegion_subset_tetrahedron {N : ℕ} (t : Tet N) :
    positiveRegion t ⊆ tetrahedron t := by
  intro x hx
  let y : Space := (meshScale N)⁻¹ • x
  have hp (a : Fin 4) : 0 < eval y (ChainGeometry.barycentric t.2 (cellOrigin t.1) a) := by
    simpa only [FreudenthalMesh.barycentric, scaledBarycentric_eval] using
      (mem_positiveRegion t x).mp hx a
  have hc := unit_positive_chain t.2 (cellOrigin t.1) y hp
  exact unitChainSet_mem_of_bounds t.2 (cellOrigin t.1) y
    (fun j => ⟨(unit_positive_coordinate_bounds _ _ _ hp j).1.le,
      (unit_positive_coordinate_bounds _ _ _ hp j).2.le⟩) hc.2.1.le hc.2.2.1.le

theorem ae_no_face_planes {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x : Space ∂volume, ∀ (t : Tet N) (a : Fin 4), eval x (barycentric t a) ≠ 0 := by
  apply ae_all_iff.mpr
  intro t
  apply ae_all_iff.mpr
  intro a
  have hp := measure_eq_zero_iff_ae_notMem.mp (facePlane_volume_zero hN t a)
  filter_upwards [hp] with x hx
  exact fun he => hx ((mem_facePlane t a x).mpr he)

theorem velocityFunction_fderiv_on_positive {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (x : Space) (hx : x ∈ positiveRegion t)
    (j i : Fin 3) :
    fderiv ℝ (velocityFunction hN v j) x (Pi.single i 1) = eval x (pderiv i (v.val t j)) := by
  have he : velocityFunction hN v j =ᶠ[𝓝 x] (fun y => eval y (v.val t j)) := by
    filter_upwards [(positiveRegion_isOpen t).mem_nhds hx] with y hy
    exact velocityFunction_on_element hN v t y (positiveRegion_subset_tetrahedron t hy) j
  rw [he.fderiv_eq]
  exact PolynomialCalculus.fderiv_eval_single (v.val t j) x i

theorem velocityFunction_fderiv_off_cube {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (x : Space) (hx : x ∉ cube) (j i : Fin 3) :
    fderiv ℝ (velocityFunction hN v j) x (Pi.single i 1) = 0 := by
  have he : velocityFunction hN v j =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_Icc : IsClosed cube).isOpen_compl.mem_nhds hx] with y hy
    exact velocityFunction_zero_off_cube hN v j y hy
  rw [he.fderiv_eq]
  simp

theorem velocityFunction_fderiv_ae {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    (fun x => fderiv ℝ (velocityFunction hN v j) x (Pi.single i 1)) =ᵐ[volume]
      piecewisePressure (fun t => pderiv i (v.val t j)) := by
  filter_upwards [ae_unique_owner hN, ae_no_face_planes hN] with x hx hf
  by_cases hc : x ∈ cube
  · let t := owner hN x hc
    have ht : x ∈ tetrahedron t := owner_mem hN x hc
    have hp : x ∈ positiveRegion t := (mem_positiveRegion t x).mpr (fun a =>
      lt_of_le_of_ne (MeshIntersectionFaces.barycentric_nonneg t x ht a) (Ne.symm (hf t a)))
    rw [velocityFunction_fderiv_on_positive hN v t x hp j i,
      piecewisePressure_on_unique _ t x ht (fun u hu => hx u t hu ht)]
  · rw [velocityFunction_fderiv_off_cube hN v x hc j i,
      piecewisePressure_zero_off_cube hN _ x hc]

theorem velocityFunction_fderiv_memLp {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j i : Fin 3) :
    MemLp (fun x => fderiv ℝ (velocityFunction hN v j) x (Pi.single i 1)) 2 volume :=
  (piecewisePressure_memLp hN (fun t => pderiv i (v.val t j))).ae_eq
    (velocityFunction_fderiv_ae hN v j i).symm

theorem velocityFunction_classical_gradient_energy {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) :
    (∑ j : Fin 3, ∑ i : Fin 3, ∫ x,
      (fderiv ℝ (velocityFunction hN v j) x (Pi.single i 1)) ^ 2) = velocityEnergy v.val := by
  calc
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x, (piecewisePressure (fun t => pderiv i (v.val t j)) x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [velocityFunction_fderiv_ae hN v j i] with x hx
      exact congrArg (fun y : ℝ => y ^ 2) hx
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
        ‖toMeshL2 hN (fun t => pderiv i (v.val t j))‖ ^ 2 := by
      simp only [piecewisePressure_square_integral hN, toMeshL2_norm_square]
    _ = _ := (velocityEnergy_eq_sum_L2 hN v.val).symm

end FreudenthalSVLean.ClassicalVelocityGradient
