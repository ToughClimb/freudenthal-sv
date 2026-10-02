import FreudenthalSVLean.GlobalPolynomialL2
import Mathlib.Topology.LocallyFinite

/-!
# Actual continuous zero extensions of conforming velocities

For the manuscript's definition of `V_{h,k}`, actual conforming polynomial
data have a fixed linear global function representation.  It agrees with
every local polynomial at every closed-element point, including faces,
edges and vertices, vanishes on the physical boundary and outside the
cube, and is continuous on all Euclidean space.  Finite closed-cover
gluing proves continuity; a coordinate-open cube and its closed complement
prove continuity of the zero extension.  Its actual component L2 norms
are identified through the proved almost-everywhere mesh partition.
Weak derivative and H1_0 conclusions are not asserted in this module.
-/

open scoped BigOperators
open Classical
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.GlobalPolynomialL2

noncomputable section

namespace FreudenthalSVLean.ConformingVelocityFunction

set_option backward.isDefEq.respectTransparency false

def owner {N : ℕ} (hN : 0 < N) (x : Space) (hx : x ∈ cube) : Tet N :=
  (cube_covered N hN x hx).choose

theorem owner_mem {N : ℕ} (hN : 0 < N) (x : Space) (hx : x ∈ cube) :
    x ∈ tetrahedron (owner hN x hx) := (cube_covered N hN x hx).choose_spec

def velocityFunction {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (j : Fin 3) (x : Space) : ℝ :=
  if hx : x ∈ cube then eval x (v.val (owner hN x hx) j) else 0

theorem velocityFunction_on_element {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (t : Tet N) (x : Space) (ht : x ∈ tetrahedron t) (j : Fin 3) :
    velocityFunction hN v j x = eval x (v.val t j) := by
  have hx := tetrahedron_subset_cube hN t ht
  rw [velocityFunction, dif_pos hx]
  exact v.property.2.1 _ t x (owner_mem hN x hx) ht j

theorem velocityFunction_zero_off_cube {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) (x : Space) (hx : x ∉ cube) :
    velocityFunction hN v j x = 0 := by
  exact dif_neg hx

theorem velocityFunction_boundary_zero {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) (x : Space) (hx : x ∈ cubeBoundary) :
    velocityFunction hN v j x = 0 := by
  rw [velocityFunction, dif_pos hx.1]
  exact v.property.2.2 _ x (owner_mem hN x hx.1) hx j

def velocityFunctionLinear {N k : ℕ} (hN : 0 < N) :
    velocitySpace N k →ₗ[ℝ] (Fin 3 → Space → ℝ) where
  toFun := velocityFunction hN
  map_add' v w := by
    funext j x
    simp only [velocityFunction, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext j x
    simp only [velocityFunction, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

def openCube : Set Space := pi univ (fun _ : Fin 3 => Ioo (0 : ℝ) 1)

theorem mem_openCube (x : Space) : x ∈ openCube ↔ ∀ j, 0 < x j ∧ x j < 1 := by
  simp [openCube, Set.mem_pi]

theorem openCube_isOpen : IsOpen openCube :=
  isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem openCube_subset_cube : openCube ⊆ cube := by
  intro x hx
  have hp := (mem_openCube x).mp hx
  exact ⟨fun j => (hp j).1.le, fun j => (hp j).2.le⟩

theorem cube_off_open_is_boundary (x : Space) (hx : x ∈ cube) (ho : x ∉ openCube) :
    x ∈ cubeBoundary := by
  refine ⟨hx, ?_⟩
  have hn : ¬ ∀ j : Fin 3, 0 < x j ∧ x j < 1 := fun h => ho ((mem_openCube x).mpr h)
  obtain ⟨j, hj⟩ := not_forall.mp hn
  refine ⟨j, ?_⟩
  by_cases h0 : 0 < x j
  · right
    have h1 : ¬ x j < 1 := fun h => hj ⟨h0, h⟩
    exact le_antisymm (hx.2 j) (le_of_not_gt h1)
  · left
    exact le_antisymm (le_of_not_gt h0) (hx.1 j)

theorem cube_union_closed_exterior : cube ∪ openCubeᶜ = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ openCube
  · exact Or.inl (openCube_subset_cube hx)
  · exact Or.inr hx

theorem velocityFunction_zero_off_openCube {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) (x : Space) (hx : x ∉ openCube) :
    velocityFunction hN v j x = 0 := by
  by_cases hc : x ∈ cube
  · exact velocityFunction_boundary_zero hN v j x (cube_off_open_is_boundary x hc hx)
  · exact velocityFunction_zero_off_cube hN v j x hc

theorem velocityFunction_continuousOn_cube {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) : ContinuousOn (velocityFunction hN v j) cube := by
  rw [← tetrahedra_union_cube N hN]
  apply (locallyFinite_of_finite (fun t : Tet N => tetrahedron t)).continuousOn_iUnion
    (fun t => (tetrahedron_isCompact hN t).isClosed)
  intro t
  exact (continuous_eval (v.val t j)).continuousOn.congr
    (fun x hx => velocityFunction_on_element hN v t x hx j)

theorem velocityFunction_continuous {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) : Continuous (velocityFunction hN v j) := by
  have ho : ContinuousOn (velocityFunction hN v j) openCubeᶜ :=
    continuous_const.continuousOn.congr (fun x hx => velocityFunction_zero_off_openCube hN v j x hx)
  have hc := (velocityFunction_continuousOn_cube hN v j).union_of_isClosed ho
    (isClosed_Icc : IsClosed cube) openCube_isOpen.isClosed_compl
  rw [cube_union_closed_exterior] at hc
  exact continuousOn_univ.mp hc

theorem velocityFunction_ae_piecewise {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    velocityFunction hN v j =ᵐ[volume] piecewisePressure (fun t => v.val t j) := by
  filter_upwards [ae_unique_owner hN] with x hx
  by_cases hc : x ∈ cube
  · let t := owner hN x hc
    have ht : x ∈ tetrahedron t := owner_mem hN x hc
    rw [velocityFunction_on_element hN v t x ht j,
      piecewisePressure_on_unique _ t x ht (fun u hu => hx u t hu ht)]
  · rw [velocityFunction_zero_off_cube hN v j x hc,
      piecewisePressure_zero_off_cube hN _ x hc]

theorem velocityFunction_memLp {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) : MemLp (velocityFunction hN v j) 2 volume :=
  (piecewisePressure_memLp hN (fun t => v.val t j)).ae_eq
    (velocityFunction_ae_piecewise hN v j).symm

theorem velocityFunction_square_integral {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    (∫ x, (velocityFunction hN v j x) ^ 2) =
      ∑ t : Tet N, ∫ x in tetrahedron t, (eval x (v.val t j)) ^ 2 := by
  calc
    _ = ∫ x, (piecewisePressure (fun t => v.val t j) x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [velocityFunction_ae_piecewise hN v j] with x hx
      exact congrArg (fun y : ℝ => y ^ 2) hx
    _ = _ := piecewisePressure_square_integral hN _

end FreudenthalSVLean.ConformingVelocityFunction
