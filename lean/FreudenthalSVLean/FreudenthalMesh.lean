import FreudenthalSVLean.ScaledChainGeometry
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.GroupTheory.Perm.Fin

/-!
# Arbitrary-size Freudenthal meshes and the finite-element algebra

The manuscript's definitions of `T_h`, `V_{h,k}`, and `Q_{h,k}=div V_{h,k}`
are encoded for arbitrary `N`.  Velocities are actual spatial polynomials,
with equality of values on every tetrahedron intersection and zero values
on the boundary of the cube.  The pressure space is exactly the image of
the actual polynomial divergence, not a larger guessed pressure space.

The displayed energies use genuine Lebesgue integrals of the polynomial
gradient and pressure.  Identifying this representation with `H¹₀` and
proving mesh coverage and almost-everywhere disjointness remain separate
theorems; they are not assumptions in the definition of the algebraic spaces.
No uniform-right-inverse assertion is proved merely by defining its target.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.FreudenthalMesh

abbrev Cell (N : ℕ) := Fin 3 → Fin N
abbrev Tet (N : ℕ) := Cell N × Equiv.Perm (Fin 3)

def meshScale (N : ℕ) : ℝ := (N : ℝ)⁻¹

theorem meshScale_pos (N : ℕ) (hN : 0 < N) : 0 < meshScale N := by
  exact inv_pos.mpr (Nat.cast_pos.mpr hN)

def cellOrigin {N : ℕ} (c : Cell N) : Space := fun j => (c j).val

def tetrahedron {N : ℕ} (t : Tet N) : Set Space :=
  scaledChainSet t.2 (cellOrigin t.1) (meshScale N)

def vertex {N : ℕ} (t : Tet N) (a : Fin 4) : Space :=
  scaledVertex t.2 (cellOrigin t.1) (meshScale N) a

def barycentric {N : ℕ} (t : Tet N) (a : Fin 4) : MvPolynomial (Fin 3) ℝ :=
  scaledBarycentric t.2 (cellOrigin t.1) (meshScale N) a

theorem barycentric_vertex {N : ℕ} (hN : 0 < N) (t : Tet N) (i a : Fin 4) :
    eval (vertex t a) (barycentric t i) = if i = a then 1 else 0 :=
  scaledBarycentric_vertex t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN).ne' i a

theorem tetrahedron_isCompact {N : ℕ} (hN : 0 < N) (t : Tet N) :
    IsCompact (tetrahedron t) :=
  scaledChainSet_isCompact t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN).ne'

theorem tetrahedron_count (N : ℕ) : Fintype.card (Tet N) = 6 * N ^ 3 := by
  simp [Tet, Cell, Fintype.card_perm, Nat.mul_comm]
  norm_num

def cube : Set Space := Set.Icc 0 1

def cubeBoundary : Set Space :=
  {x | x ∈ cube ∧ ∃ j : Fin 3, x j = 0 ∨ x j = 1}

abbrev BrokenVelocity (N : ℕ) := Tet N → Fin 3 → MvPolynomial (Fin 3) ℝ
abbrev BrokenPressure (N : ℕ) := Tet N → MvPolynomial (Fin 3) ℝ

/-- Continuous piecewise-`P_k` velocity data with homogeneous boundary trace.
Conformity is imposed on all actual shared points, including edges/vertices. -/
def velocitySpace (N k : ℕ) : Submodule ℝ (BrokenVelocity N) where
  carrier := {v |
    (∀ t j, (v t j).totalDegree ≤ k) ∧
    (∀ t u x, x ∈ tetrahedron t → x ∈ tetrahedron u →
      ∀ j, eval x (v t j) = eval x (v u j)) ∧
    (∀ t x, x ∈ tetrahedron t → x ∈ cubeBoundary → ∀ j, eval x (v t j) = 0)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp
  add_mem' := by
    rintro v w ⟨hvdeg, hvcon, hvbd⟩ ⟨hwdeg, hwcon, hwbd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t j
      exact (totalDegree_add _ _).trans (max_le (hvdeg t j) (hwdeg t j))
    · intro t u x ht hu j
      simp only [Pi.add_apply, map_add, hvcon t u x ht hu j, hwcon t u x ht hu j]
    · intro t x ht hb j
      simp only [Pi.add_apply, map_add, hvbd t x ht hb j, hwbd t x ht hb j, add_zero]
  smul_mem' := by
    rintro c v ⟨hvdeg, hvcon, hvbd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t j
      exact (totalDegree_smul_le _ _).trans (hvdeg t j)
    · intro t u x ht hu j
      simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, hvcon t u x ht hu j]
    · intro t x ht hb j
      simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, hvbd t x ht hb j,
        mul_zero]

def divergence (N : ℕ) : BrokenVelocity N →ₗ[ℝ] BrokenPressure N where
  toFun v t := ∑ j : Fin 3, pderiv j (v t j)
  map_add' v w := by
    funext t
    simp [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext t
    simp only [Pi.smul_apply, Derivation.map_smul, Finset.smul_sum, RingHom.id_apply]

/-- Exactly the divergence image of the conforming velocity space. -/
def pressureSpace (N k : ℕ) : Submodule ℝ (BrokenPressure N) :=
  (velocitySpace N k).map (divergence N)

theorem pressure_mem_iff (N k : ℕ) (q : BrokenPressure N) :
    q ∈ pressureSpace N k ↔ ∃ v ∈ velocitySpace N k, divergence N v = q :=
  Iff.rfl

def velocityEnergy {N : ℕ} (v : BrokenVelocity N) : ℝ :=
  ∑ t : Tet N, ∫ x in tetrahedron t,
    ∑ j : Fin 3, ∑ i : Fin 3, (eval x (pderiv i (v t j))) ^ 2

def pressureEnergy {N : ℕ} (q : BrokenPressure N) : ℝ :=
  ∑ t : Tet N, ∫ x in tetrahedron t, (eval x (q t)) ^ 2

/-- Precise discrete target of the manuscript's uniform right-inverse theorem.
The constant is chosen before `N`, and each lift is a single linear map. -/
def HasUniformRightInverse (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    ∃ R : pressureSpace N k →ₗ[ℝ] velocitySpace N k,
      (∀ q, divergence N (R q).val = q.val) ∧
      (∀ q, velocityEnergy (R q).val ≤ C ^ 2 * pressureEnergy q.val)

end FreudenthalSVLean.FreudenthalMesh
