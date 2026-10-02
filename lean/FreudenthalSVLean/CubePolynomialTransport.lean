import FreudenthalSVLean.CubeMeshSymmetry
import FreudenthalSVLean.PolynomialChainTransport

/-!
# Polynomial and finite-element transport under cube symmetries

For the manuscript's local edge lifting and uniform scaling estimates,
the coordinate-permuted, centrally inverted lifts are actual conforming
polynomial fields on the physical mesh.  The affine substitution below
has a proved chain rule.  The signed vector transformation commutes with
divergence and preserves the actual integral energies and element means.
This is a mesh-level transport theorem, not a classification by counts.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeMeshSymmetry

noncomputable section

namespace FreudenthalSVLean.CubePolynomialTransport

set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial Coordinate ℝ

def orientationSign (flip : Bool) : ℝ := if flip then -1 else 1

theorem orientationSign_square (flip : Bool) : orientationSign flip ^ 2 = 1 := by
  cases flip <;> norm_num [orientationSign]

def affineVariable (π : Equiv.Perm Coordinate) (flip : Bool) (j : Coordinate) : Poly :=
  if flip then 1 - X (π j) else X (π j)

def substitute (π : Equiv.Perm Coordinate) (flip : Bool) (p : Poly) : Poly :=
  eval₂Hom C (affineVariable π flip) p

def substituteLinear (π : Equiv.Perm Coordinate) (flip : Bool) : Poly →ₗ[ℝ] Poly where
  toFun := substitute π flip
  map_add' p q := by simp only [substitute, map_add]
  map_smul' c p := by
    simp only [substitute, smul_eq_C_mul, map_mul, eval₂Hom_C, RingHom.id_apply]

theorem substitute_eval (π : Equiv.Perm Coordinate) (flip : Bool) (p : Poly)
    (x : Space) : eval x (substitute π flip p) = eval ((pointEquiv π flip).symm x) p := by
  rw [substitute, PolynomialCalculus.eval_substitution]
  apply congrArg (fun y : Space => eval y p)
  funext j
  rw [pointEquiv_symm, pointEquiv_apply]
  cases flip <;> simp [affineVariable]

theorem substitute_inverse (π : Equiv.Perm Coordinate) (flip : Bool) (p : Poly) :
    substitute π.symm flip (substitute π flip p) = p := by
  apply MvPolynomial.funext
  intro x
  rw [substitute_eval, substitute_eval, pointEquiv_symm, pointEquiv_symm]
  simpa using congrArg (fun y : Space => eval y p) (pointEquiv_inverse π flip x)

theorem substitute_degree (π : Equiv.Perm Coordinate) (flip : Bool) (p : Poly) :
    (substitute π flip p).totalDegree ≤ p.totalDegree := by
  apply PolynomialDegree.affine_substitution_degree
  intro j
  cases flip
  · simp [affineVariable]
  · exact (PolynomialDegree.sub_degree_le _ _).trans (by simp)

theorem pderiv_affineVariable (π : Equiv.Perm Coordinate) (flip : Bool)
    (r j : Coordinate) : pderiv j (affineVariable π flip r) =
      if π r = j then C (orientationSign flip) else 0 := by
  cases flip <;> by_cases he : π r = j <;>
    simp [affineVariable, orientationSign, pderiv_X, he]

theorem pderiv_substitute (π : Equiv.Perm Coordinate) (flip : Bool)
    (p : Poly) (j : Coordinate) :
    pderiv j (substitute π flip p) =
      C (orientationSign flip) * substitute π flip (pderiv (π.symm j) p) := by
  rw [substitute, PolynomialCalculus.pderiv_substitution]
  simp only [pderiv_affineVariable, mul_ite, mul_zero, ← π.eq_symm_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

def pushPressure {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) : BrokenPressure N :=
  fun t => substitute π flip (q ((tetEquiv π flip).symm t))

def pushVelocity {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) : BrokenVelocity N :=
  fun t j => C (orientationSign flip) *
    substitute π flip (v ((tetEquiv π flip).symm t) (π.symm j))

def pushPressureLinear {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) :
    BrokenPressure N →ₗ[ℝ] BrokenPressure N where
  toFun := pushPressure π flip
  map_add' q r := by
    funext t
    simp [pushPressure, substitute, map_add]
  map_smul' c q := by
    funext t
    exact (substituteLinear π flip).map_smul c (q ((tetEquiv π flip).symm t))

def pushVelocityLinear {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) :
    BrokenVelocity N →ₗ[ℝ] BrokenVelocity N where
  toFun := pushVelocity π flip
  map_add' v w := by
    funext t j
    simp [pushVelocity, substitute, map_add, mul_add]
  map_smul' c v := by
    funext t j
    simp [pushVelocity, substitute, smul_eq_C_mul, mul_left_comm]

theorem pushPressure_eval {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) (t : Tet N) (x : Space) :
    eval x (pushPressure π flip q t) =
      eval ((pointEquiv π flip).symm x) (q ((tetEquiv π flip).symm t)) :=
  substitute_eval π flip _ x

theorem pushVelocity_eval {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) (t : Tet N) (x : Space) (j : Coordinate) :
    eval x (pushVelocity π flip v t j) = orientationSign flip *
      eval ((pointEquiv π flip).symm x) (v ((tetEquiv π flip).symm t) (π.symm j)) := by
  simp only [pushVelocity, map_mul, eval_C, substitute_eval]

theorem pushVelocity_derivative {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) (t : Tet N) (i j : Coordinate) :
    pderiv i (pushVelocity π flip v t j) =
      substitute π flip (pderiv (π.symm i) (v ((tetEquiv π flip).symm t) (π.symm j))) := by
  rw [pushVelocity, pderiv_C_mul, pderiv_substitute, ← mul_assoc, ← C_mul]
  have hs : orientationSign flip * orientationSign flip = 1 := by
    simpa [pow_two] using orientationSign_square flip
  rw [hs, C_1, one_mul]

theorem divergence_pushVelocity {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) : divergence N (pushVelocity π flip v) =
      pushPressure π flip (divergence N v) := by
  funext t
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, pushVelocity_derivative]
  change (∑ j : Coordinate, substitute π flip
    (pderiv (π.symm j) (v ((tetEquiv π flip).symm t) (π.symm j)))) = _
  simp only [substitute, ← map_sum]
  apply congrArg (eval₂Hom C (affineVariable π flip))
  exact Equiv.sum_comp π.symm (fun j : Coordinate =>
    pderiv j (v ((tetEquiv π flip).symm t) j))

theorem pushVelocity_mem {N k : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) (hv : v ∈ velocitySpace N k) :
    pushVelocity π flip v ∈ velocitySpace N k := by
  rcases hv with ⟨hd, hc, hb⟩
  have hm (t : Tet N) (x : Space) (hx : x ∈ tetrahedron t) :
      (pointEquiv π flip).symm x ∈ tetrahedron ((tetEquiv π flip).symm t) := by
    have he := (tetMap_mem π flip ((tetEquiv π flip).symm t)
      ((pointEquiv π flip).symm x)).mp
    rw [← tetEquiv_apply, Equiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply] at he
    exact he hx
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    change (C (orientationSign flip) * substitute π flip
      (v ((tetEquiv π flip).symm t) (π.symm j))).totalDegree ≤ k
    exact (totalDegree_mul _ _).trans (by
      simpa using (substitute_degree π flip _).trans (hd _ _))
  · intro t u x ht hu j
    rw [pushVelocity_eval, pushVelocity_eval,
      hc _ _ _ (hm t x ht) (hm u x hu) (π.symm j)]
  · intro t x ht hx j
    rw [pushVelocity_eval, hb _ _ (hm t x ht)
      ((pointEquiv_boundary_mem π flip ((pointEquiv π flip).symm x)).mp (by simpa using hx))
      (π.symm j), mul_zero]

def velocityMap {N k : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) :
    velocitySpace N k →ₗ[ℝ] velocitySpace N k :=
  ((pushVelocityLinear π flip).comp (velocitySpace N k).subtype).codRestrict _
    (fun v => pushVelocity_mem π flip v.val v.property)

theorem pushPressure_mem {N k : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) (hq : q ∈ pressureSpace N k) :
    pushPressure π flip q ∈ pressureSpace N k := by
  obtain ⟨v, hv, rfl⟩ := hq
  exact ⟨pushVelocity π flip v, pushVelocity_mem π flip v hv,
    divergence_pushVelocity π flip v⟩

def pressureMap {N k : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool) :
    pressureSpace N k →ₗ[ℝ] pressureSpace N k :=
  ((pushPressureLinear π flip).comp (pressureSpace N k).subtype).codRestrict _
    (fun q => pushPressure_mem π flip q.val q.property)

theorem pushPressure_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) : pushPressure π.symm flip (pushPressure π flip q) = q := by
  funext t
  simp only [pushPressure, tetEquiv_symm_apply, Equiv.symm_symm, tetMap_inverse,
    substitute_inverse]

theorem pushVelocity_inverse {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) : pushVelocity π.symm flip (pushVelocity π flip v) = v := by
  funext t j
  apply MvPolynomial.funext
  intro x
  rw [pushVelocity_eval, pushVelocity_eval]
  simp only [tetEquiv_symm_apply, tetMap_inverse, pointEquiv_symm,
    Equiv.symm_symm, Equiv.symm_apply_apply, pointEquiv_inverse]
  have hs : orientationSign flip * orientationSign flip = 1 := by
    simpa [pow_two] using orientationSign_square flip
  rw [← mul_assoc, hs, one_mul]

theorem pushVelocity_gradient_square {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) (t : Tet N) (x : Space) :
    (∑ j : Coordinate, ∑ i : Coordinate,
      (eval x (pderiv i (pushVelocity π flip v t j))) ^ 2) =
      ∑ j : Coordinate, ∑ i : Coordinate,
        (eval ((pointEquiv π flip).symm x)
          (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2 := by
  simp only [pushVelocity_derivative, substitute_eval]
  have hi (j : Coordinate) :
      (∑ i : Coordinate, (eval ((pointEquiv π flip).symm x)
        (pderiv (π.symm i) (v ((tetEquiv π flip).symm t) j))) ^ 2) =
      ∑ i : Coordinate, (eval ((pointEquiv π flip).symm x)
        (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2 :=
    Equiv.sum_comp π.symm (fun i : Coordinate =>
      (eval ((pointEquiv π flip).symm x)
        (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2)
  simp only [hi]
  exact Equiv.sum_comp π.symm (fun j : Coordinate =>
    ∑ i : Coordinate, (eval ((pointEquiv π flip).symm x)
      (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2)

theorem pushPressure_energy {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) : pressureEnergy (pushPressure π flip q) = pressureEnergy q := by
  simp only [pressureEnergy, pushPressure_eval]
  calc
    _ = ∑ t : Tet N, ∫ x in tetrahedron ((tetEquiv π flip).symm t),
        (eval x (q ((tetEquiv π flip).symm t))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact pullback_integral π flip t (fun x =>
        (eval x (q ((tetEquiv π flip).symm t))) ^ 2)
    _ = _ := Equiv.sum_comp (tetEquiv π flip).symm (fun t : Tet N =>
      ∫ x in tetrahedron t, (eval x (q t)) ^ 2)

theorem pushVelocity_energy {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) : velocityEnergy (pushVelocity π flip v) = velocityEnergy v := by
  simp only [velocityEnergy, pushVelocity_gradient_square]
  calc
    _ = ∑ t : Tet N, ∫ x in tetrahedron ((tetEquiv π flip).symm t),
        ∑ j : Coordinate, ∑ i : Coordinate,
          (eval x (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      exact pullback_integral π flip t (fun x => ∑ j : Coordinate, ∑ i : Coordinate,
        (eval x (pderiv i (v ((tetEquiv π flip).symm t) j))) ^ 2)
    _ = _ := Equiv.sum_comp (tetEquiv π flip).symm (fun t : Tet N =>
      ∫ x in tetrahedron t, ∑ j : Coordinate, ∑ i : Coordinate,
        (eval x (pderiv i (v t j))) ^ 2)

theorem pushPressure_element_mean {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (q : BrokenPressure N) (t : Tet N) :
    (∫ x in tetrahedron t, eval x (pushPressure π flip q t)) =
      ∫ x in tetrahedron ((tetEquiv π flip).symm t), eval x (q ((tetEquiv π flip).symm t)) := by
  simp only [pushPressure_eval]
  exact pullback_integral π flip t (fun x => eval x (q ((tetEquiv π flip).symm t)))

theorem pushVelocity_divergence_mean {N : ℕ} (π : Equiv.Perm Coordinate) (flip : Bool)
    (v : BrokenVelocity N) (t : Tet N) :
    (∫ x in tetrahedron t, eval x (divergence N (pushVelocity π flip v) t)) =
      ∫ x in tetrahedron ((tetEquiv π flip).symm t),
        eval x (divergence N v ((tetEquiv π flip).symm t)) := by
  rw [divergence_pushVelocity]
  exact pushPressure_element_mean π flip (divergence N v) t

end FreudenthalSVLean.CubePolynomialTransport
