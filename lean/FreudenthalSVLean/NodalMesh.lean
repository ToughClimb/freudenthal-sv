import FreudenthalSVLean.GridNodalSupport
import FreudenthalSVLean.PolynomialScaling

/-!
# Actual global nodal data on every mesh

This module implements the nodal functions used in manuscript
`vertex-raw-bubble` as spatial polynomials on every arbitrary-`N` mesh.
Their common global expression proves conformity at every shared point,
not merely on a list of sampled faces.  The integer lattice proof in
`GridNodalSupport` proves local support, and the coordinate range proves
vanishing on a physical boundary plane not containing the node.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GridNodal
open FreudenthalSVLean.GridNodalSupport
open FreudenthalSVLean.PolynomialScaling

noncomputable section

namespace FreudenthalSVLean.NodalMesh

def cellIntOrigin {N : ℕ} (c : Cell N) : Fin 3 → ℤ := fun j => (c j).val

theorem intPoint_cellIntOrigin {N : ℕ} (c : Cell N) :
    intPoint (cellIntOrigin c) = cellOrigin c := by
  funext j
  simp [intPoint, cellIntOrigin, cellOrigin]

def meshNodalPolynomial {N : ℕ} (t : Tet N) (n : Fin 3 → ℤ) :
    MvPolynomial (Fin 3) ℝ :=
  rescale (meshScale N) 1 (nodalPolynomial t.2 (cellIntOrigin t.1) n)

def meshNodal (N : ℕ) (n : Fin 3 → ℤ) (x : Space) : ℝ :=
  nodal (intPoint n) ((meshScale N)⁻¹ • x)

theorem meshNodalPolynomial_eval {N : ℕ} (t : Tet N) (n : Fin 3 → ℤ)
    (x : Space) (hx : x ∈ tetrahedron t) :
    eval x (meshNodalPolynomial t n) = meshNodal N n x := by
  rw [meshNodalPolynomial, rescale_eval, one_mul]
  apply nodalPolynomial_eval
  change (meshScale N)⁻¹ • x ∈ unitChainSet t.2 (cellOrigin t.1) at hx
  simpa only [intPoint_cellIntOrigin] using hx

theorem meshNodalPolynomial_degree_le {N : ℕ} (t : Tet N) (n : Fin 3 → ℤ) :
    (meshNodalPolynomial t n).totalDegree ≤ 1 :=
  (rescale_degree_le _ _ _).trans (nodalPolynomial_degree_le _ _ _)

theorem meshNodalPolynomial_conforming {N : ℕ} (t u : Tet N) (n : Fin 3 → ℤ)
    (x : Space) (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) :
    eval x (meshNodalPolynomial t n) = eval x (meshNodalPolynomial u n) := by
  rw [meshNodalPolynomial_eval t n x ht, meshNodalPolynomial_eval u n x hu]

theorem meshNodalPolynomial_eq_barycentric {N : ℕ} (t : Tet N) (n : Fin 3 → ℤ)
    (a : Fin 4) (hn : intPoint n = ChainGeometry.chainVertex t.2 (cellOrigin t.1) a) :
    meshNodalPolynomial t n = barycentric t a := by
  rw [meshNodalPolynomial, nodalPolynomial_eq_barycentric t.2 (cellIntOrigin t.1) n a
    (by simpa only [intPoint_cellIntOrigin] using hn)]
  simp [rescale, barycentric, scaledBarycentric, intPoint_cellIntOrigin]

theorem meshNodalPolynomial_zero_of_not_vertex {N : ℕ} (t : Tet N) (n : Fin 3 → ℤ)
    (hn : ∀ a : Fin 4, intPoint n ≠ ChainGeometry.chainVertex t.2 (cellOrigin t.1) a) :
    meshNodalPolynomial t n = 0 := by
  simp [meshNodalPolynomial, nodalPolynomial, intPoint_cellIntOrigin, hn, rescale]

def nodeInBox (N : ℕ) (n : Fin 3 → ℤ) : Prop :=
  ∀ j : Fin 3, 0 ≤ n j ∧ n j ≤ (N : ℤ)

theorem meshNodal_zero_lower {N : ℕ} (n : Fin 3 → ℤ) (hn : nodeInBox N n)
    (x : Space) (j : Fin 3) (hx : x j = 0) (hnj : n j ≠ 0) :
    meshNodal N n x = 0 := by
  apply hat_zero_of_le_neg_one _ j
  have hni : (1 : ℤ) ≤ n j := by have h := (hn j).1; omega
  have hnr : (1 : ℝ) ≤ (n j : ℝ) := by exact_mod_cast hni
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intPoint, hx, mul_zero]
  linarith

theorem meshNodal_zero_upper {N : ℕ} (_hN : 0 < N) (n : Fin 3 → ℤ)
    (hn : nodeInBox N n) (x : Space) (j : Fin 3) (hx : x j = 1) (hnj : n j ≠ (N : ℤ)) :
    meshNodal N n x = 0 := by
  apply hat_zero_of_ge_one _ j
  have hni : n j ≤ (N : ℤ) - 1 := by have h := (hn j).2; omega
  have hnr : (n j : ℝ) ≤ (N : ℝ) - 1 := by exact_mod_cast hni
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, intPoint, meshScale,
    inv_inv, hx, mul_one]
  linarith

end FreudenthalSVLean.NodalMesh
