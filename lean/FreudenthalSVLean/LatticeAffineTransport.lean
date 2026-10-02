import FreudenthalSVLean.PolynomialChainTransport
import FreudenthalSVLean.GridNodalSupport
import FreudenthalSVLean.VelocityEnergy

/-!
# Actual lattice translations and coordinate-permutation transport

For manuscript equation `macro-scale` and Lemma `macro`, a translated
coordinate permutation maps every closed lattice tetrahedron to the
corresponding closed lattice tetrahedron.  Actual nodal polynomials,
spatial divergence, volume integration and the full gradient energy
are transported by proved affine substitutions and measure-preserving
equivalences.  All origins and permutations are arbitrary; no sampled
mesh supplies these geometric identities.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.GridNodalSupport
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.LatticeAffineTransport

def affineNode (π : Equiv.Perm Coordinate) (o n : Coordinate → ℤ) : Coordinate → ℤ :=
  fun j => n (π.symm j) + o j

def inverseNode (π : Equiv.Perm Coordinate) (o n : Coordinate → ℤ) : Coordinate → ℤ :=
  fun j => n (π j) - o (π j)

theorem affineNode_inverse (π : Equiv.Perm Coordinate) (o n : Coordinate → ℤ) :
    affineNode π o (inverseNode π o n) = n := by
  funext j
  simp [affineNode, inverseNode]

theorem inverseNode_affine (π : Equiv.Perm Coordinate) (o n : Coordinate → ℤ) :
    inverseNode π o (affineNode π o n) = n := by
  funext j
  simp [affineNode, inverseNode]

theorem affineNode_injective (π : Equiv.Perm Coordinate) (o : Coordinate → ℤ) :
    Function.Injective (affineNode π o) := by
  intro n m he
  have h := congrArg (inverseNode π o) he
  simpa only [inverseNode_affine] using h

theorem affineNode_intPoint (π : Equiv.Perm Coordinate) (o n : Coordinate → ℤ) :
    intPoint (affineNode π o n) = (unitNormalize π (intPoint o)).symm (intPoint n) := by
  funext j
  simp [intPoint, affineNode, unitNormalize_symm_apply]

theorem affine_vertex (π σ : Equiv.Perm Coordinate) (o c : Space) (a : Vertex) :
    chainVertex (σ.trans π) ((unitNormalize π o).symm c) a =
      (unitNormalize π o).symm (chainVertex σ c a) := by
  funext j
  simp only [chainVertex, unitNormalize_symm_apply, Equiv.symm_trans_apply]
  change c (π.symm j) + o j +
      (if (σ.symm (π.symm j)).val < a.val then (1 : ℝ) else 0) =
    (c (π.symm j) + (if (σ.symm (π.symm j)).val < a.val then (1 : ℝ) else 0)) + o j
  ring

theorem normalize_composition (π σ : Equiv.Perm Coordinate) (o c x : Space) :
    unitNormalize (σ.trans π) ((unitNormalize π o).symm c) x =
      unitNormalize σ c (unitNormalize π o x) := by
  funext j
  simp only [unitNormalize_apply, unitNormalize_symm_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  ring

theorem affine_chain_mem (π σ : Equiv.Perm Coordinate) (o c x : Space) :
    x ∈ unitChainSet (σ.trans π) ((unitNormalize π o).symm c) ↔
      unitNormalize π o x ∈ unitChainSet σ c := by
  change unitNormalize (σ.trans π) ((unitNormalize π o).symm c) x ∈ coordinateChainSet ↔ _
  rw [normalize_composition]
  rfl

theorem affine_chain_set (π σ : Equiv.Perm Coordinate) (o c : Space) :
    unitChainSet (σ.trans π) ((unitNormalize π o).symm c) =
      (unitNormalize π o) ⁻¹' unitChainSet σ c := by
  ext x
  exact affine_chain_mem π σ o c x

theorem affine_integral (π σ : Equiv.Perm Coordinate) (o c : Space) (f : Space → ℝ) :
    (∫ x in unitChainSet (σ.trans π) ((unitNormalize π o).symm c),
      f (unitNormalize π o x)) = ∫ y in unitChainSet σ c, f y := by
  rw [affine_chain_set]
  exact (unitNormalize_preserving π o).setIntegral_preimage_emb
    (unitNormalize π o).measurableEmbedding f (unitChainSet σ c)

theorem forward_affine_barycentric (π σ : Equiv.Perm Coordinate) (o c : Space) (a : Vertex) :
    forward π o (barycentric σ c a) =
      barycentric (σ.trans π) ((unitNormalize π o).symm c) a := by
  apply MvPolynomial.funext
  intro x
  rw [forward_eval, unitBarycentric_normalize σ c (unitNormalize π o x) a,
    unitBarycentric_normalize (σ.trans π) ((unitNormalize π o).symm c) x a,
    normalize_composition]

/-- All lattice nodal hats obey the same affine polynomial transport,
including zero polynomials for missing vertices. -/
theorem nodalPolynomial_affine (π σ : Equiv.Perm Coordinate) (o c n : Coordinate → ℤ) :
    nodalPolynomial (σ.trans π) (affineNode π o c) (affineNode π o n) =
      forward π (intPoint o) (nodalPolynomial σ c n) := by
  simp only [nodalPolynomial, forward, map_sum, apply_ite, map_zero,
    affineNode_intPoint, affine_vertex]
  apply Finset.sum_congr rfl
  intro a _
  have he : (unitNormalize π (intPoint o)).symm (intPoint n) =
      (unitNormalize π (intPoint o)).symm (chainVertex σ (intPoint c) a) ↔
      intPoint n = chainVertex σ (intPoint c) a :=
    (unitNormalize π (intPoint o)).symm.injective.eq_iff
  by_cases hn : intPoint n = chainVertex σ (intPoint c) a
  · simp only [hn, if_true]
    exact (forward_affine_barycentric π σ (intPoint o) (intPoint c) a).symm
  · simp only [he, hn, if_false]

theorem nodalPolynomial_inverse_affine (π σ : Equiv.Perm Coordinate)
    (o c n : Coordinate → ℤ) :
    nodalPolynomial σ c (affineNode π o n) =
      forward π (intPoint o) (nodalPolynomial (σ.trans π.symm) (inverseNode π o c) n) := by
  rw [← nodalPolynomial_affine, affineNode_inverse]
  have he : (σ.trans π.symm).trans π = σ := by ext j; simp
  rw [he]

theorem affine_polynomial_integral (π σ : Equiv.Perm Coordinate) (o c : Space)
    (p : MvPolynomial Coordinate ℝ) :
    (∫ x in unitChainSet (σ.trans π) ((unitNormalize π o).symm c),
      eval x (forward π o p)) = ∫ y in unitChainSet σ c, eval y p := by
  simp only [forward_eval]
  exact affine_integral π σ o c (fun y => eval y p)

theorem affine_gradient_density (π : Equiv.Perm Coordinate) (o : Space)
    (v : LocalVelocity) (x : Space) :
    gradientDensity (pushVector π o v) x = gradientDensity v (unitNormalize π o x) := by
  simp only [gradientDensity, pushVector, pderiv_forward, forward_eval]
  calc
    _ = ∑ e : Coordinate × Coordinate,
        (eval (unitNormalize π o x) (pderiv e.2 (v e.1))) ^ 2 :=
      (π.symm.prodCongr π.symm).sum_comp
        (fun e => (eval (unitNormalize π o x) (pderiv e.2 (v e.1))) ^ 2)
    _ = _ := rfl

/-- True gradient energy is invariant under every lattice translation and
coordinate permutation, simultaneously for all nine gradient entries. -/
theorem affine_vector_energy (π σ : Equiv.Perm Coordinate) (o c : Space)
    (v : LocalVelocity) :
    (∫ x in unitChainSet (σ.trans π) ((unitNormalize π o).symm c),
      gradientDensity (pushVector π o v) x) =
      ∫ y in unitChainSet σ c, gradientDensity v y := by
  simp only [affine_gradient_density]
  exact affine_integral π σ o c (gradientDensity v)

/-- Integrating the actual gradient density equals the sum of the nine
actual derivative square integrals on every compact unit tetrahedron. -/
theorem unitGradientIntegral_eq_sum (σ : Equiv.Perm Coordinate) (c : Space) (v : LocalVelocity) :
    (∫ x in unitChainSet σ c, gradientDensity v x) =
      ∑ j : Coordinate, ∑ i : Coordinate,
        ∫ x in unitChainSet σ c, (eval x (pderiv i (v j))) ^ 2 := by
  have hv (e : Coordinate × Coordinate) :
      IntegrableOn (fun x => (eval x (pderiv e.2 (v e.1))) ^ 2) (unitChainSet σ c) :=
    ((continuous_eval _).pow 2).continuousOn.integrableOn_compact
      (μ := volume) (unitChainSet_isCompact σ c)
  unfold gradientDensity
  rw [integral_finsetSum _ (fun e _ => hv e)]
  exact Fintype.sum_prod_type _

end FreudenthalSVLean.LatticeAffineTransport
