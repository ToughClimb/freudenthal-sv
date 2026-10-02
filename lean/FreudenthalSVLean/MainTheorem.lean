import FreudenthalSVLean.BogovskiiHilbertSurjectivity
import FreudenthalSVLean.HilbertInverseReduction
import FreudenthalSVLean.ConformingH1Energy

/-!
# Uniform Freudenthal Scott--Vogelius right inverses for k=4,5

This proves manuscript Theorem `thm:main`, equation `eq:right-inverse`,
for the two newly treated degrees. The spaces are the actual conforming
piecewise polynomial velocity space and its exact spatial divergence
image on every N>=1 Freudenthal cube mesh. Both energies are genuine
Lebesgue integrals of the actual polynomials and derivatives. A single
positive constant precedes every mesh size; on each mesh a single linear
right inverse precedes all pressure inputs.
The full physical H1-energy variant follows from the proved smooth-closure
cube Poincare inequality, with one constant before every positive mesh size.

The continuous cube divergence is genuinely onto by the checked Bogovskii
construction, uniform true-gradient estimates, zero-mean compatibility,
actual L2 convergence, smooth density and complete-space approximation.
Orthogonal-kernel projection supplies one bounded linear continuous
section. Its actual H1_0 representatives and the proved uniform mean Fortin
map supply the initial element means. The supported vertex, edge,
two-cube and element-bubble lifts complete the discrete inverse. The
separate N=1 finite-dimensional true-energy argument covers the small mesh.
No Zhang-specific vertex lemma, assumed rank theorem, continuous-divergence
surjectivity hypothesis, project axiom or unchecked proof oracle is used.
The paper's higher-degree extension is not asserted here.
-/

open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ContinuousInverseReduction
open FreudenthalSVLean.HilbertInverseReduction
open FreudenthalSVLean.BogovskiiHilbertSurjectivity
open FreudenthalSVLean.ConformingH1Energy
open FreudenthalSVLean.DivergenceEnergy

noncomputable section

namespace FreudenthalSVLean.MainTheorem

theorem continuous_cube_right_inverse : HasContinuousCubeRightInverse :=
  continuous_inverse_of_surjective divergenceHilbert_surjective

theorem quartic_uniform_right_inverse : HasUniformRightInverse 4 :=
  quartic_uniform_right_inverse_of_surjective divergenceHilbert_surjective

theorem quintic_uniform_right_inverse : HasUniformRightInverse 5 :=
  quintic_uniform_right_inverse_of_surjective divergenceHilbert_surjective

theorem quartic_quintic_uniform_right_inverse :
    HasUniformRightInverse 4 ∧ HasUniformRightInverse 5 :=
  ⟨quartic_uniform_right_inverse, quintic_uniform_right_inverse⟩

def HasUniformH1RightInverse (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N),
    ∃ R : pressureSpace N k →ₗ[ℝ] velocitySpace N k,
      (∀ q, divergence N (R q).val = q.val) ∧
      (∀ q, h1Energy hN (R q) ≤ C ^ 2 * pressureEnergy q.val)

theorem uniform_h1_right_inverse_of_gradient {k : ℕ}
    (h : HasUniformRightInverse k) : HasUniformH1RightInverse k := by
  obtain ⟨C, hC, hR⟩ := h
  refine ⟨3 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN
  obtain ⟨R, hr, he⟩ := hR N hN
  refine ⟨R, hr, fun q => ?_⟩
  calc
    _ ≤ 5 * velocityEnergy (R q).val := h1Energy_bound hN (R q)
    _ ≤ 5 * (C ^ 2 * pressureEnergy q.val) :=
      mul_le_mul_of_nonneg_left (he q) (by norm_num)
    _ ≤ (3 * C) ^ 2 * pressureEnergy q.val := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (pressureEnergy_nonneg q.val)

theorem quartic_uniform_h1_right_inverse : HasUniformH1RightInverse 4 :=
  uniform_h1_right_inverse_of_gradient quartic_uniform_right_inverse

theorem quintic_uniform_h1_right_inverse : HasUniformH1RightInverse 5 :=
  uniform_h1_right_inverse_of_gradient quintic_uniform_right_inverse

end FreudenthalSVLean.MainTheorem
