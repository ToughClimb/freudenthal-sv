import FreudenthalSVLean.GlobalElementBubbleLift
import FreudenthalSVLean.MeanPreservingSkeletonLift

/-!
# A uniform actual right inverse on the zero-element-mean pressure image

For the zero-mean residual in the manuscript's main theorem, the fixed
mean-preserving skeleton lift and the fixed global element-bubble lift
compose to a genuine divergence right inverse.  The codomain is the actual
all-point conforming homogeneous velocity space and the energy bound uses
true Lebesgue integrals.  The common constant precedes every `N >= 2`.
The input subspace is explicitly restricted to zero mean on every element;
this theorem does not assert the initial stable mean lift or the full
unrestricted uniform-right-inverse theorem.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.GlobalSkeletonLift
open FreudenthalSVLean.MeanPreservingSkeletonLift
open FreudenthalSVLean.GlobalElementBubbleLift
open FreudenthalSVLean.DivergenceEnergy

noncomputable section

namespace FreudenthalSVLean.ZeroElementMeanRightInverse

set_option backward.isDefEq.respectTransparency false

def zeroElementMeanSpace {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Submodule ℝ (pressureSpace N k) where
  carrier := {q | ∀ t, tetIntegral hN t (q.val t) = 0}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro q r hq hr t
    simp only [Submodule.coe_add, Pi.add_apply, map_add, hq t, hr t, add_zero]
  smul_mem' := by
    intro c q hq t
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, hq t, smul_zero]

def bubbleResidual {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A) :
    zeroElementMeanSpace hN k →ₗ[ℝ] zeroEdgeMeanSpace hN k :=
  ((pressureResidual S).comp (zeroElementMeanSpace hN k).subtype).codRestrict _ (by
    intro q
    constructor
    · intro t a b hab s hs
      exact skeleton_residual_zero_edge S A hS.toSkeletonSpec q.val t a b hab s
    · intro t
      exact (residual_element_mean hN S A hS q.val t).trans (q.property t))

theorem bubbleResidual_val {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A) (q : zeroElementMeanSpace hN k) :
    (bubbleResidual hN S A hS q).val.val = q.val.val - divergence N (S q.val).val := rfl

theorem bubbleResidual_energy {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A) (q : zeroElementMeanSpace hN k) :
    pressureEnergy (bubbleResidual hN S A hS q).val.val ≤
      (2 + 6 * A) * pressureEnergy q.val.val := by
  rw [bubbleResidual_val]
  have hs := pressureEnergy_sub hN q.val.val (divergence N (S q.val).val)
  have hd := divergence_energy_bound hN (S q.val).val
  have hv := hS.energy_bound q.val
  nlinarith

def zeroMeanLift {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A)
    (B : zeroEdgeMeanSpace hN k →ₗ[ℝ] velocitySpace N k) :
    zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k :=
  S.comp (zeroElementMeanSpace hN k).subtype + B.comp (bubbleResidual hN S A hS)

theorem zeroMeanLift_val {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A)
    (B : zeroEdgeMeanSpace hN k →ₗ[ℝ] velocitySpace N k)
    (q : zeroElementMeanSpace hN k) :
    (zeroMeanLift hN S A hS B q).val =
      (S q.val).val + (B (bubbleResidual hN S A hS q)).val := rfl

theorem zeroMeanLift_divergence {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A)
    (B : zeroEdgeMeanSpace hN k →ₗ[ℝ] velocitySpace N k)
    (hB : ∀ q, divergence N (B q).val = q.val.val)
    (q : zeroElementMeanSpace hN k) :
    divergence N (zeroMeanLift hN S A hS B q).val = q.val.val := by
  rw [zeroMeanLift_val, map_add, hB, bubbleResidual_val]
  abel

theorem zeroMeanLift_energy {N k : ℕ} (hN : 0 < N)
    (S : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hS : MeanPreservingSkeletonSpec hN S A)
    (B : zeroEdgeMeanSpace hN k →ₗ[ℝ] velocitySpace N k) (D : ℝ) (hD : 0 ≤ D)
    (hB : ∀ q, velocityEnergy (B q).val ≤ D * pressureEnergy q.val.val)
    (q : zeroElementMeanSpace hN k) :
    velocityEnergy (zeroMeanLift hN S A hS B q).val ≤
      (2 * (A + D * (2 + 6 * A))) * pressureEnergy q.val.val := by
  rw [zeroMeanLift_val]
  have hs := StableCanonicalEdgeLift.add_energy_bound hN (S q.val).val
    (B (bubbleResidual hN S A hS q)).val
  have hv := hS.energy_bound q.val
  have hb := hB (bubbleResidual hN S A hS q)
  have hr := mul_le_mul_of_nonneg_left (bubbleResidual_energy hN S A hS q) hD
  nlinarith

structure ZeroMeanInverseSpec {N k : ℕ} (hN : 0 < N)
    (R : zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  right_inverse : ∀ q, divergence N (R q).val = q.val.val
  energy : ∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val.val

/-- The actual zero-element-mean right inverse is uniformly stable in both
degrees on every `N >= 2`.  No local or global lifting hypothesis is assumed. -/
theorem uniform_zero_element_mean_right_inverse : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ (R₄ : zeroElementMeanSpace (by omega) 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : zeroElementMeanSpace (by omega) 5 →ₗ[ℝ] velocitySpace N 5),
        ZeroMeanInverseSpec (by omega) R₄ C ∧ ZeroMeanInverseSpec (by omega) R₅ C := by
  obtain ⟨A, hA, hS⟩ := uniform_mean_preserving_skeleton_stage
  obtain ⟨B, hB, hJ⟩ := uniform_global_bubble_stage
  refine ⟨2 * (A + B * (2 + 6 * A)), by positivity, ?_⟩
  intro N hN
  have hp : 0 < N := by omega
  obtain ⟨S₄, S₅, hs₄, hs₅⟩ := hS N hN
  obtain ⟨J₄, J₅, hj₄, hj₅, he₄, he₅⟩ := hJ N hp
  exact ⟨zeroMeanLift hp S₄ A hs₄ J₄, zeroMeanLift hp S₅ A hs₅ J₅,
    ⟨zeroMeanLift_divergence hp S₄ A hs₄ J₄ hj₄,
      zeroMeanLift_energy hp S₄ A hs₄ J₄ B hB.le he₄⟩,
    ⟨zeroMeanLift_divergence hp S₅ A hs₅ J₅ hj₅,
      zeroMeanLift_energy hp S₅ A hs₅ J₅ B hB.le he₅⟩⟩

end FreudenthalSVLean.ZeroElementMeanRightInverse
