import FreudenthalSVLean.ZeroElementMeanRightInverse
import FreudenthalSVLean.FixedMeshRightInverse

/-!
# Exact reduction of the uniform theorem to initial element-mean lifting

For the manuscript's main proof, an initial fixed linear map need only
match the true divergence mean on every element with one uniform energy
bound.  The proved zero-element-mean right inverse then completes the
actual divergence inverse.  The separate fixed-mesh theorem treats `N=1`.
For both `k=4` and `k=5`, this module proves an equivalence between the
unrestricted discrete uniform target and that precise initial mean-lift
statement. The initial statement is proved from the genuine continuous
inverse and uniform mean Fortin map; `MainTheorem` instantiates this
equivalence. No initial lift is assumed as a project axiom.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.GlobalSkeletonLift
open FreudenthalSVLean.ZeroElementMeanRightInverse
open FreudenthalSVLean.FixedMeshRightInverse
open FreudenthalSVLean.DivergenceEnergy

noncomputable section

namespace FreudenthalSVLean.UniformMeanLiftReduction

set_option backward.isDefEq.respectTransparency false

structure InitialMeanLiftSpec {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  match_means : ∀ q t, tetIntegral hN t (divergence N (M q).val t) = tetIntegral hN t (q.val t)
  energy : ∀ q, velocityEnergy (M q).val ≤ C * pressureEnergy q.val

def HasUniformInitialMeanLift (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
    ∃ M : pressureSpace N k →ₗ[ℝ] velocitySpace N k, InitialMeanLiftSpec (by omega) M C

def meanResidual {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A) :
    pressureSpace N k →ₗ[ℝ] zeroElementMeanSpace hN k :=
  (pressureResidual M).codRestrict _ (by
    intro q t
    rw [pressureResidual_val]
    simp only [Pi.sub_apply, map_sub, hM.match_means q t, sub_self])

theorem meanResidual_val {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A) (q : pressureSpace N k) :
    (meanResidual hN M A hM q).val.val = q.val - divergence N (M q).val := rfl

theorem meanResidual_energy {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A) (q : pressureSpace N k) :
    pressureEnergy (meanResidual hN M A hM q).val.val ≤ (2 + 6 * A) * pressureEnergy q.val := by
  rw [meanResidual_val]
  have hs := pressureEnergy_sub hN q.val (divergence N (M q).val)
  have hd := divergence_energy_bound hN (M q).val
  have hv := hM.energy q
  nlinarith

def completeLift {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A)
    (Z : zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k) :
    pressureSpace N k →ₗ[ℝ] velocitySpace N k := M + Z.comp (meanResidual hN M A hM)

theorem completeLift_val {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A)
    (Z : zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k) (q : pressureSpace N k) :
    (completeLift hN M A hM Z q).val = (M q).val + (Z (meanResidual hN M A hM q)).val := rfl

theorem completeLift_divergence {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A)
    (Z : zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k)
    (hZ : ∀ q, divergence N (Z q).val = q.val.val) (q : pressureSpace N k) :
    divergence N (completeLift hN M A hM Z q).val = q.val := by
  rw [completeLift_val, map_add, hZ, meanResidual_val]
  abel

theorem completeLift_energy {N k : ℕ} (hN : 0 < N)
    (M : pressureSpace N k →ₗ[ℝ] velocitySpace N k) (A : ℝ)
    (hM : InitialMeanLiftSpec hN M A)
    (Z : zeroElementMeanSpace hN k →ₗ[ℝ] velocitySpace N k) (B : ℝ) (hB : 0 ≤ B)
    (hZ : ∀ q, velocityEnergy (Z q).val ≤ B * pressureEnergy q.val.val)
    (q : pressureSpace N k) :
    velocityEnergy (completeLift hN M A hM Z q).val ≤
      (2 * (A + B * (2 + 6 * A))) * pressureEnergy q.val := by
  rw [completeLift_val]
  have hs := StableCanonicalEdgeLift.add_energy_bound hN (M q).val
    (Z (meanResidual hN M A hM q)).val
  have hv := hM.energy q
  have hz := hZ (meanResidual hN M A hM q)
  have hr := mul_le_mul_of_nonneg_left (meanResidual_energy hN M A hM q) hB
  nlinarith

theorem uniform_initial_mean_lift_of_right_inverse (k : ℕ)
    (h : HasUniformRightInverse k) : HasUniformInitialMeanLift k := by
  obtain ⟨C, hC, hR⟩ := h
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro N hN
  obtain ⟨R, hr, he⟩ := hR N (by omega)
  refine ⟨R, ⟨?_, he⟩⟩
  intro q t
  rw [hr q]

/-- Composition of the initial mean lift and the zero-element-mean inverse,
with the separate small mesh and all true-energy bounds discharged.
The hypotheses are instantiated in `MainTheorem`. -/
theorem uniform_right_inverse_of_initial_mean_lift (k : ℕ)
    (hM : HasUniformInitialMeanLift k)
    (hZ : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ Z : zeroElementMeanSpace (by omega) k →ₗ[ℝ] velocitySpace N k,
        ZeroMeanInverseSpec (by omega) Z C) : HasUniformRightInverse k := by
  obtain ⟨A, hA, hMean⟩ := hM
  obtain ⟨B, hB, hZero⟩ := hZ
  obtain ⟨R₁, C₁, hC₁, hr₁, he₁⟩ := unit_mesh_right_inverse k
  let D : ℝ := 2 * (A + B * (2 + 6 * A))
  have hD : 0 < D := by dsimp [D]; positivity
  let C : ℝ := 1 + D + C₁
  have hC : 0 < C := by dsimp [C]; linarith
  have hdC : D ≤ C ^ 2 := by dsimp [C]; nlinarith
  have h₁C : C₁ ≤ C ^ 2 := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro N hN
  by_cases h2 : 2 ≤ N
  · obtain ⟨M, hm⟩ := hMean N h2
    obtain ⟨Z, hz⟩ := hZero N h2
    refine ⟨completeLift hN M A hm Z, completeLift_divergence hN M A hm Z hz.right_inverse, ?_⟩
    intro q
    exact (completeLift_energy hN M A hm Z B hB.le hz.energy q).trans
      (mul_le_mul_of_nonneg_right hdC (pressureEnergy_nonneg q.val))
  · have hn : N = 1 := by omega
    subst N
    refine ⟨R₁, hr₁, ?_⟩
    intro q
    exact (he₁ q).trans (mul_le_mul_of_nonneg_right h₁C (pressureEnergy_nonneg q.val))

theorem quartic_uniform_right_inverse_iff_initial_mean_lift :
    HasUniformRightInverse 4 ↔ HasUniformInitialMeanLift 4 := by
  constructor
  · exact uniform_initial_mean_lift_of_right_inverse 4
  · intro hm
    apply uniform_right_inverse_of_initial_mean_lift 4 hm
    obtain ⟨C, hC, hZ⟩ := uniform_zero_element_mean_right_inverse
    refine ⟨C, hC, ?_⟩
    intro N hN
    obtain ⟨Z₄, Z₅, hz₄, hz₅⟩ := hZ N hN
    exact ⟨Z₄, hz₄⟩

theorem quintic_uniform_right_inverse_iff_initial_mean_lift :
    HasUniformRightInverse 5 ↔ HasUniformInitialMeanLift 5 := by
  constructor
  · exact uniform_initial_mean_lift_of_right_inverse 5
  · intro hm
    apply uniform_right_inverse_of_initial_mean_lift 5 hm
    obtain ⟨C, hC, hZ⟩ := uniform_zero_element_mean_right_inverse
    refine ⟨C, hC, ?_⟩
    intro N hN
    obtain ⟨Z₄, Z₅, hz₄, hz₅⟩ := hZ N hN
    exact ⟨Z₅, hz₅⟩

end FreudenthalSVLean.UniformMeanLiftReduction
