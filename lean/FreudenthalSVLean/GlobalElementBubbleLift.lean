import FreudenthalSVLean.ElementBubbleAssembly
import FreudenthalSVLean.PressureVertexBound
import FreudenthalSVLean.StarMeanRouting
import FreudenthalSVLean.DivergenceEnergy

/-!
# Uniform global element-bubble lifting in degrees four and five

For manuscript Lemma `bubble` and the main proof's final bubble stage,
actual pressure-image data with zero full edge restrictions and zero
actual element means have a fixed linear conforming bubble lift.  Its
divergence is exactly the input and its true global gradient energy has
one constant before every positive mesh size.  The actual face vanishing
and mesh-intersection arguments establish the codomain, rather than
assuming a zero-extension conformity rule.  This is the bubble stage,
not a right inverse on the unrestricted pressure image.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.StableElementBubbleLift
open FreudenthalSVLean.ElementBubbleAssembly
open FreudenthalSVLean.PressureVertexBound
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.GlobalElementBubbleLift

set_option backward.isDefEq.respectTransparency false

def zeroEdgeMeanSpace {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Submodule ℝ (pressureSpace N k) where
  carrier := {q | (∀ t, zeroScaledEdgeTrace t.2 (cellOrigin t.1) (meshScale N) (q.val t)) ∧
    ∀ t, tetIntegral hN t (q.val t) = 0}
  zero_mem' := by
    constructor
    · intro t a b hab s hs
      simp
    · intro t
      simp
  add_mem' := by
    rintro q r ⟨hq, hqm⟩ ⟨hr, hrm⟩
    constructor
    · intro t a b hab s hs
      simp only [Submodule.coe_add, Pi.add_apply, map_add,
        hq t a b hab s hs, hr t a b hab s hs, add_zero]
    · intro t
      simp only [Submodule.coe_add, Pi.add_apply, map_add, hqm t, hrm t, add_zero]
  smul_mem' := by
    rintro c q ⟨hq, hqm⟩
    constructor
    · intro t a b hab s hs
      simp only [Submodule.coe_smul, Pi.smul_apply, MvPolynomial.smul_eval,
        hq t a b hab s hs, mul_zero]
    · intro t
      simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, hqm t, smul_zero]

def pressureInclusion {N k : ℕ} (hN : 0 < N) :
    zeroEdgeMeanSpace hN k →ₗ[ℝ] BrokenPressure N :=
  (pressureSpace N k).subtype.comp (zeroEdgeMeanSpace hN k).subtype

def quarticFamily (N : ℕ) : LocalFamily N :=
  fun t => quarticVelocityLift t.2 (cellOrigin t.1) (meshScale N)

def quinticFamily (N : ℕ) : LocalFamily N :=
  fun t => quinticVelocityLift t.2 (cellOrigin t.1) (meshScale N)

theorem quarticFamily_degree (N : ℕ) (t : Tet N) (p : ElementBubbleAssembly.Poly)
    (j : Fin 3) : (quarticFamily N t p j).totalDegree ≤ 4 :=
  quarticVelocityLift_degree t.2 (cellOrigin t.1) (meshScale N) p j

theorem quinticFamily_degree (N : ℕ) (t : Tet N) (p : ElementBubbleAssembly.Poly)
    (j : Fin 3) : (quinticFamily N t p j).totalDegree ≤ 5 :=
  quinticVelocityLift_degree t.2 (cellOrigin t.1) (meshScale N) p j

theorem quarticFamily_face_zero (N : ℕ) : FaceZero (quarticFamily N) := by
  intro t p x a ha j
  exact quarticVelocityLift_face_zero t.2 (cellOrigin t.1) x (meshScale N) p a ha j

theorem quinticFamily_face_zero (N : ℕ) : FaceZero (quinticFamily N) := by
  intro t p x a ha j
  exact quinticVelocityLift_face_zero t.2 (cellOrigin t.1) x (meshScale N) p a ha j

def quarticBubbleLift {N : ℕ} (hN : 0 < N) :
    zeroEdgeMeanSpace hN 4 →ₗ[ℝ] velocitySpace N 4 :=
  (assembleVelocity hN (quarticFamily N) (quarticFamily_degree N)
    (quarticFamily_face_zero N)).comp (pressureInclusion hN)

def quinticBubbleLift {N : ℕ} (hN : 0 < N) :
    zeroEdgeMeanSpace hN 5 →ₗ[ℝ] velocitySpace N 5 :=
  (assembleVelocity hN (quinticFamily N) (quinticFamily_degree N)
    (quinticFamily_face_zero N)).comp (pressureInclusion hN)

theorem quarticBubbleLift_val {N : ℕ} (hN : 0 < N)
    (q : zeroEdgeMeanSpace hN 4) :
    (quarticBubbleLift hN q).val = assemble (quarticFamily N) q.val.val := rfl

theorem quinticBubbleLift_val {N : ℕ} (hN : 0 < N)
    (q : zeroEdgeMeanSpace hN 5) :
    (quinticBubbleLift hN q).val = assemble (quinticFamily N) q.val.val := rfl

theorem quarticBubbleLift_divergence {N : ℕ} (hN : 0 < N)
    (q : zeroEdgeMeanSpace hN 4) : divergence N (quarticBubbleLift hN q).val = q.val.val := by
  funext t
  change PolynomialCalculus.polynomialDivergence
    (quarticVelocityLift t.2 (cellOrigin t.1) (meshScale N) (q.val.val t)) = q.val.val t
  exact quarticVelocityLift_divergence _ _ _ (meshScale_pos N hN) _
    (pressure_degree_bound q.val t) (q.property.1 t) (q.property.2 t)

theorem quinticBubbleLift_divergence {N : ℕ} (hN : 0 < N)
    (q : zeroEdgeMeanSpace hN 5) : divergence N (quinticBubbleLift hN q).val = q.val.val := by
  funext t
  change PolynomialCalculus.polynomialDivergence
    (quinticVelocityLift t.2 (cellOrigin t.1) (meshScale N) (q.val.val t)) = q.val.val t
  exact quinticVelocityLift_divergence _ _ _ (meshScale_pos N hN) _
    (pressure_degree_bound q.val t) (q.property.1 t) (q.property.2 t)

theorem quarticBubbleLift_uniform_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (q : zeroEdgeMeanSpace hN 4),
      velocityEnergy (quarticBubbleLift hN q).val ≤ C * pressureEnergy q.val.val := by
  obtain ⟨C, hC, hb⟩ := quarticVelocityLift_energy_bound
  refine ⟨C, hC, ?_⟩
  intro N hN q
  rw [quarticBubbleLift_val]
  apply assemble_energy_bound (quarticFamily N) 3 C _ q.val.val (pressure_degree_bound q.val)
  intro t p hp
  rw [localEnergy_eq_sum hN]
  exact hb t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) p hp

theorem quinticBubbleLift_uniform_energy : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N) (q : zeroEdgeMeanSpace hN 5),
      velocityEnergy (quinticBubbleLift hN q).val ≤ C * pressureEnergy q.val.val := by
  obtain ⟨C, hC, hb⟩ := quinticVelocityLift_energy_bound
  refine ⟨C, hC, ?_⟩
  intro N hN q
  rw [quinticBubbleLift_val]
  apply assemble_energy_bound (quinticFamily N) 4 C _ q.val.val (pressure_degree_bound q.val)
  intro t p hp
  rw [localEnergy_eq_sum hN]
  exact hb t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN) p hp

/-- The global final bubble stage, simultaneously in both degrees and
with a common positive constant before every positive mesh size. -/
theorem uniform_global_bubble_stage : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (hN : 0 < N),
      ∃ (R₄ : zeroEdgeMeanSpace hN 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : zeroEdgeMeanSpace hN 5 →ₗ[ℝ] velocitySpace N 5),
        (∀ q, divergence N (R₄ q).val = q.val.val) ∧
        (∀ q, divergence N (R₅ q).val = q.val.val) ∧
        (∀ q, velocityEnergy (R₄ q).val ≤ C * pressureEnergy q.val.val) ∧
        (∀ q, velocityEnergy (R₅ q).val ≤ C * pressureEnergy q.val.val) := by
  obtain ⟨A, hA, ha⟩ := quarticBubbleLift_uniform_energy
  obtain ⟨B, hB, hb⟩ := quinticBubbleLift_uniform_energy
  refine ⟨A + B, by positivity, ?_⟩
  intro N hN
  refine ⟨quarticBubbleLift hN, quinticBubbleLift hN,
    quarticBubbleLift_divergence hN, quinticBubbleLift_divergence hN, ?_, ?_⟩
  · intro q
    exact (ha N hN q).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hB.le) (DivergenceEnergy.pressureEnergy_nonneg q.val.val))
  · intro q
    exact (hb N hN q).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hA.le) (DivergenceEnergy.pressureEnergy_nonneg q.val.val))

end FreudenthalSVLean.GlobalElementBubbleLift
