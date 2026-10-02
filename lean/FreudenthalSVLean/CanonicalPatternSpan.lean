import FreudenthalSVLean.CanonicalFacePatterns
import FreudenthalSVLean.FiniteLinearLifting
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Explicit bounded canonical incidence inverses

For the spanning step in manuscript Lemma `edge-star`, the geometry-derived
face patterns have explicit integer right inverses on the zero, equal-pair,
checkerboard, and unrestricted source spaces.  The certificate is the
structural identity `B J + V W = I` together with `W B = 0`, where `W` is
the stated source relation.  It proves an actual inverse on `ker W`, not
only a numerical rank equality.  All finite identities are checked in the
Lean kernel over integers and transported by ring homomorphism to reals.

The inverses are fixed linear maps, and finite-dimensional norm theory
gives one positive coefficient bound before all seven types and both
endpoints.  Actual pressure compatibility and physical face realization
are separate obligations.
-/

open scoped BigOperators Matrix
open FreudenthalSVLean.CanonicalFacePatterns
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.FiniteLinearLifting

noncomputable section

namespace FreudenthalSVLean.CanonicalPatternSpan

def constraintWeights (c : Fin 7) (i : Fin 6) : ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0], ![1, -1, -1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] c i

def correctionVector (c : Fin 7) (i : Fin 6) : ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] c i

def inverseEntry (c : Fin 7) (side : Bool) (p i : Fin 6) : ℤ :=
  if side then
    ![fun _ => 0,
      ![![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], 0, 0, 0, 0],
      ![![1, 0, 0, 0, 0, 0], 0, 0, 0, 0, 0],
      ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, 1, 0, 0, 0, 0], 0, 0, 0],
      ![![-1, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, -1, 0, 0, 0], 0, 0, 0],
      ![![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1], ![0, 0, -1, 0, 0, 0],
        ![0, 0, 0, -1, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0]],
      ![![0, 1, -1, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![1, 0, 0, -1, 0, 0],
        ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0]]] c p i
  else
    ![fun _ => 0,
      ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], 0, 0, 0, 0],
      ![![1, 0, 0, 0, 0, 0], 0, 0, 0, 0, 0],
      ![![1, 0, 0, 0, 0, 0], ![1, -1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0], 0, 0, 0],
      ![![-1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], 0, 0, 0],
      ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
        ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]],
      ![![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, -1],
        ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, -1, 0], ![0, 0, 0, 1, 0, 0]]] c p i

def integerPatternMatrix (c : Fin 7) (side : Bool) :
    Matrix (Fin (incidenceValence c)) (Fin (patternCount c)) ℤ :=
  fun i p => expectedPattern c side (p.castLE (patternCount_le_six c))
    (i.castLE (incidenceValence_le_six c))

def integerInverseMatrix (c : Fin 7) (side : Bool) :
    Matrix (Fin (patternCount c)) (Fin (incidenceValence c)) ℤ :=
  fun p i => inverseEntry c side (p.castLE (patternCount_le_six c))
    (i.castLE (incidenceValence_le_six c))

def integerConstraintMatrix (c : Fin 7) : Matrix (Fin 1) (Fin (incidenceValence c)) ℤ :=
  fun _ i => constraintWeights c (i.castLE (incidenceValence_le_six c))

def integerCorrectionMatrix (c : Fin 7) : Matrix (Fin (incidenceValence c)) (Fin 1) ℤ :=
  fun i _ => correctionVector c (i.castLE (incidenceValence_le_six c))

theorem integer_inverse_identity : ∀ (c : Fin 7) (side : Bool),
    integerPatternMatrix c side * integerInverseMatrix c side +
      integerCorrectionMatrix c * integerConstraintMatrix c = 1 := by
  decide +kernel

theorem integer_compatibility_identity : ∀ (c : Fin 7) (side : Bool),
    integerConstraintMatrix c * integerPatternMatrix c side = 0 := by
  decide +kernel

def realPatternMatrix (c : Fin 7) (side : Bool) :
    Matrix (Fin (incidenceValence c)) (Fin (patternCount c)) ℝ :=
  (integerPatternMatrix c side).map (Int.castRingHom ℝ)

def realInverseMatrix (c : Fin 7) (side : Bool) :
    Matrix (Fin (patternCount c)) (Fin (incidenceValence c)) ℝ :=
  (integerInverseMatrix c side).map (Int.castRingHom ℝ)

def realConstraintMatrix (c : Fin 7) : Matrix (Fin 1) (Fin (incidenceValence c)) ℝ :=
  (integerConstraintMatrix c).map (Int.castRingHom ℝ)

def realCorrectionMatrix (c : Fin 7) : Matrix (Fin (incidenceValence c)) (Fin 1) ℝ :=
  (integerCorrectionMatrix c).map (Int.castRingHom ℝ)

theorem real_inverse_identity (c : Fin 7) (side : Bool) :
    realPatternMatrix c side * realInverseMatrix c side +
      realCorrectionMatrix c * realConstraintMatrix c = 1 := by
  unfold realPatternMatrix realInverseMatrix realCorrectionMatrix realConstraintMatrix
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, integer_inverse_identity]
  exact Matrix.map_one _ (map_zero (Int.castRingHom ℝ)) (map_one (Int.castRingHom ℝ))
  exact fun a b => map_add (Int.castRingHom ℝ) a b

theorem real_compatibility_identity (c : Fin 7) (side : Bool) :
    realConstraintMatrix c * realPatternMatrix c side = 0 := by
  unfold realPatternMatrix realConstraintMatrix
  rw [← Matrix.map_mul, integer_compatibility_identity]
  exact Matrix.map_zero _ (map_zero (Int.castRingHom ℝ))

def patternMap (c : Fin 7) (side : Bool) :
    (Fin (patternCount c) → ℝ) →ₗ[ℝ] (Fin (incidenceValence c) → ℝ) :=
  (realPatternMatrix c side).mulVecLin

def inverseMap (c : Fin 7) (side : Bool) :
    (Fin (incidenceValence c) → ℝ) →ₗ[ℝ] (Fin (patternCount c) → ℝ) :=
  (realInverseMatrix c side).mulVecLin

def sourceSpace (c : Fin 7) : Submodule ℝ (Fin (incidenceValence c) → ℝ) :=
  (realConstraintMatrix c).mulVecLin.ker

theorem mem_source_iff (c : Fin 7) (q : Fin (incidenceValence c) → ℝ) :
    q ∈ sourceSpace c ↔
      (∑ i : Fin (incidenceValence c),
        (constraintWeights c (i.castLE (incidenceValence_le_six c)) : ℝ) * q i) = 0 := by
  change realConstraintMatrix c *ᵥ q = 0 ↔ _
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext j
    exact h

theorem zero_source_iff (q : Fin (incidenceValence 0) → ℝ) :
    q ∈ sourceSpace 0 ↔ q 0 = 0 := by
  rw [mem_source_iff]
  change (∑ i : Fin 1, (constraintWeights 0 (i.castLE (incidenceValence_le_six 0)) : ℝ) * q i) = 0 ↔ _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1 : ℤ) : ℝ) * q 0 = 0 ↔ q 0 = 0
  simp

theorem equal_pair_source_iff (q : Fin (incidenceValence 2) → ℝ) :
    q ∈ sourceSpace 2 ↔ q 0 = q 1 := by
  rw [mem_source_iff]
  change (∑ i : Fin 2, (constraintWeights 2 (i.castLE (incidenceValence_le_six 2)) : ℝ) * q i) = 0 ↔ _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1 : ℤ) : ℝ) * q 0 + ((-1 : ℤ) : ℝ) * q 1 = 0 ↔ q 0 = q 1
  norm_num
  constructor <;> intro h <;> linarith

theorem checkerboard_source_iff (q : Fin (incidenceValence 4) → ℝ) :
    q ∈ sourceSpace 4 ↔ q 0 - q 1 - q 2 + q 3 = 0 := by
  rw [mem_source_iff]
  change (∑ i : Fin 4, (constraintWeights 4 (i.castLE (incidenceValence_le_six 4)) : ℝ) * q i) = 0 ↔ _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1 : ℤ) : ℝ) * q 0 +
    (((-1 : ℤ) : ℝ) * q 1 + (((-1 : ℤ) : ℝ) * q 2 + ((1 : ℤ) : ℝ) * q 3)) = 0 ↔ _
  norm_num
  constructor <;> intro h <;> linarith

theorem unrestricted_constraint : ∀ c : Fin 7, c ≠ 0 → c ≠ 2 → c ≠ 4 →
    integerConstraintMatrix c = 0 := by
  decide +kernel

theorem unrestricted_source (c : Fin 7) (h₀ : c ≠ 0) (h₂ : c ≠ 2) (h₄ : c ≠ 4) :
    sourceSpace c = ⊤ := by
  unfold sourceSpace realConstraintMatrix
  rw [unrestricted_constraint c h₀ h₂ h₄, Matrix.map_zero _ (map_zero (Int.castRingHom ℝ)),
    Matrix.mulVecLin_zero, LinearMap.ker_zero]

theorem pattern_mem_source (c : Fin 7) (side : Bool) (x : Fin (patternCount c) → ℝ) :
    patternMap c side x ∈ sourceSpace c := by
  change realConstraintMatrix c *ᵥ (realPatternMatrix c side *ᵥ x) = 0
  rw [Matrix.mulVec_mulVec, real_compatibility_identity, Matrix.zero_mulVec]

theorem inverse_on_source (c : Fin 7) (side : Bool) (q : sourceSpace c) :
    patternMap c side (inverseMap c side q.val) = q.val := by
  have hq : realConstraintMatrix c *ᵥ q.val = 0 := q.property
  have h := congrArg (fun A => A *ᵥ q.val) (real_inverse_identity c side)
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hq, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

theorem pattern_range_eq_source (c : Fin 7) (side : Bool) :
    (patternMap c side).range = sourceSpace c := by
  apply Submodule.ext
  intro q
  constructor
  · rintro ⟨x, rfl⟩
    exact pattern_mem_source c side x
  · intro hq
    exact ⟨inverseMap c side q, inverse_on_source c side ⟨q, hq⟩⟩

/-- The explicit inverse family is uniformly bounded before geometry
type, endpoint, and all input data. -/
theorem fixed_inverse_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (c : Fin 7) (side : Bool) (q : sourceSpace c), ‖inverseMap c side q.val‖ ≤ C * ‖q‖ := by
  obtain ⟨C, hC, hb⟩ := finite_family_map_bounds
    (fun cs : Fin 7 × Bool => Fin (incidenceValence cs.1) → ℝ)
    (fun cs : Fin 7 × Bool => Fin (patternCount cs.1) → ℝ)
    (fun cs => inverseMap cs.1 cs.2)
  exact ⟨C, hC, fun c side q => hb (c, side) q.val⟩

end FreudenthalSVLean.CanonicalPatternSpan
