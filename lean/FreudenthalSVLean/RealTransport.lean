import FreudenthalSVLean.EdgeIncidence
import FreudenthalSVLean.QuarticBernstein
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Transport of the finite certificates from `ℚ` to `ℝ`

The manuscript's local velocity and pressure spaces are real vector spaces,
whereas the exact certificates in `QuarticMacro.lean`,
`QuarticBernstein.lean`, and `EdgeIncidence.lean` are deliberately computed
over `ℚ`.  All matrix entries, inverse entries, and spanning patterns are
rational.  This module makes the mathematically routine scalar extension
literal in Lean.

The paper sources are `overleaf_single_file/manuscript.tex`, equations
`quartic-mean-matrix`, `edge-checkerboard`, and the spanning-pattern table
around lines 1042--1093.
-/

open Matrix

namespace FreudenthalSVLean.RealTransport

open FreudenthalSVLean.QuarticMacro
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.EdgeIncidence

/-- The quartic mean matrix after the canonical embedding `ℚ ↪ ℝ`. -/
def realQuarticMeanMatrix : Matrix MacroIndex MacroIndex ℝ :=
  quarticMeanMatrix.map fun q => (q : ℝ)

/-- The displayed rational inverse after the canonical embedding `ℚ ↪ ℝ`. -/
def realQuarticMeanMatrixInverse : Matrix MacroIndex MacroIndex ℝ :=
  quarticMeanMatrixInverse.map fun q => (q : ℝ)

/-- The cast inverse is a right inverse over the actual scalar field of the
paper. -/
theorem realQuarticMeanMatrix_mul_inverse :
    realQuarticMeanMatrix * realQuarticMeanMatrixInverse = 1 := by
  change quarticMeanMatrix.map (Rat.castHom ℝ) *
      quarticMeanMatrixInverse.map (Rat.castHom ℝ) = 1
  rw [← Matrix.map_mul]
  rw [quarticMeanMatrix_mul_inverse]
  exact Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))

/-- The cast inverse is also a left inverse over `ℝ`. -/
theorem realQuarticMeanMatrix_inverse_mul :
    realQuarticMeanMatrixInverse * realQuarticMeanMatrix = 1 := by
  change quarticMeanMatrixInverse.map (Rat.castHom ℝ) *
      quarticMeanMatrix.map (Rat.castHom ℝ) = 1
  rw [← Matrix.map_mul]
  rw [quarticMeanMatrix_inverse_mul]
  exact Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))

/-- The exact determinant identity also transports to `ℝ`. -/
theorem realQuarticMeanMatrix_det : realQuarticMeanMatrix.det = -6 := by
  unfold realQuarticMeanMatrix
  rw [← Rat.cast_det quarticMeanMatrix]
  norm_num [quarticMeanMatrix_det]

/-- The scaled Bernstein mean matrix produced semantically in
`QuarticBernstein.lean`, now viewed over `ℝ`. -/
def realBernsteinScaledMeanMatrix : Matrix MacroIndex MacroIndex ℝ :=
  bernsteinScaledMeanMatrix.map fun q => (q : ℝ)

/-- The real Bernstein mean matrix is the real paper matrix. -/
theorem realBernsteinScaledMeanMatrix_eq :
    realBernsteinScaledMeanMatrix = realQuarticMeanMatrix := by
  rw [realBernsteinScaledMeanMatrix, realQuarticMeanMatrix,
    bernsteinScaledMeanMatrix_eq_quarticMeanMatrix]

/-- The rational equal-pair generator viewed in `ℝ²`. -/
def realEqualPairPattern : Fin 2 → ℝ := fun i => (equalPairPattern i : ℝ)

/-- Exact equal-pair spanning over the paper's real scalar field. -/
theorem real_equal_pair_spanned (q : Fin 2 → ℝ) (h : q 0 = q 1) :
    ∃ c : ℝ, q = c • realEqualPairPattern := by
  refine ⟨q 0, ?_⟩
  funext i
  fin_cases i <;> simp [realEqualPairPattern, equalPairPattern, h]

/-- The three rational checkerboard generators viewed in `ℝ⁴`. -/
def realCheckerboardPattern₀ : Fin 4 → ℝ := fun i => (checkerboardPattern₀ i : ℝ)
def realCheckerboardPattern₁ : Fin 4 → ℝ := fun i => (checkerboardPattern₁ i : ℝ)
def realCheckerboardPattern₂ : Fin 4 → ℝ := fun i => (checkerboardPattern₂ i : ℝ)

/-- Each real generator satisfies the checkerboard relation. -/
theorem real_checkerboard_patterns_compatible (j : Fin 3) :
    let p : Fin 4 → ℝ := fun i =>
      ((![checkerboardPattern₀, checkerboardPattern₁, checkerboardPattern₂] j i : ℚ) : ℝ)
    p 0 - p 1 - p 2 + p 3 = 0 := by
  dsimp
  have hq := checkerboard_patterns_compatible j
  dsimp at hq
  exact_mod_cast hq

/-- The three displayed real patterns span exactly the real checkerboard
hyperplane `q₀ - q₁ - q₂ + q₃ = 0`. -/
theorem real_checkerboard_spanned (q : Fin 4 → ℝ)
    (h : q 0 - q 1 - q 2 + q 3 = 0) :
    ∃ α β γ : ℝ,
      q = α • realCheckerboardPattern₀ + β • realCheckerboardPattern₁ +
        γ • realCheckerboardPattern₂ := by
  refine ⟨q 2 - q 0, q 3, q 2, ?_⟩
  funext i
  fin_cases i
  all_goals simp [realCheckerboardPattern₀, realCheckerboardPattern₁,
    realCheckerboardPattern₂, checkerboardPattern₀, checkerboardPattern₁,
    checkerboardPattern₂]
  all_goals linarith

end FreudenthalSVLean.RealTransport
