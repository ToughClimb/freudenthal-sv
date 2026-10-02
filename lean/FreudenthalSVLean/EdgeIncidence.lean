import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Edge-incidence spaces

This module formalizes two finite spanning assertions used in the supported
edge-star lift. The source is `final_submission/paper.tex`, especially the
incidence relations and spanning-pattern tables around lines 888–1069
(author-named copy: `overleaf_single_file/manuscript.tex`, lines 947–1129).

The statements here concern the abstract incidence-coordinate spaces. They do
not yet prove that the displayed vectors arise from the paper's barycentric
face bubbles; that is a later polynomial formalization milestone.
-/

namespace FreudenthalSVLean.EdgeIncidence

/-- The equal-pair pattern for a boundary-face diagonal. -/
def equalPairPattern : Fin 2 → ℚ := ![1, 1]

/-- Every vector satisfying the equal-pair compatibility relation lies in the
span of the explicit equal-pair pattern. -/
theorem equal_pair_spanned (q : Fin 2 → ℚ) (h : q 0 = q 1) :
    ∃ c : ℚ, q = c • equalPairPattern := by
  refine ⟨q 0, ?_⟩
  funext i
  fin_cases i <;> simp [equalPairPattern, h]

/-- First endpoint pattern for the interior face diagonal. -/
def checkerboardPattern₀ : Fin 4 → ℚ := ![-1, -1, 0, 0]

/-- Second endpoint pattern for the interior face diagonal. -/
def checkerboardPattern₁ : Fin 4 → ℚ := ![0, 1, 0, 1]

/-- Third endpoint pattern for the interior face diagonal. -/
def checkerboardPattern₂ : Fin 4 → ℚ := ![1, 0, 1, 0]

/-- Each explicit pattern obeys the checkerboard compatibility relation. -/
theorem checkerboard_patterns_compatible (j : Fin 3) :
    let p := ![checkerboardPattern₀, checkerboardPattern₁, checkerboardPattern₂] j
    p 0 - p 1 - p 2 + p 3 = 0 := by
  fin_cases j
  · change (-1 : ℚ) - (-1) - 0 + 0 = 0
    norm_num
  · change (0 : ℚ) - 1 - 0 + 1 = 0
    norm_num
  · change (1 : ℚ) - 0 - 1 + 0 = 0
    norm_num

/-- The three analytic patterns span exactly the checkerboard hyperplane
`q₀ - q₁ - q₂ + q₃ = 0`. -/
theorem checkerboard_spanned (q : Fin 4 → ℚ)
    (h : q 0 - q 1 - q 2 + q 3 = 0) :
    ∃ α β γ : ℚ,
      q = α • checkerboardPattern₀ + β • checkerboardPattern₁ +
        γ • checkerboardPattern₂ := by
  refine ⟨q 2 - q 0, q 3, q 2, ?_⟩
  funext i
  fin_cases i
  all_goals simp [checkerboardPattern₀, checkerboardPattern₁, checkerboardPattern₂]
  all_goals linarith

end FreudenthalSVLean.EdgeIncidence
