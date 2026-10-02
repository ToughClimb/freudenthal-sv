import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-!
# Quartic two-cube macroelement matrix

The matrix `quarticMeanMatrix` is the integer matrix `A` displayed in the
quartic two-cube macro lift in `final_submission/paper.tex`, lines 1258–1273
(author-named copy: `overleaf_single_file/manuscript.tex`, lines 1350–1365).

Instead of trusting a determinant computed by an external program, this module
records an explicit rational inverse. Lean checks both matrix products by
kernel reduction and derives `det A ≠ 0` inside the logic. The exact identity
`det A = -6` is independently checked using Mathlib's proved-correct Bird
determinant algorithm. These facts establish the full-rank conclusion used by
the analytic macroelement argument.
-/

open Matrix

namespace FreudenthalSVLean.QuarticMacro

abbrev MacroIndex := Fin 11

/-- Row-major entries of the scaled 11 by 11 mean matrix from the paper. -/
def quarticMeanArray : Array ℚ := #[
  -1,  1,  0, -1,  0,  0,  0,  0,  1,  0,  0,
   1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,
   0, -1,  0,  1,  0,  0,  0,  1,  0,  0,  0,
   0,  0,  1,  1,  0,  0,  0,  0,  0,  0,  0,
   0, -1,  0,  0,  0,  0,  0,  0,  0,  0,  1,
   0,  0,  0, -1,  1,  0,  0,  0,  0,  0,  0,
   0,  0,  0,  0,  0,  1, -1,  0, -1,  1,  0,
   0,  0,  0,  0,  0,  1,  1,  0,  0, -1,  0,
   0,  0,  0,  0,  0, -1, -1, -1,  0,  0,  0,
  -1,  0, -1,  0,  0,  0,  1,  0,  0,  0,  0,
   0,  0,  0,  0,  0, -1,  0,  0,  0, -1, -1]

theorem quarticMeanArray_size : quarticMeanArray.size = 11 * 11 := by
  decide +kernel

/-- The paper matrix, reconstructed from its row-major exact data. -/
def quarticMeanMatrix : Matrix MacroIndex MacroIndex ℚ :=
  Matrix.ofArray quarticMeanArray quarticMeanArray_size

/-- An explicit rational inverse certificate for `quarticMeanMatrix`. -/
def quarticMeanMatrixInverse : Matrix MacroIndex MacroIndex ℚ :=
  ![![-1/2,  0,   0,  -1/2, -1/2, 0, -1/2,  0,   0,  -1/2, -1/2],
    ![ 1/2,  1,   0,   1/2,  1/2, 0,  1/2,  0,   0,   1/2,  1/2],
    ![   0, -1/3, -2/3, 2/3, 1/3, 0,    0, -1/3, -2/3, -1/3, 1/3],
    ![   0,  1/3,  2/3, 1/3,-1/3, 0,    0,  1/3,  2/3,  1/3,-1/3],
    ![   0,  1/3,  2/3, 1/3,-1/3, 1,    0,  1/3,  2/3,  1/3,-1/3],
    ![   0, -1/3,  1/3,-1/3,-2/3, 0,    0,  2/3,  1/3, -1/3,-2/3],
    ![-1/2, -1/3, -2/3, 1/6,-1/6, 0, -1/2, -1/3, -2/3, 1/6,-1/6],
    ![ 1/2,  2/3,  1/3, 1/6, 5/6, 0,  1/2, -1/3, -2/3, 1/6, 5/6],
    ![   0, -2/3,  2/3,-2/3,-4/3, 0,   -1,  1/3,  2/3,-2/3,-4/3],
    ![-1/2, -2/3, -1/3,-1/6,-5/6, 0, -1/2, -2/3, -1/3,-1/6,-5/6],
    ![ 1/2,  1,     0,  1/2, 3/2, 0,  1/2,    0,    0,  1/2, 1/2]]

theorem quarticMeanMatrix_mul_inverse :
    quarticMeanMatrix * quarticMeanMatrixInverse = 1 := by
  decide +kernel

theorem quarticMeanMatrix_inverse_mul :
    quarticMeanMatrixInverse * quarticMeanMatrix = 1 := by
  decide +kernel

/-- The exact determinant printed in the analytic manuscript. The evaluation
is connected to `Matrix.det` by Mathlib's proof of Bird's algorithm and is
performed by kernel reduction, not by `native_decide`. -/
theorem quarticMeanMatrix_det : quarticMeanMatrix.det = -6 := by
  unfold quarticMeanMatrix
  rw [BirdDet.det_eq_birdDet quarticMeanArray quarticMeanArray_size]
  decide +kernel

/-- The determinant is nonzero, which is the full-rank conclusion needed for
the quartic macro lift. -/
theorem quarticMeanMatrix_det_ne_zero : quarticMeanMatrix.det ≠ 0 := by
  intro h
  have hdet := congrArg Matrix.det quarticMeanMatrix_mul_inverse
  simp [Matrix.det_mul, h] at hdet

end FreudenthalSVLean.QuarticMacro
