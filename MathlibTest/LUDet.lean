module

import Mathlib.Tactic.LUDet
import Mathlib.LinearAlgebra.Matrix.Notation

example : Matrix.det (R := ℚ) !![1, 2; 3, 4] = -2 := by
  lu_det

example : Matrix.det (R := ℚ) !![5] = 5 := by
  lu_det

example : Matrix.det (R := ℚ) !![1/2, 2; 3, 4] = -4 := by
  lu_det

example : Matrix.det (R := ℚ) !![1, 2, 3; 4, 5, 6; 7, 8, 10] = -3 := by
  lu_det

-- singular
example : Matrix.det (R := ℚ) !![1, 2; 2, 4] = 0 := by
  lu_det

-- zero pivot, but the whole column is zero, so no swap is needed
example : Matrix.det (R := ℚ) !![0, 1; 0, 2] = 0 := by
  lu_det

example : Matrix.det (R := ℚ) !![-3, 2/7, 1, 0; 4, -1/2, 0, 6; 1, 1, 1, 1; 0, 5, -2, 3] =
    1083/7 := by
  lu_det

example : Matrix.det (R := ℚ) !![-1/2, 1/3; 1/5, 1/4] = -23/120 := by
  lu_det

-- these need row swaps
example : Matrix.det (R := ℚ) !![0, 1; 1, 0] = -1 := by
  lu_det

example : Matrix.det (R := ℚ) !![0, 0, 1; 0, 2, 3; 4, 5, 6] = -8 := by
  lu_det

example : Matrix.det (R := ℚ) !![0, 1, 2; 1, 0, 3; 0, 0, 5] = -5 := by
  lu_det

/--
error: lu_det: the determinant is -2, but the goal claims 3
-/
#guard_msgs in
example : Matrix.det (R := ℚ) !![1, 2; 3, 4] = 3 := by
  lu_det
