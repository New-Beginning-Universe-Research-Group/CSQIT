import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic

-- Test 1: norm_num on ℚ equality
example : (67.39475 : ℚ) = 269579/4000 := by norm_num

-- Test 2: norm_num on ℝ equality with Rat.cast RHS
example : (67.39475 : ℝ) = ((269579/4000 : ℚ) : ℝ) := by norm_num

-- Test 3: push_cast then norm_num
example : (67.39475 : ℝ) = ((269579/4000 : ℚ) : ℝ) := by
  push_cast
  norm_num

-- Test 4: using Rat.ofScientific
example : (67.39475 : ℚ) = 269579/4000 := by
  rw [show (67.39475 : ℚ) = OfScientific.ofScientific 6739475 true 5 from rfl]
  rw [Rat.ofScientific_true_def]
  norm_num

-- Test 5: 1e-4
example : (1e-4 : ℚ) = 1/10000 := by norm_num

-- Test 6: full hubble_prediction style
example : abs (((102777/1525 : ℚ) : ℝ) - 67.39475) < 1e-4 := by
  norm_num
