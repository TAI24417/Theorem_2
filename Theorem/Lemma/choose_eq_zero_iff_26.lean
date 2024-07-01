import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity

open Nat


theorem choose_eq_zero_iff_26(k n : ℕ) (h1: n < k): choose n k = 0 := by
  exact choose_eq_zero_iff.mpr h1
