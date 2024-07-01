import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div


open Nat
open Finset
open BigOperators


theorem Rat.alternating_sum_range_choose {n : ℕ} :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℝ)) = if n = 0 then 1 else 0 := by
  cases n; · simp
  case succ n =>
    have h := add_pow (-1 : ℝ) 1 n.succ
    simp only [one_pow, mul_one, add_left_neg] at h
    rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]


theorem Rat.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℝ)) = 0 := by
  rw [Rat.alternating_sum_range_choose, if_neg h0]
