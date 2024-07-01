import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div
import Theorem.Lemma.f_choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators


theorem neg_one_pow_add {k:ℕ}: (-1:ℝ) ^ k = (-1:ℝ) ^ (k+2):= by
  rw [pow_add]
  rw [neg_one_pow_two]
  ring
