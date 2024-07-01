import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div
import Theorem.Lemma.f_choose_mul_eq_mul_sub_div

open Nat
open Finset
open BigOperators

theorem choose_mul_eq_mul_sub_div_2 {n k: ℕ} : (((1/(k+2)) : ℝ) * choose (n+1) (k+1)) = (1/(n+2)) * choose (n+2) (k+2) := by
  have h1: 1 / (↑(k + 1) + 1) * ↑(Nat.choose (n + 1) (k + 1)) =  (((1/(k+2)) : ℝ) * choose (n+1) (k+1)) :=by
    simp
    left
    rw [add_assoc]
    simp
    ring
  rw [←h1]
  rw [f_choose_mul_eq_mul_sub_div (n+1) (k+1)]
  simp
  left
  rw [add_assoc]
  simp
  ring
