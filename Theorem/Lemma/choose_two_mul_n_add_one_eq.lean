import Mathlib.Data.Nat.Choose.Sum
import Theorem.IDT_1to100.IDT_1to10.idt_8


open Nat
open Finset
open BigOperators


theorem choose_two_mul_n_add_one_eq {n:ℕ}: Nat.choose (2 + n * 2) (1 + n)  = Nat.choose (1 + n * 2) (1 + n) * 2 :=by
  have hkn : 1 +n ≤ 2 + n * 2:=by
    rw [← one_add_one_eq_two,add_assoc]
    simp
    linarith
  have hk: 1≤ 1+n:=by
    simp
  have h1 : (2 + n * 2 -  (1 + n)) * choose (2 + n * 2) (1 + n) = (2 + n * 2) * choose (2 + n * 2 -1) (1 + n) :=by
    rw [idt8 hkn hk]
  simp at h1
  have h2: 2 + n * 2 - (1 + n) = 1+n :=by
    nth_rw 1 [←mul_one 2]
    rw [mul_comm n 2]
    rw [←mul_add]
    rw [two_mul]
    rw [Nat.add_sub_cancel]
  rw [h2] at h1
  have h3: (2 + n * 2) = (1+n) * 2 :=by
    nth_rw 1 [←mul_one 2]
    rw [mul_comm n 2]
    rw [←mul_add]
    rw [mul_comm]
  nth_rw 2 [h3] at h1
  have h4:  1+n ≠ 0 :=by
    simp
  rw [←mul_right_inj' h4]
  rw [h1]
  ring
