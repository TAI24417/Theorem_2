import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div
import Theorem.Lemma.f_choose_mul_eq_mul_sub_div
import Theorem.IDT_1to100.IDT_1to10.idt_6

open Nat
open Finset
open BigOperators


theorem binom_identity_n_1 {n k : ℕ} (hkn: k<=n) : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k :=by
  let t:= k+1
  have h1: t= k+1 :=by
    simp
  simp [←h1]
  have h2: k = t-1 := by
    simp [tsub_add_tsub_comm]
  rw [h2]
  let m:= n+1
  have h3: m= n+1:=by
    simp
  rw [←h3]
  have h4: n = m-1 :=by
    simp [tsub_add_tsub_comm]
  rw [h4]
  have h_tm: t<=m :=by
    simp
    exact hkn
  have h_sk: 1≤ t :=by
    simp
  exact (idt6_Absorption h_tm h_sk)
