import Mathlib.Data.Nat.Choose.Sum
import Theorem.example_separate.choose_mul_eq_mul_sub_div
import Theorem.IDT_1to100.IDT_11to20.idt_12
import Theorem.IDT_1to100.IDT_1to10.idt_6
import Theorem.Lemma.two_eq_one_add_one
import Theorem.Lemma.three_eq_two_add_one

open Nat
open Finset
open BigOperators


-- theorem lemma_1 {k : ℕ}: (-1:ℝ) ^ k = (-1:ℝ) ^ (k + 2 -2) := by
--     congr

theorem lemma_2 {n : ℕ} : ∑ k in Ico 0 (n+1) , (-1:ℝ) ^ (k +2) * choose (n+2) (k+2) = n+1 :=by
    let f: ℕ → ℝ := fun k =>  (-1:ℝ) ^ k * choose (n+2) k
    rw [sum_Ico_add' f]
    ring_nf
    rw [add_comm 3 n]

theorem idt_41 { n : ℕ }: ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *  (1/ (k+2)) * (1/ (k+1)) * n.choose (k) = 1 / (n +2 ) :=by
 sorry
  -- have l₁:  ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *  (1/ (k+2)) * (1/ (k+1)) * n.choose (k) =
  --    ∑ k in Ico 0 (n+1),  (-1:ℝ)^k * (1/ (n+1)) * (1/ (k+2)) * (n+1).choose (k+1) := by
  --     refine' sum_congr rfl fun k _ => _
  --     rw [mul_assoc,choose_mul_eq_mul_sub_div,← mul_assoc]
  --     congr 1
  --     ring
  -- rw [l₁]

  -- have h₁: ∑ x in Ico 0 (n + 3), f x =  f 0 + f 1 + ∑ x in Ico 2 (n + 3), f x :=by
  --   rw [sum_eq_sum_Ico_succ_bot,sum_eq_sum_Ico_succ_bot]
  --   simp
  --   ring
  --   linarith

  --   have hh : 0 + 3 ≤ n + 3 := Nat.add_le_add_right (Nat.zero_le n) 3
  --   rw [Nat.zero_add] at hh
  --   exact lt_of_lt_of_le (Nat.zero_lt_succ 2) hh
  -- have h_2: f 0 = 1 :=by
  --   ring_nf
  --   rw [choose_zero_right]
  --   ring

  -- have h_3 : f 1 = - (n+2) :=by
  --   ring_nf
  --   rw [choose_one_right]
  --   simp
  --   ring

  -- have h_4: ∑ x in Ico 0 (n + 3), f x  = 0 := by
  --   ring_nf
  --   rw [←range_eq_Ico]
  --   rw [add_comm 2 n,add_comm 3 n]
  --   rw [tree_eq_two_add_one,←add_assoc]

  --   rw [sum_congr rfl fun a ha => by
  --     rw [mul_comm]
  --   ]
  --   have h0: ∑ a in range (n + 2 + 1), (-1:ℝ) ^ a * (Nat.choose (n + 2) a) = ∑ a in range (n + 2 + 1), (-1:ℤ) ^ a * (Nat.choose (n + 2) a) :=by
  --     simp
  --   rw [h0]
  --   have hn2: (n+2) ≠ 0 :=by
  --     simp
  --   rw [Int.alternating_sum_range_choose_of_ne hn2]
  --   simp

  -- rw [h_4,h_2,h_3] at h₁
  -- symm at h₁
  -- rw [add_comm 1] at h₁
  -- ring_nf at h₁
  -- rw [add_comm] at h₁

  -- rw [sub_eq_neg_add,←neg_add,add_neg_eq_iff_eq_add,zero_add,add_comm 3] at h₁
  -- symm at h₁
  -- rw [h₁, sum_congr rfl fun a ha => by
  --   rw [mul_comm]
  -- ]
  -- have l₂: ∑ k in Ico 0 (n+1), (-1:ℝ) ^ k * (1 / (n + 1)) * (1 / (k + 2)) * Nat.choose (n + 1) (k + 1) =
  --   ∑ k in Ico 0 (n+1),  (-1:ℝ)^k *(n+2).choose (k+2) * (1/ (n+1)) * (1/ (n+2)):= by
  --     refine' sum_congr rfl fun k _ => _
  --     rw [mul_assoc,choose_mul_eq_mul_sub_div_2]
  --     ring
  -- rw [l₂]

  -- rw [←sum_mul,←sum_mul]

  -- have l₃: ∑ k in Ico 0 (n+1), (-1:ℝ) ^ k * (Nat.choose (n + 2) (k + 2)) = (n + 1) :=by
  --   rw [sum_congr rfl fun k _ => by
  --     rw [neg_one_pow_add]
  --   ]
  --   exact lemma_2

  -- rw [l₃]
  -- congr
  -- rw [← mul_div_assoc,mul_one,div_eq_iff_mul_eq]
  -- ring
  -- linarith
  -- rw [one_div]
