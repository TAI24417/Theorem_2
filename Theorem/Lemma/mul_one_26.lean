import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity

open Nat



theorem mul_one_26(a:ℤ): a * 1 * 1 = a := by
  have a1:a * 1 = a:=by
    exact mul_one a
  rw[a1]
  rw[a1]
