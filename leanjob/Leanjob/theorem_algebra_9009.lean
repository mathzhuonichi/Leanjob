import Mathlib

/-
The roots of the quadratic equation $x^{2}-49=0$ are ____.-/
theorem algebra_9009 (x : ℝ) (hx : x^2 - 49 = 0) : x = 7 ∨ x = -7 := by
--The anser is x=7 and x=-7.
  nth_rewrite 2[←sub_eq_zero];rw[←sub_eq_zero,sub_neg_eq_add,←mul_eq_zero];ring_nf;rw[add_comm,←sub_eq_add_neg,hx]
