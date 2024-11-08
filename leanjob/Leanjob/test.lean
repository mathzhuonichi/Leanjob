import Mathlib
open Nat

example ( n : Nat) (a r: ℝ ) (h: r≠ 1):(∑ j in Finset.range (n+1) , a*(r^j))=(a*r^(n+1)-a)/(r-1):= by
  --Translate the condition to r-1≠ 0 for later use.
  rw[← sub_ne_zero] at h
  --We use induction on n
  induction' n with n ih
  --Evaluate the base case, we use simp to simplify the statement to an identity without summation and use simp only to make the code stable.
  ·simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one]
  --We prove this in the ring ℝ.
   rw [eq_div_iff_mul_eq]
   ring_nf
   exact h
  --Decompose the summation into two parts, one part we use our induction hypothesis and then prove the conclusion by calculation.
  ·rw[Finset.sum_range_succ,ih]
   --We prove by calculation, again we annihilate the denominator
   rw [eq_div_iff_mul_eq,add_mul,div_mul,div_self,div_one]
   ring_nf
   exact h
   exact h

example (n : Nat ) (k : Nat ) (h : k≤ n):(Nat.choose n k= Nat.choose n (n-k)) ∧ (Nat.choose n 0=1)∧ (Nat.choose n n=1):=by
  --Use choose_symm from Mathlib.Nat
  rw[Nat.choose_symm h,Nat.choose_zero_right,Nat.choose_self]
  simp only [and_self]
  --An alternative solution by unfolding and do a calculation.
  -- simp[Nat.choose]
  -- rw[Nat.choose_eq_factorial_div_factorial,Nat.choose_eq_factorial_div_factorial,mul_comm,Nat.sub_sub_self h]
  -- exact Nat.sub_le n k
  -- exact h

example (n: Nat) (hn: 0< n) (f : Nat -> Int) (h₁: f 1= 1) (h₂: f 2= 5) (h: ∀ k>0 , f (k+2)=f (k+1) +2 * f k):f n =2^n + (- 1)^n:=by
  induction' n using Nat.twoStepInduction with m ih1 ih2
  ·trivial
  ·ring_nf
   exact h₁
  by_cases h2:m=0
  · rw [h2,zero_add,h₂]
    norm_num
  · rw[h,ih1,ih2]
    ring_nf
    linarith
    apply Nat.ne_zero_iff_zero_lt.1 h2
    apply Nat.ne_zero_iff_zero_lt.1 h2
