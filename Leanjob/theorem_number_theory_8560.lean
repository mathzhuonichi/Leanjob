import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- $a,b,c$  are positive integer.
Solve the equation: $ 2^{a!}+2^{b!}=c^3 $ -/

theorem number_theory_8560 (a b c : ℕ)(h₀ : 0 < a)(h₁ : 0 < b)(h₂ : 0 < c)(h₃ : 2^(a !) + 2^(b !) = c ^ 3) :(a, b, c) = (2, 2, 2) := by
--We consider the remainder of power three of natural numbers
  have pow_three_mod9 (x:ℕ):x^3 % 9 =0 ∨ x^3 % 9 =1 ∨ x^3 % 9 =8:=by
    let r:=x%3;have r_def:r=x%3:=rfl
    have hr:x=r+x/3*3:=by rw[r_def,Nat.mod_add_div']
    have this':((1 + x / 3 * 9 + (x / 3) ^ 2 * 27 + (x / 3) ^ 3 * 27)=1 + (x / 3  + ((x / 3) ^ 2 * 3) + ((x / 3) ^ 3 * 3))*9)∧ ((8 + x / 3 * 36 + (x / 3) ^ 2 * 54 + (x / 3) ^ 3 * 27)=8+(x/3*4+(x/3)^2*6+(x/3)^3*3)*9):=by constructor;ring_nf;ring_nf
    mod_cases h:x%3
    · rw[Nat.ModEq,←r_def,zero_mod] at h
      rw[h,zero_add] at hr
      apply Or.inl
      rw[hr,mul_comm,mul_pow,pow_three,mul_assoc,mul_comm,mul_assoc]
      simp only[reduceMul,mul_mod_right]
    · rw[Nat.ModEq,←r_def] at h
      rw[h] at hr;simp at hr
      apply Or.inr
      apply Or.inl
      rw[hr];ring_nf;rw[this'.1];simp
    · rw[Nat.ModEq,←r_def] at h
      rw[h] at hr;simp at hr
      apply Or.inr
      apply Or.inr
      rw[hr];ring_nf;rw[this'.2];simp
  have cpow3:c ^ 3 % 9 = 0 ∨ c ^ 3 % 9 = 1 ∨ c ^ 3 % 9 = 8:=by apply pow_three_mod9
--We use this lemma to show that if a is greater than 2 then the remainder of 2 ^ a ! by 9 must be 1 (and the same holds for b).
  have gttwo (x:ℕ) (hx:2<x):2^(x !)%9=1:=by
    induction x,hx using Nat.le_induction
    · simp only [succ_eq_add_one, reduceAdd,factorial,reduceMul];norm_num;
    · rename_i hr;rw[factorial,succ_eq_add_one,pow_mul',pow_mod,hr];simp
  have modh₃:(2 ^ a ! + 2 ^ b !)%9=c^3%9:=by rw[h₃]
  rw[Nat.add_mod] at modh₃
--We reduce the problem to a finite case discussion. First for a.
  have alt3:a≤2:=by
    by_contra! ha
    · apply gttwo at ha
      · by_cases hb:2<b;apply gttwo at hb
        rw[ha,hb] at modh₃;simp at modh₃
        rw[←modh₃] at cpow3;contradiction
        · simp at hb
          by_cases beq2:b=2
          rw[beq2,ha] at modh₃;simp at modh₃;rw[←modh₃] at cpow3;contradiction
          have beq1:b=1:=by
            interval_cases b;rfl;exfalso;apply beq2;rfl
          rw[beq1,ha] at modh₃;simp at modh₃
          rw[←modh₃] at cpow3;contradiction
--We reduce the problem to a finite case discussion. Do the same for b.
  have blt3:b≤2:=by
    by_contra! hb
    · apply gttwo at hb
      · by_cases ha:2<a
        apply gttwo at ha;rw[hb,ha] at modh₃
        simp at modh₃;rw[←modh₃] at cpow3;contradiction
        · simp at hb;by_cases aeq2:a=2
          rw[aeq2,hb] at modh₃;simp at modh₃
          rw[←modh₃] at cpow3;contradiction
          have aeq1:a=1:=by
            interval_cases a;rfl;exfalso;apply aeq2;rfl
          rw[aeq1,hb] at modh₃;simp at modh₃
          rw[←modh₃] at cpow3;contradiction
--Check the fact case by case.
  interval_cases a
  interval_cases b
  repeat' simp at modh₃;rw[←modh₃] at cpow3;contradiction;
  interval_cases b
  repeat' simp at modh₃;rw[←modh₃] at cpow3;contradiction;
  simp at h₃;simp;
  have h₃:c^3=2^3:=by rw[←h₃];simp
  rcases Nat.eq_iff_le_and_ge.mp h₃ with ⟨H1,H2⟩
  apply Nat.eq_iff_le_and_ge.mpr
  constructor
  · apply (Nat.pow_le_pow_iff_left _).mp;apply H1;simp
  · apply (Nat.pow_le_pow_iff_left _).mp;apply H2;simp
