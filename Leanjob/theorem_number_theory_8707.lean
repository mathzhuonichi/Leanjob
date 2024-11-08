import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat Ring

-- For all positive integers  $n$ , find the remainder of  $\dfrac{(7n)!}{7^n \cdot n !}$  upon division by 7.

theorem number_theory_8707 : (Odd n -> (7 * n)! / (7^n * n !)≡6 [MOD 7] )∧ (Even n ->((7 * n)! / (7^n * n !))≡1 [MOD 7]):= by
--This lemma should be set into mathlib4
  have nat_mul_tdiv_assoc (a b c:ℕ) (hc:c∣a): a*b/c=a/c*b :=by
    apply Int.natCast_inj.mp
    simp only [Int.ofNat_ediv, Nat.cast_mul]
    apply Int.natCast_dvd_natCast.mpr at hc
    apply Int.mul_tdiv_assoc' b hc
--Simplification for the term to be appeared.
  have aux1 (m:ℕ): ((7 * m + 6 + 1) * (7 * m + 5 + 1) * (7 * m + 4 + 1) * (7 * m + 3 + 1) * (7 * m + 2 + 1) * (7 * m + 1 + 1) * (7 * m + 1))=((7*m+1)*(7*m+2)*(7*m+3)*(7*m+4)*(7*m+5)*(7*m+6))*(7*m+7):=by ring
  have aux2 (m:ℕ):(7 ^ m * 7 ^ 1 * ((m + 1) * m !))=(7 ^ m * m !)*(7*m+7):=by ring
--Expand (7*(m+1)) !
  have aux3 (m:ℕ):((7*(m+1)) !) =((7*m) !)*((7*m+1)*(7*m+2)*(7*m+3)*(7*m+4)*(7*m+5)*(7*m+6))*(7*m+7):=by
    rw[mul_add,mul_one,factorial_succ,mul_comm,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,aux1,← mul_assoc]
--Expand (7 ^ (m + 1)) * ((m + 1)!)
  have aux4 (m:ℕ):(7 ^ (m + 1)) * ((m + 1)!)=7^m *(m !)*(7*m+7):=by
    rw[pow_add,pow_one,mul_assoc,factorial_succ];ring
--Simplify the terms with 7
  have facmod7 (m n :ℕ):7*m+n≡n [MOD 7]:=by
    apply Nat.modEq_iff_dvd.mpr
    simp only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, sub_add_cancel_right, dvd_neg,
      dvd_mul_right]
--Simple eval.
  have fac1:(1*2*3*4*5*6)≡6[MOD 7] ∧ 6*6≡1[MOD7]:=by
    constructor
    rfl;rfl
--We use the fact that all considered fraction is indeed an integer to get the expansion.
  have dvdfac(m:ℕ):(7^m) * (m !) ∣ (7*m)!:=by
    induction' m with m hm
    · simp only [pow_zero, factorial_zero, mul_one, mul_zero, dvd_refl]
    rw[aux3,aux4]
    apply mul_dvd_mul;apply dvd_trans hm;apply dvd_mul_right;apply dvd_rfl
--The key fact using in the induction.
  have fsucc (m:ℕ):(7 * (m + 1))! / (7 ^ (m + 1) * (m + 1)!)=((7 * m)! / (7^m * m !))*((7*m+1)*(7*m+2)*(7*m+3)*(7*m+4)*(7*m+5)*(7*m+6)):=by
    rw[mul_add,mul_one,factorial_succ,mul_comm,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,mul_assoc,mul_comm,mul_assoc,factorial_succ,pow_add]
    rw[aux1,aux2]
    have :0<7*m+7:=by linarith
    rw[←mul_assoc,Nat.mul_div_mul_right _ _ this]
    apply nat_mul_tdiv_assoc;apply dvdfac
  induction' n with n hn
  simp only [not_odd_zero, mul_zero, factorial_zero, pow_zero, mul_one, zero_lt_one, Nat.div_self,
    false_implies, even_zero, true_implies, true_and];rfl
  rw[fsucc]
  constructor
  intro oddcase
  rw [← not_even_iff_odd,Nat.even_add_one, not_even_iff_odd,not_odd_iff_even] at oddcase
  nth_rw 2[←one_mul 6]
  apply Nat.ModEq.mul
  apply hn.2 oddcase
  simp only [one_mul,ModEq]
  rw[←fac1.1]
  repeat' apply Nat.ModEq.mul
  repeat' apply facmod7
  intro evencase
  rw[Nat.even_add_one,not_even_iff_odd] at evencase
  simp only [ModEq]
  rw[←fac1.2]
  apply Nat.ModEq.mul
  apply hn.1 evencase
  simp only [one_mul,ModEq]
  rw[←fac1.1]
  repeat' apply Nat.ModEq.mul
  repeat' apply facmod7
