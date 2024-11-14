import Mathlib
import Aesop



open BigOperators Real Nat Topology Rat

/-Find all prime numbers such that the square of the prime number can be written as the sum of cubes of two positive integers.-/
theorem number_theory_8605 :{p : ℕ | p.Prime ∧ ∃ x y : ℕ, 0<x ∧ 0<y ∧  x^3 + y^3 = p^2} = {3} := by
--We introduce AM-GM inequality
  have am_gm (x y:ℕ):2*x*y≤x^2+y^2:=by
          rw[←Int.ofNat_le]
          simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
          rw[←Int.sub_nonneg,←sub_add_eq_add_sub,←sub_sq]
          apply sq_nonneg
  have mul_le_sq_sum (x y:ℕ):x*y≤x^2+y^2:=by
    apply le_trans' (am_gm _ _)
    nth_rewrite 1[←one_mul (x*y),mul_assoc]
    apply mul_le_mul
    repeat' norm_num
  have aux1 (x y:ℕ):↑((x ^ 2 + y ^ 2 - x * y))=((x:ℤ) ^ 2 + y ^ 2 - x * y):=by
    rw[Int.natCast_sub]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul]
    apply mul_le_sq_sum
  ext p;
  simp_all only [exists_and_left, Set.mem_setOf_eq, Set.mem_singleton_iff]
  apply Iff.intro
  · intro h
    obtain ⟨p_prime, right⟩ := h
    obtain ⟨x, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    obtain ⟨y, h⟩ := right
    obtain ⟨ypos, h⟩ := h
--We decompose the sum of cubes.
    replace h:(x+y)*(x^2+y^2-x*y)=p^2:=by
      rw[←h,←Int.natCast_inj]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
      rw[aux1]
      ring
    have dvdpsq:(x+y)∣p^2:=by
      use (x^2+y^2-x*y);rw[h]
    rcases (Nat.dvd_prime_pow p_prime).mp dvdpsq with ⟨i,hi,hxy⟩
--We know that x+y is a power of p, we check our conclusion case by case.
    interval_cases i
--i=0 case by exfalso
    linarith
--i=1 case
    rw[pow_one] at hxy;rw[hxy,pow_two p] at h;field_simp at h;
    rcases h with h|h
    rw[←Int.ofNat_inj,aux1] at h;
    have yltp:y<p:=by linarith
    have xltp:x<p:=by linarith
    replace hxy:x=p-y:=by rw[←hxy,Nat.add_sub_cancel]
    rw[hxy] at h;ring_nf at h
    have psuby:↑(p - y)=(p:ℤ)-y:=by apply Int.natCast_sub;linarith
    rw[psuby] at h
    ring_nf at h
    replace h: (y:ℤ) ^ 2 * 3 = ↑p*( ↑y * 3+1-↑ p):=by
      rw[←sub_eq_zero];ring_nf
      rw[←sub_eq_zero] at h;ring_nf at h;rw[←h];ring_nf
--We deduce that p∣3 by p.Coprime y^2
    have :p∣ y^2*3:=by
      rw[←Int.natCast_dvd_natCast]
      use (↑y * 3 + 1 - ↑p)
      rw[←h];simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have pcoprimey:Coprime p (y^2):=by
      apply @Nat.Coprime.pow_right p y 2
      apply Nat.coprime_of_lt_prime ypos yltp p_prime
    apply Nat.Coprime.dvd_of_dvd_mul_left pcoprimey at this
--We get p=3 by p∣3
    rw[←Nat.prime_dvd_prime_iff_eq];exact this;exact p_prime;norm_num;linarith
--i=2 case by exfalso
    rw[hxy,←mul_one (p^2),mul_assoc] at h;
    apply Nat.mul_left_cancel at h
    simp at h
    have xyeqone:x*y=1:=by
      apply eq_of_le_of_le
      rw[←h]
      apply Nat.le_sub_of_add_le
      ring_nf;rw[mul_comm,←mul_assoc];apply am_gm
      apply one_le_mul;linarith;linarith
    have x_y_eq_one:x=1∧y=1:=by
      constructor
      apply Nat.eq_one_of_mul_eq_one_right xyeqone
      apply Nat.eq_one_of_mul_eq_one_left xyeqone
    rcases x_y_eq_one with ⟨hx,hy⟩
    rw[hx,hy] at hxy dvdpsq
    simp only [reduceAdd] at dvdpsq
    apply Nat.Prime.dvd_of_dvd_pow at dvdpsq
    rw[Nat.prime_dvd_prime_iff_eq] at dvdpsq
    simp only [reduceAdd] at hxy
    rw[←dvdpsq] at hxy
    contradiction
    exact Nat.prime_two;exact p_prime;exact Nat.prime_two;linarith
  · intro h
    simp_all only [reducePow]
    apply And.intro
    · decide
    · use 2
      simp_all
      use 1
      simp_all
