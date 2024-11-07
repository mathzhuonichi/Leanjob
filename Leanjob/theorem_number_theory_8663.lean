import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat Int Set ArithmeticFunction

/-A natural number is called *good* if it can be represented as sum of two coprime natural numbers, the first of which decomposes into odd number of primes (not necceserily distinct) and the second to even. Prove that there exist infinity many  $n$  with  $n^4$  being good.-/
/-Solution from AOPS:
I will prove that there exists infinitely many numbers  $n^4$  such that  $n^4=x^2+2y^2$  in which  $x$  is odd and  $y$  is even and  $gcd(x,y)=1$  .
Clearly we have that  $n^4$  is a good number. Reason :  $x^2$  has even prime factors and since  $y^2$  has even prime factors  $\implies$   $2y^2$  has odd prime factors.
The goal is to construct a good number from previous good numbers
Note that we have :  $3^4=7^2+2*4^2$
By lagrange formula we have that  $(a^2+mb^2)(c^2+md^2)=(ac-mbd)^2+m(bc+ad)^2$ By putting  $c=a$  and  $d=b$  and  $m=2$   we get that  $(a^2+2b^2)(a^2+2b^2)=(a^2-2b^2)^2+2(2ab)^2$ Assume that we have   $(a^2+2b^2)=n_1^4$  , and  $n_1^4$  is the largest number we know of the form  $a^4$  and good number .
Therefor by the formula above we can see that  $n_1^8=(a^2-2b^2)+2(2ab)^2 \implies n_1^8$  is a good number , so we have found a bigger number of the form  $a^4$  such that it is a good number . ( Note that  $a^2-2b^2$  and  $2ab$  are coprime)
So we start form  $3^4$  and construct  $9^4$  and  $81^4$   $\dots$   $Q.E.D$ -/
theorem number_theory_8663 : Set.Infinite {n : ℕ | ∃ m k : ℕ, n = m + k ∧ m ≠ k ∧ Nat.Coprime m k ∧ Odd (cardFactors m)∧ Even (cardFactors k) ∧ ∃ j : ℕ, j^4 = n} := by
--The formulation is almost correct but the set primeFactors doesn't compute the multiplicity, we should use primeFactorList or the Ω function instead. Not easy to handle.
-- A subset of natural numbers is infinite iff it's not bounded above.
  apply infinite_of_not_bddAbove
  rw[not_bddAbove_iff]
--Introduce several lemmas
--If x^2 is even, then x is even
  have even_of_even_sq (m : ℕ) (h : 2 ∣ m ^ 2) : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
--If x^2 is divided by p, then so is x
  have prime_dvd_of_dvd_sq (m p : ℕ) (p_prime : Nat.Prime p) (hp:p∣m^2):p∣m:=by
    exact Nat.Prime.dvd_of_dvd_pow p_prime hp
--Ω x^2 is always even
  have even_length_of_prime_factors_square (x : ℕ) : Even (cardFactors (x ^ 2)):= by
    by_cases h:x=0
    rw[h,pow_two,mul_zero]
    apply even_iff_two_dvd.mpr
    simp only[ArithmeticFunction.map_zero, dvd_zero]
    rw[pow_two,Even]
    use Ω x
    exact cardFactors_mul h h
--Ω 2*x^2 is odd as long as x ≠ 0
  have odd_length_of_prime_factors_two_mul_square (y : ℕ) (ynezero:y ≠ 0): Odd (cardFactors (2*y ^ 2)) := by
    rw[cardFactors_mul,cardFactors_eq_one_iff_prime.mpr Nat.prime_two]
    apply Even.one_add (even_length_of_prime_factors_square y)
    norm_num
    norm_num[ynezero]
--We construct a sequence in the good numbers which is not bounded.
  have pow3_Archimedean (N : ℕ): N<3^(2^(2+N)) :=by
    induction' N with k ih
    norm_num
    rw[←add_assoc,pow_add,pow_mul,pow_one]
    by_cases hk:k=0
    rw[hk]
    norm_num
    have auxk:k+1≤ 3 ^ 2 ^ (2 + k):=by
      linarith
    apply lt_of_le_of_lt auxk
    have auxm (m:Nat)(hm:2≤ m):m < m^2:=by
      rw[pow_two]
      nth_rw 1[←one_mul m]
      apply mul_lt_mul
      repeat linarith
    apply auxm
    have final:2≤ k+1 :=by
      simp only [reduceLeDiff]
      apply Nat.add_one_le_of_lt
      apply Nat.zero_lt_of_ne_zero hk
    exact le_trans final auxk
--Introduce the upper bound N, we shall see later we can find good number greater than N.
  intro N
--We first prove that numbers of the form j^4=2*y^2+x^2 are all good.
  have h (n:ℕ):(∃ j : ℕ, j^4 = n ∧ ∃ x y :ℕ, n=2*y^2+x^2 ∧ y ≠ 0 ∧ Odd x∧ Nat.Coprime x y)->(∃ m k : ℕ, n = m + k ∧ m ≠ k ∧ Nat.Coprime m k ∧ Odd (cardFactors m) ∧ Even (cardFactors k) ∧ ∃ j : ℕ, j^4 = n):=by
--Introduce assumptions needed.
    intro ⟨j,hj,x,y,hxy,ynezero,oddx,hxy_coprime⟩
    use 2*y^2,x^2
    constructor
    exact hxy
    constructor
--We prove that they are distinct via parity, this is not needed in the natural language.
    contrapose! oddx
    simp only[Nat.not_odd_iff_even]
    apply even_iff_two_dvd.mpr
    apply even_of_even_sq
    rw[←oddx]
    norm_num
    constructor
--We prove that the m,k we choose are coprime
    rw[Nat.coprime_comm]
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    rw[Nat.pow_two]
    apply Odd.coprime_two_right
    apply Odd.mul oddx oddx
    contrapose! hxy_coprime
    apply Nat.Prime.not_coprime_iff_dvd.mpr
--We use prime to test the common divisor
    rcases Nat.Prime.not_coprime_iff_dvd.mp hxy_coprime with ⟨p,p_prime,hpx,hpy⟩
    use p
    constructor
    exact p_prime
    constructor
    exact prime_dvd_of_dvd_sq x p p_prime hpx
    exact prime_dvd_of_dvd_sq y p p_prime hpy
    constructor
--Use the lemma given above two prove the desired parity.
    apply odd_length_of_prime_factors_two_mul_square y ynezero
    constructor
    apply even_length_of_prime_factors_square x
    exact ⟨j,hj⟩
--We prove that as long as n satisfies our assumption before, then so is n^2
  have h' (n:ℕ):(∃ j : ℕ, j^4 = n ∧ ∃ x y :ℕ, n=2*y^2+x^2 ∧ y ≠ 0 ∧ Odd x∧ Nat.Coprime x y)->(∃ j' : ℕ, j'^4 = n^2 ∧ ∃ x' y' :ℕ, n^2=2*y'^2+x'^2 ∧ y' ≠ 0 ∧ Odd x'∧ Nat.Coprime x' y'):=by
    rintro ⟨j,hj,x,y,hxy,ynezero,oddx,hxy_coprime⟩
    have hodd:Odd ((x^2-2*y^2):ℤ).natAbs :=by
      rw[Int.natAbs_odd]
      apply Int.odd_sub.mpr
      constructor
      norm_num
      intro _
      rw[pow_two,Int.odd_mul,Int.odd_coe_nat]
      exact ⟨oddx,oddx⟩
    use j^2
    rw[hxy]
    constructor
    rw[pow_right_comm,hj,hxy]
    use ((x:ℤ)^2-2*(y:ℤ)^2: ℤ ).natAbs,2*x*y
    constructor
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, natCast_natAbs, sq_abs]
    ring
--We check the unpleasant conditions one by one.
    constructor
    apply mul_ne_zero
    apply mul_ne_zero
    linarith
    contrapose! oddx
    rw[oddx]
    norm_num
    exact ynezero
    constructor
    have hodd:Odd ((x^2-2*y^2):ℤ).natAbs :=by
      rw[Int.natAbs_odd]
      apply Int.odd_sub.mpr
      constructor
      norm_num
      intro _
      rw[pow_two,Int.odd_mul,Int.odd_coe_nat]
      exact ⟨oddx,oddx⟩
    exact hodd
    apply coprime_mul_iff_right.mpr
    constructor
    apply coprime_mul_iff_right.mpr
    constructor
    apply Nat.coprime_two_right.mpr hodd
    contrapose! hxy_coprime
    rcases Nat.Prime.not_coprime_iff_dvd.mp hxy_coprime with ⟨p,p_prime,hpx,hpy⟩
    apply Nat.Prime.not_coprime_iff_dvd.mpr
    use p
    constructor
    exact p_prime
    constructor
    exact hpy
    apply prime_dvd_of_dvd_sq
    have pdvd:p∣2*y^2:=by
      rw[←Int.ofNat_dvd] at hpx
      simp only [natCast_natAbs, dvd_abs] at hpx
      apply Int.dvd_iff_dvd_of_dvd_sub at hpx
      rw[←Int.ofNat_dvd]
      apply hpx.mp
      rw[pow_two,←Int.ofNat_mul,Int.ofNat_dvd]
      apply Nat.dvd_trans hpy
      norm_num
    by_cases hp:p=2
    rw[hp] at hpy
    by_contra! _
    apply Nat.not_even_iff_odd.mpr at oddx
    apply even_iff_two_dvd.mpr at hpy
    exact oddx hpy
    apply Nat.Coprime.dvd_of_dvd_mul_left _ pdvd
    simp only [coprime_two_right]
    apply Nat.Prime.odd_of_ne_two
    exact p_prime
    exact hp
    exact p_prime
    contrapose! hxy_coprime
    rcases Nat.Prime.not_coprime_iff_dvd.mp hxy_coprime with ⟨p,p_prime,hpx,hpy⟩
    apply Nat.Prime.not_coprime_iff_dvd.mpr
    use p
    constructor
    exact p_prime
    constructor
    have pdvd:p∣x^2:=by
      rw[←Int.ofNat_dvd] at hpx
      simp only [natCast_natAbs, dvd_abs] at hpx
      apply Int.dvd_iff_dvd_of_dvd_sub at hpx
      rw[←Int.ofNat_dvd]
      apply hpx.mpr
      rw[pow_two,← Int.ofNat_mul]
      apply Int.ofNat_dvd.mpr
      apply Nat.dvd_trans hpy
      rw[←mul_assoc]
      norm_num[hpy]
    apply prime_dvd_of_dvd_sq
    exact pdvd
    exact p_prime
    exact hpy
--We construct our n explicitly so it is relatively easy for us to show that it is unbounded.
  have h'' (n:ℕ):(∃ j : ℕ, j^4 = 3^(2^(2+n)) ∧ ∃ x y :ℕ, 3^(2^(2+n))=2*y^2+x^2 ∧ y ≠ 0 ∧ Odd x∧ Nat.Coprime x y):=by
    induction' n with k hk
    use 3
    norm_num
    use 7,4
    constructor
    norm_num
    norm_num
    apply odd_iff_exists_bit1.mpr
    use 3
    rfl
    use 3^(2^(k+1))
    constructor
    rw[←pow_mul']
    have :(4 * 2 ^ (k + 1)) = 2 ^ (2 + (k + 1)):=by
      nth_rw 2[pow_add]
      rfl
    rw[this]
    rcases (h' (3 ^ 2 ^ (2 + k)) hk) with ⟨j',_,h'''⟩
    have aux:(3 ^ 2 ^ (2 + k)) ^ 2 = 3 ^ 2 ^ (2 + (k + 1)):= by
      rw[←pow_mul]
      rw[pow_add,pow_add,pow_add]
      norm_num
      rw[mul_assoc]
    rw[aux] at h'''
    apply h'''
  have n_exists_above : ∃ n, N< n ∧  ∃ m k : ℕ, n = m + k ∧ m ≠ k ∧ Nat.Coprime m k ∧ Odd (cardFactors m) ∧ Even (cardFactors k) ∧ ∃ j : ℕ, j^4 = n:=  by
    use 3^(2^(2+N))
    constructor
    apply pow3_Archimedean
    apply h
    apply h''
  obtain ⟨n,h₁,h₂⟩ := n_exists_above
  simp only [mem_setOf_eq]
  use n
