import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
/- The sequences of natural numbers  $p_n$  and  $q_n$  are given such that  $$ p_1 = 1,\ q_1 = 1,\ p_{n + 1} = 2q_n^2-p_n^2,\  q_{n + 1} = 2q_n^2+p_n^2  $$  Prove that  $p_n$  and  $q_m$  are coprime for any m and n.-/

theorem euc_induction {P : Nat → Nat → Prop} (m n : Nat)
  (H0 : ∀ d, P d 0)
  (H1 : ∀ d, P 0 d)
  (H2 : ∀ m n, m ≤ n → P m (n - m - 1) → P m n)
  (H3 : ∀ m n, n ≤ m → P (m - n - 1) n → P m n) :
  P m n :=by
    let l:=m+n ;have l_def: l=m+n:=rfl
--We prove this by induction on the sum of m and n.
    have indl :∀l:ℕ,( ∀m n:ℕ, m+n=l -> P m n):=by
      intro l
      induction' l using Nat.strong_induction_on with k IH
      intro m' n' hmn
      by_cases mzero:m'=0
      · rw[mzero];apply H1
      by_cases nzero:n'=0
      · rw[nzero];apply H0
      · replace mzero:0<m':=pos_iff_ne_zero.mpr mzero
        replace nzero:0<n':=pos_iff_ne_zero.mpr nzero
        by_cases mlen:m'≤n'
        · apply H2 m' n'
          apply mlen
          have nltl:n'<k:=by
            rw[←hmn];linarith
          have _:n'=m'+(n'-m'):=by norm_num[mlen]
          by_cases meqn:m'=n'
          rw[meqn]
          simp only [le_refl, tsub_eq_zero_of_le, _root_.zero_le]
          apply H0
          replace meqn:n'-1=n'-m'-1+m':=by
            rw[←Nat.sub_right_comm,Nat.sub_add_cancel]
            apply Nat.le_pred_of_lt
            simp only [sub_eq, tsub_zero]
            apply Nat.lt_of_le_of_ne mlen meqn
          apply IH (n'-1)
          apply Nat.lt_trans _ nltl
          norm_num[nzero]
          rw[add_comm,meqn]
        · replace mlen:n'≤m':=by linarith
          apply H3 m' n' mlen
          by_cases  meqn:n'=m';rw[meqn]
          simp only [le_refl, tsub_eq_zero_of_le, _root_.zero_le]
          apply H1
          replace meqn:m'-1=m'-n'-1+n':=by
            rw[←Nat.sub_right_comm,Nat.sub_add_cancel]
            apply Nat.le_pred_of_lt
            simp only [sub_eq, tsub_zero]
            apply Nat.lt_of_le_of_ne mlen meqn
          have nltl:m'<k:=by
            rw[←hmn];linarith
          apply IH (m'-1);apply Nat.lt_trans _ nltl;
          simp only [tsub_lt_self_iff, zero_lt_one, and_true,mzero]
          subst hmn
          simp_all only [_root_.zero_le, l]
    apply indl
    exact l_def

--This nested induction in the answer is not contained in mathlib. It is similar to gcd.induction

theorem number_theory_8651 (p q : ℕ → ℤ) (h₀ : p 0 = 1) (h₁ : q 0 = 1) (h₂ : ∀ n, p (n + 1) = 2 * (q n)^2 - (p n)^2) (h₃ : ∀ n, q (n + 1) = 2 * (q n)^2 + (p n)^2) :
  ∀ m n, IsCoprime (p m) (q n) := by
  have id1 (x y:ℤ):(2 * (y) ^2 + (x) ^2)=2 * (x)^2 + 1*(2 * (y )^2 - (x)^2)∧ (x)^2 - 2 * (y )^2= 1* (x)^2 + 2*(-(y)^2):=by ring_nf;simp only[and_self]
  have fac1:p 1=1∧ q 1=3:=by
    rw[←zero_add 1,h₂,h₃,h₀,h₁]
    simp only [one_pow, mul_one, Int.reduceSub, Int.reduceAdd, and_self]
--Formation is almost correct except that as p and q have type ℕ → ℤ, we should use IsCoprime instead of Nat.Coprime.
  have coprime_mod_equiv (a b c : ℤ) (h:a % b = c % b):
  IsCoprime a b → IsCoprime c b :=by
    intro hab
    have :c=a % b+b*(c / b):=by rw[h,Int.emod_add_ediv]
    rw[this]
    apply IsCoprime.add_mul_left_left_iff.mpr
    rw[Int.emod_def,sub_eq_add_neg,neg_mul_eq_mul_neg]
    apply IsCoprime.add_mul_left_left hab
--All p and q are odd
  have oddpq (n : ℕ) : Odd (p n)∧ Odd (q n):= by
    induction' n with k hk
    · simp only [h₀, odd_one, h₁, and_self]
    rcases hk with ⟨hp,_⟩
    constructor
    rw[h₂ k]
    apply Even.sub_odd
    ·simp only [even_two, Even.mul_right]
    ·exact Odd.pow hp
    rw[h₃ k]
    apply Even.add_odd
    ·simp only [even_two, Even.mul_right]
    ·exact Odd.pow hp
--We state the modified claims (as our sequence starting from zero).
--sec_term
  have sec_term_1 (x y :ℤ):2*(2*x^2+y^2)^2-(2*x^2-y^2)^2=4*x*x^3+12*x*x*y*y+y*y^3:=by ring
  have sec_term_2 (x y :ℤ):2*(2*x^2+y^2)^2+(2*x^2-y^2)^2=12*x*x^3+4*x*x*y*y+3*y*y^3:=by ring
  have pow4(x:ℤ): x^4=x*x^3:=by ring
  have pos_sub_add_one (x:ℕ) (h:1≤ x):x=(x-1)+1:=by
    rw[Nat.sub_one_add_one];linarith
--Claim 1: $p_{m+i} \equiv p_{i-1}p_m^{2^i} \pmod{q_m}$ for i>1 and -p_m^2 for i=1
--Claim 2:$q_{m+i} \equiv q_{i-1}p_m^{2^i} \pmod{q_m}$  for all i
  have claim1 (m:ℕ) (i :ℕ) (hi:1 ≤ i): (p (m+i)% (q m)= if i= 1 then -(p m)^2% (q m) else (p (i-1))*(p m)^(2^i) % (q m)) ∧ q (m+i)% (q m)= (q (i-1))*(p m)^(2^i) % (q m):=by
    induction' i with k hk
    contradiction
    constructor
    · split
      rename_i aux
      simp only [add_left_eq_self] at aux
      rw[aux,←add_assoc,h₂,sub_eq_add_neg,add_zero,pow_two,←mul_assoc,mul_comm,add_comm,Int.add_mul_emod_self_left]
      rename_i aux
      replace aux:1≤k :=by
        rw[add_left_eq_self] at aux
        apply pos_iff_ne_zero.mpr at aux
        linarith
      rw[←add_assoc,h₂]
      simp only [add_tsub_cancel_right]
      rcases hk aux with ⟨pa,qa⟩
      split at pa
      rename_i deg
      rw[deg];rw[deg] at pa qa
      simp only [reduceAdd, reducePow]
      rw[fac1.1,one_mul,h₂,h₃,sec_term_1]
      apply Int.ModEq.eq
      apply Int.modEq_iff_dvd.mpr
      rw[←sub_sub,sub_right_comm]
      apply Int.dvd_sub
      ring_nf;simp only [dvd_zero];nth_rw 2[mul_comm];nth_rw 5[mul_comm]
      apply Int.dvd_add
      rw[mul_assoc];apply Int.dvd_mul_right
      rw[mul_assoc,mul_assoc];apply Int.dvd_mul_right
      rename_i hi
      apply Int.ModEq.eq at pa
      apply Int.ModEq.eq at qa
      apply Int.ModEq.eq
      calc 2 * q (m + k) ^ 2 - p (m + k) ^ 2 ≡ q (m+k) * q (m+k)* 2-p (m + k) * p (m+k)[ZMOD q m]:=by
            rw[mul_comm,pow_two,pow_two]
        _≡ (q (k - 1) * p m ^ 2 ^ k)*(q (k - 1) * p m ^ 2 ^ k)*2-(p (k - 1) * p m ^ 2 ^ k)*(p (k - 1) * p m ^ 2 ^ k)[ZMOD q m]:=by
          apply Int.ModEq.sub
          apply Int.ModEq.mul
          apply Int.ModEq.mul qa
          apply qa
          rfl
          apply Int.ModEq.mul
          repeat' apply pa
        _≡ (2 * q (k - 1) ^ 2-p (k-1)^2) * p m ^ 2 ^ k * p m ^ 2 ^ k [ZMOD q m]:=by
          ring_nf
          simp only [Int.ModEq.refl]
        _≡ p k * p m ^ 2 ^ (k + 1)[ZMOD q m]:=by
          rw[←h₂]
          norm_num[aux]
          rw[mul_assoc,← pow_two,←pow_mul,Nat.pow_add_one]
    · norm_num
      rw[←add_assoc,h₃]
      by_cases h:k<1
      · norm_num at h;rw[h,add_zero,h₁,one_mul,zero_add,pow_one,pow_two,←mul_assoc,mul_comm,add_comm]
        simp only [Int.add_mul_emod_self_left]
      rw[not_lt] at h
      rcases hk h with ⟨pa,qa⟩
      split at pa
      rename_i hi
      apply Int.ModEq.eq
      rw[hi,fac1.2,h₃,h₂]
      simp only [reduceAdd, reducePow]
      rw[sec_term_2]
      apply Int.modEq_iff_dvd.mpr
      ring_nf
      apply Int.dvd_neg.mp
      simp only [neg_sub, sub_neg_eq_add]
      apply Int.dvd_add
      rw[pow4,mul_assoc]
      apply Int.dvd_mul_right
      rw[mul_assoc,mul_comm,pow_two,mul_assoc,mul_assoc]
      apply Int.dvd_mul_right
      simp at sec_term_2
      apply Int.ModEq.eq
      calc 2 * q (m + k) ^ 2 + p (m + k) ^ 2 ≡ 2 * (q (k - 1) * (p m ^ 2 ^ k)) ^ 2 +  (p (k - 1) * (p m ^ 2^k)) ^ 2[ZMOD q m]:=by
            apply Int.ModEq.add
            rw[pow_two,pow_two]
            apply Int.ModEq.mul
            rfl
            apply Int.ModEq.mul qa qa
            rw[pow_two,pow_two]
            apply Int.ModEq.mul pa pa
          _ ≡ (2* q (k-1) ^2 + p (k-1) ^2) * (p m ^ 2 ^ k) ^2[ZMOD q m]:=by
            rw[mul_pow,mul_pow,←mul_assoc,add_mul]
          _ ≡ q k * p m ^ 2 ^ (k + 1)[ZMOD q m]:=by
            rw[←h₃,←pos_sub_add_one k h];ring_nf;rfl
--Claim 3: $p_{n+i} \equiv 2^{2^{i-1}}p_{i-1}q_n^{2^i} \pmod{p_n}$
--Claim 4:  $q_{n+i} \equiv 2^{2^i}q_{i-1}q_n^{2^{i-1}} \pmod{p_n}$  for all  $i \geq 1$ . The original proof on the aops is wrong.
  have claim3 (n:ℕ) (i :ℕ) (hi:1 ≤ i): (p (n+i)% (p n)=2^(2^ (i-1)) * (p (i-1))*(q n)^(2^i) % (p n)) ∧ (q (n+i)% (p n)= 2^2^(i-1) *(q (i-1))* (q n)^(2^i) % (p n)):=by
    induction' i with k hk
    contradiction
    constructor
    by_cases h:k<1
    · norm_num at h;rw[h]
      simp only [zero_add, pow_one, Int.reducePow, le_refl, tsub_eq_zero_of_le,h₀,mul_one,pow_zero,h₂]
      apply Int.ModEq.eq
      apply Int.modEq_iff_dvd.mpr
      simp only [sub_sub_cancel,pow_two]
      norm_num
    · replace h : 1≤ k :=by linarith
      rcases hk h with ⟨pa,qa⟩
      simp only [add_tsub_cancel_right]
      rw[←add_assoc,h₂]
      apply Int.ModEq.eq
      have ksub_add:k=k-1+1:=by norm_num[h]
      have :n+k=n+k-1+1:=by
            rw[ksub_add]
            simp only [add_succ_sub_one, add_left_inj,add_assoc]
      calc 2 * q (n + k) ^ 2 - (p (n + k)) ^ 2
         ≡ 2 * (2 * q (n+ k - 1)^2 + p (n+k-1) ^2 ) ^ 2 -( 2 * q (n+ k - 1)^2 - p (n+k-1) ^2) ^ 2 [ZMOD p n]:=by
            rw[←h₃,←h₂,←h₂,←h₂,this,add_tsub_cancel_right]
        _≡  2 *( 2 ^ 2 ^ (k - 1) * q (k - 1) * q n ^ 2 ^ k)^ 2 - (2 ^ 2 ^ (k - 1) * p (k - 1) * q n ^ 2 ^ k)^ 2 [ZMOD p n]:=by
            apply Int.ModEq.sub;apply Int.ModEq.mul;rfl;
            apply Int.ModEq.pow;rw[←h₃,←this];exact qa
            apply Int.ModEq.pow;rw[←h₂,←this];exact pa
        _≡ 2 ^ 2 ^ k * p k * q n ^ 2 ^ (k + 1) [ZMOD p n]:=by
            nth_rewrite 8[ksub_add]
            rw[h₂,mul_pow,mul_pow _ (q n ^2^k),←mul_assoc,← sub_mul,←pow_mul,pow_add,pow_one,mul_pow,←pow_mul,←Nat.pow_add_one 2,←ksub_add,mul_pow,←pow_mul,←Nat.pow_add_one 2,←ksub_add,←mul_assoc,mul_comm 2,mul_assoc,mul_sub]
    by_cases h:k<1
    · norm_num at h;rw[h]
      simp only [zero_add, pow_one, Int.reducePow, le_refl, tsub_eq_zero_of_le,h₁,mul_one,pow_zero,h₃]
      apply Int.ModEq.eq
      apply Int.modEq_iff_dvd.mpr
      simp only [sub_sub_cancel,pow_two]
      norm_num
    · replace h : 1≤ k :=by linarith
      rcases hk h with ⟨pa,qa⟩
      simp only [add_tsub_cancel_right]
      rw[←add_assoc,h₃]
      apply Int.ModEq.eq
      have ksub_add:k=k-1+1:=by norm_num[h]
      have :n+k=n+k-1+1:=by
            rw[ksub_add]
            simp only [add_succ_sub_one, add_left_inj,add_assoc]
      calc 2 * q (n + k) ^ 2 + (p (n + k)) ^ 2
         ≡ 2 * (2 * q (n+ k - 1)^2 + p (n+k-1) ^2 ) ^ 2 +( 2 * q (n+ k - 1)^2 - p (n+k-1) ^2) ^ 2 [ZMOD p n]:=by
            rw[←h₃,←h₂,←h₃,←h₃,this,add_tsub_cancel_right]
        _≡  2 *( 2 ^ 2 ^ (k - 1) * q (k - 1) * q n ^ 2 ^ k)^ 2 + (2 ^ 2 ^ (k - 1) * p (k - 1) * q n ^ 2 ^ k)^ 2 [ZMOD p n]:=by
            apply Int.ModEq.add
            · apply Int.ModEq.mul;rfl;
              apply Int.ModEq.pow;rw[←h₃,←this];exact qa
            · apply Int.ModEq.pow;rw[←h₂,←this];exact pa
        _≡ 2 ^ 2 ^ k * q k * q n ^ 2 ^ (k + 1) [ZMOD p n]:=by
            nth_rewrite 8[ksub_add]
            rw[h₃,mul_pow,mul_pow _ (q n ^2^k),←mul_assoc,← add_mul,←pow_mul,pow_add,pow_one,mul_pow,←pow_mul,←Nat.pow_add_one 2,←ksub_add,mul_pow,←pow_mul,←Nat.pow_add_one 2,←ksub_add,←mul_assoc,mul_comm 2,mul_assoc,mul_add]
--We first prove that p n and p n are coprime. This is used in the recursion step.
  have diagonal (n : ℕ): IsCoprime (p n) (q n) := by
    induction' n with k hk
    norm_num[h₀, h₁]
    rw[h₂,h₃]
    rw[(id1 (p k) (q k)).1]
    apply IsCoprime.add_mul_right_right_iff.mpr
    apply IsCoprime.mul_right
    rw[sub_eq_add_neg,add_comm]
    apply IsCoprime.add_mul_left_left
    apply IsCoprime.neg_left;apply Int.coprime_iff_nat_coprime.mpr;simp only [Int.reduceAbs,
      coprime_two_right]
    apply Odd.natAbs (Odd.pow (oddpq k).1)
    rw[←neg_neg (2 * q k ^ 2 - p k ^ 2)]
    apply IsCoprime.neg_left;simp only [neg_sub]
    rw[(id1 (p k) (q k)).2,add_comm]
    apply IsCoprime.add_mul_right_left
    apply IsCoprime.mul_left;apply Int.coprime_iff_nat_coprime.mpr;simp only [Int.reduceAbs,
      coprime_two_left];apply Odd.natAbs (Odd.pow (oddpq k).1)
    symm
    apply IsCoprime.neg_right
    apply IsCoprime.pow hk
--We prove that we can recurse on m
  have precm (m n:ℕ) (nlem:n ≤ m): IsCoprime (p (m-n-1)) (q n)-> IsCoprime (p m) (q n):=by
    have msubn:m=n+(m-n):=by norm_num[nlem]
    intro redm
    by_cases diag:m=n
    · rw[diag]
      apply diagonal
    by_cases difone:m=n+1
    · apply coprime_mod_equiv (-(p n) ^2)
      rw[difone,h₂]
      apply Int.modEq_iff_dvd.mpr;simp only [sub_neg_eq_add, sub_add_cancel]
      rw[pow_two,←mul_assoc];apply dvd_mul_left
      apply IsCoprime.neg_left
      apply IsCoprime.pow_left
      apply diagonal
    · apply coprime_mod_equiv (p (m - n - 1) * p n ^ 2 ^ (m-n));symm
      nth_rewrite 1[msubn]
      replace nlem:1≤m-n:=by
        contrapose! diag
        simp only [lt_one_iff] at diag
        rw[←add_zero n,←diag,Nat.add_sub_cancel' nlem]
      rcases claim1 n (m-n) nlem with ⟨pa,_⟩
      replace nlem:1≠m-n:=by
        contrapose! difone;rw[difone,Nat.add_sub_cancel'];linarith
      rw[pa]
      split;rename_i hmn;contrapose! nlem;rw[hmn];rfl
      apply IsCoprime.mul_left redm
      apply IsCoprime.pow_left (diagonal n)
--We prove that we can recurse on n
  have qrecn (m n:ℕ) (mlen:m ≤ n): IsCoprime (p m) (q (n-m-1))-> IsCoprime (p m) (q n):=by
    have nsubm:n=m+(n-m):=by norm_num[mlen]
    intro redm
    by_cases diag:m=n
    · rw[diag]
      apply diagonal
    · apply IsCoprime.symm;apply IsCoprime.symm at redm
      apply coprime_mod_equiv (2 ^ 2 ^ (n-m - 1) * q (n-m - 1) * q m ^ 2 ^ (n-m))
      replace mlen:1≤n-m:=by
        contrapose! diag
        simp only [lt_one_iff] at diag
        rw[←add_zero m,←diag,Nat.add_sub_cancel' mlen]
      rcases claim3 m (n-m) mlen with ⟨_,qa⟩
      rw[←nsubm] at qa;rw[qa]
      apply IsCoprime.mul_left
      apply IsCoprime.mul_left
      apply IsCoprime.pow_left
      apply Int.isCoprime_iff_gcd_eq_one.mpr;rw[Int.gcd]
      simp only [Int.reduceAbs, coprime_two_left]
      apply Odd.natAbs;apply (oddpq m).1;exact redm
      apply IsCoprime.pow_left (IsCoprime.symm (diagonal m))
  intro m n
--We use the euc_ind
  apply euc_induction m n
  intros;rw[h₁];apply isCoprime_one_right
  intros;rw[h₀]; apply isCoprime_one_left
  exact qrecn;apply precm
