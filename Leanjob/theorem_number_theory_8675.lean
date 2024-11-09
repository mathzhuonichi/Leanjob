import Mathlib
import Aesop
open BigOperators Real Nat Topology Rat Int Finset
-- Find the number of pairs  $(n, q)$ , where  $n$  is a positive integer and  $q$  a non-integer rational number with  $0 < q < 2000$ , that satisfy  $\{q^2\}=\left\{\frac{n!}{2000}\right\}$

def denominator_list : List ℕ :=
  (List.range' 0 14).map (fun n => ((factorial n : ℚ) / 2000).den)
#eval denominator_list
#eval denominator_list.getD 6 0
#eval denominator_list.getD 9 0

lemma hans:(fract (3/5:ℚ) ≠ 0) ∧ fract ((3/5: ℚ )^2) = fract (6 !/2000:Rat):=by
    simp_all only [ne_eq]
    norm_num
    simp only [fract]
    norm_num
    repeat' rw[factorial]
    simp only [succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat,fract]
    norm_num

theorem number_theory_8675 : ∀ (n:ℕ) (q:ℚ) (h₀:0< q ∧ q <2000) (h:fract q ≠ 0), fract (q^2) = fract (n !/2000:Rat) ↔ (n=6 ∧ q = 3/5):=by
  have rat_sub_int_den (x:ℚ) (m:ℤ):x.den=(x-m).den :=by
    rw[Rat.sub_def]
    simp[Rat.normalize]
    have aux:((x.num - m * ↑x.den).natAbs.gcd x.den) =1:=by
      nth_rewrite 2[←Int.natAbs_ofNat (x.den)]
      rw[←Int.gcd]
      apply Int.isCoprime_iff_gcd_eq_one.mp
      rw[sub_eq_add_neg,←neg_mul]
      apply IsCoprime.add_mul_right_left
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      rw[Int.gcd]
      simp only [natAbs_ofNat]
      exact x.reduced
    rw[aux];simp only [Nat.div_one]
  have den_fract (x:ℚ):x.den=(fract x).den:=by
    rw[fract];
    apply rat_sub_int_den
  have in_int (x:ℚ): (∃ (k:ℤ), k=x)  ↔ fract x=0:=by
    constructor
    · intro ⟨k,hk⟩;rw[←hk];simp only [fract_intCast]
    · intro h;rw[fract,sub_eq_zero] at h;use ⌊x⌋;rw[←h]
  have frac_zero_iff_dvd (m n:ℤ) (mpos:0≠m):m∣n ↔ fract (n / m: ℚ )=0:=by
    constructor
    intro h
    apply dvd_iff_exists_eq_mul_left.mp at h
    rcases h with ⟨d,h⟩
    rw[h]
    field_simp
    intro h
    apply (in_int _).mpr at h
    rcases h with ⟨k,hk⟩
    apply dvd_iff_exists_eq_mul_left.mpr
    use k
    apply Rat.intCast_inj.mp
    field_simp[hk]
  intro n q ⟨h₀1,h₀2⟩ hq
  have q_eq_abs:|q|=q:=by
      apply abs_eq_self.mpr;linarith
  symm
  constructor
  rintro ⟨ndef,qdef⟩
  rw[ndef,qdef]
  exact hans.2
  intro hnq
  have q_sq_nint: fract (q^2)≠ 0:=by
    contrapose! hq
    rcases (in_int _).mpr hq with ⟨k,hk⟩
    have issq:IsSquare k:=by
      apply Rat.isSquare_intCast_iff.mp
      rw[hk,pow_two,IsSquare]
      aesop
    apply (in_int q).mp
    replace issq: ∃ m, m^2=k:=by
      rw[IsSquare,] at issq
      rcases issq with ⟨r,hr⟩
      use r;rw[hr,pow_two]
    rcases issq with ⟨m,hm⟩
    use m.natAbs;rw[←hm] at hk;simp at hk
    rw[←q_eq_abs]
    apply (sq_eq_sq _ _).mp
    simp[hk];simp;simp
  rw[hnq] at q_sq_nint
  have fac2000:2000 ∣15 !:=by
    simp only [factorial]
    norm_num
  have mid_fac(n:ℕ) (ngefift:15 ≤ n):2000∣n !:=by
    apply dvd_trans fac2000
    apply Nat.factorial_dvd_factorial ngefift
  have nub:n<15:=by
    contrapose! mid_fac
    use n;simp[mid_fac];
    rcases frac_zero_iff_dvd 2000 (n !) _ with h
    simp at h;simp at q_sq_nint;simp[←h] at q_sq_nint;
    contrapose! q_sq_nint;apply Int.natCast_dvd_natCast.mpr q_sq_nint
  have den_is_sq:IsSquare ((q^2).den) ∧ IsSquare (n !/2000 : ℚ).den:=by
    constructor
    · field_simp;rw[IsSquare];use q.den;rw[pow_two]
    · rw[den_fract,←hnq,←den_fract];field_simp;rw[IsSquare];use q.den;rw[pow_two]
  rcases den_is_sq with ⟨_,hns⟩
  have casesn:n ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]:=by
    exact List.mem_range.2 nub
  have nsquare:(¬ IsSquare 2000)∧ (¬ IsSquare 1000) ∧ (¬ IsSquare 250)∧ (¬ IsSquare 50)∧ (¬ IsSquare 5):=sorry
  fin_cases casesn
  · simp at hns;contrapose! hns;exact nsquare.1;
  · simp at hns;contrapose! hns;exact nsquare.1;
  · simp at hns;contrapose! hns;norm_num;simp;exact nsquare.2.1
  · simp at hns;contrapose! hns;simp only[factorial];sorry
  · sorry
  · simp at hns;contrapose! hns;simp only[factorial];norm_num;sorry
--n=6 has solution
  · constructor;simp;
    simp only[factorial] at hnq;norm_num at hnq;
    have:fract (9/25: ℚ )=9/25:=by norm_num
    rw[this] at hnq
    rw[]
    sorry

  -- have :(n ! / 2000 :ℚ).den= denominator_list.getD n 0:=by
  --   unfold denominator_list
  --   simp only [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem number_theory_8675': Set.ncard {(n,q) : ℕ × ℚ | (0< q ∧ q <2000)∧  fract q ≠ 0 ∧ fract (q^2) = fract (n ! / 2000 : ℚ)} = 1:=by
  simp only [ne_eq, Set.ncard_eq_one, Prod.exists]
  use 6
  use 3/5
  apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
  constructor
  use ( 6 , 3/5)
  simp only [Set.mem_setOf_eq]
  constructor
  norm_num
  exact hans
  simp only [Set.mem_setOf_eq, and_imp, Prod.forall, Prod.mk.injEq]
  intro a b hbd hba hb
  apply (number_theory_8675 a b ⟨hbd,hba⟩ hb).mp
