import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat Polynomial
/-$P(x)$  is a polynomial in  $x$  with non-negative integer coefficients. If  $P(1)=5$  and  $P(P(1))=177$ , what is the sum of all possible values of  $P(10)$ ?-/
theorem number_theory_595 :
  ∑ᶠ p ∈ {p : Polynomial ℕ | p.eval 1 = 5 ∧ p.eval (p.eval 1) = 177}, p.eval 10 = 1202 := by
  have sumrange4 (f:ℕ→ℕ):∑ i∈Finset.range 4, f i=f 0+f 1+f 2+f 3:=by
    have:4=1+1+1+1:=rfl
    rw[this]
    rw[Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_one]
--We prove that there exists only one such polynomial
  have exactp (p : Polynomial ℕ) (hp: p.eval 1 = 5 ∧ p.eval (p.eval 1) = 177):p.coeff 0=2∧p.coeff 1=0∧p.coeff 2=2∧p.coeff 3=1∧ (∀ n≥4,p.coeff n=0):=by
    rcases hp with ⟨h1,h5⟩;rw[h1] at h5
--Because all coeff. are nonneg, each one ≤ sum of coeff.=eval 1 p
    have bacoe(n:ℕ):(p.coeff n)≤5:=by
      rw[←h1]
      simp only [coeff,eval,eval₂,eq_natCast, Nat.cast_id, one_pow, mul_one,sum]
      by_cases coen:p.toFinsupp n=0
      rw[coen];norm_num
      apply Finset.single_le_sum
      norm_num
      simp only [mem_support_iff, ne_eq,coeff,coen,not_false_eq_true]
    have coenonneg(n:ℕ):0≤p.coeff n *5^n:=by norm_num
--Because eval 5 p=177, we know terms higher than 3 are zero.
    have bcoege4 (n:ℕ) (hn:4≤n):p.coeff n=0:=by
      contrapose! h5
      apply Nat.ne_of_gt
      replace h5:1≤p.coeff n:= Nat.one_le_iff_ne_zero.mpr h5
      simp only [eval,eval₂,eq_natCast, Nat.cast_id, one_pow, mul_one,sum]
      have aux:177<(p.coeff n)*5^n:=by
        have :177<1*5^4:=by linarith
        apply lt_of_lt_of_le this
        apply Nat.mul_le_mul h5
        apply Nat.pow_le_pow_of_le (by norm_num) hn
      apply lt_of_lt_of_le aux
      set foo :ℕ->ℕ:= fun x=>(p.coeff x)*5^x
      have foon (n:ℕ):(p.coeff n)*5^n=foo n:=rfl
      rw[foon]
      apply Finset.single_le_sum;norm_num;
      simp only [mem_support_iff];linarith
    have supp4:p.support⊆Finset.range 4:=by
      simp only [Subset]
      intro x hx
      simp only [mem_support_iff] at hx
      simp only [Finset.mem_range]
      contrapose! hx
      apply bcoege4;linarith
    have exp:p=∑ i ∈ Finset.range 4, (monomial i) (p.coeff i):=by
      nth_rewrite 1[Polynomial.as_sum_support p]
      apply Finsupp.sum_of_support_subset
      apply supp4
      simp only [Finset.mem_range, map_zero, implies_true]
    have evalx (x:ℕ):eval x p= ∑ i ∈ Finset.range 4, (p.coeff i)*x^i:=by
      rw[eval_eq_sum,sum]
      apply Finset.sum_subset supp4
      intro y _ yne
      simp only [mem_support_iff, ne_eq, Decidable.not_not] at yne
      rw[yne,zero_mul]
--p has at most four terms.
    replace evalx (x:ℕ):eval x p= p.coeff 0 +p.coeff 1*x+p.coeff 2*x^2+p.coeff 3*x^3 :=by
      rw[evalx,sumrange4]
      simp only [pow_zero, mul_one, pow_one]
    rw[evalx] at h1 h5
    simp only [mul_one, one_pow, reducePow] at h1 h5
    replace bacoe (n:ℕ): p.coeff n≤4:=by
      apply Nat.le_of_lt_add_one
      apply lt_of_le_of_ne (bacoe n)
      by_contra hn
      have nle3:n≤3:=by
        by_contra! h;
        have :p.coeff n=0:=by
          apply bcoege4
          linarith
        rw[this] at hn
        contradiction
      contrapose! h5
      interval_cases n
      repeat' (rw[hn] at h1; linarith)
    rw[←and_assoc,←and_assoc,←and_assoc]
    constructor
    pick_goal 2
    apply bcoege4
    have coea:p.coeff 0≤4∧p.coeff 1≤4∧p.coeff 2≤4∧ p.coeff 3≤4:=by
      constructor;apply bacoe;constructor;apply bacoe;constructor;apply bacoe;apply bacoe
--We have only finite cases, so we can check it one by one.
    rcases coea with ⟨h₀,h₁,h₂,h₃⟩
    interval_cases p.coeff 0;
    all_goals
      interval_cases p.coeff 1
      all_goals
        interval_cases p.coeff 2
        all_goals
          interval_cases p.coeff 3
          all_goals
            revert h5
            decide
--The only such polynomial is 2+X*0+X^2*2+X^3*1
  have :{p : Polynomial ℕ | p.eval 1 = 5 ∧ p.eval (p.eval 1) = 177}={2+X*0+X^2*2+X^3*1}:=by
    ext p;constructor;intro hp
    simp at hp
    replace hp:p.coeff 0 = 2 ∧ p.coeff 1 = 0 ∧ p.coeff 2 = 2 ∧ p.coeff 3 = 1 ∧ ∀ n ≥ 4, p.coeff n = 0:=by
      apply exactp
      apply hp
    rcases hp with ⟨h0,h1,h2,h3,hge⟩
    ext n
    by_cases hn:n≤3
    interval_cases n
    aesop
    aesop
    aesop
    aesop
    have :p.coeff n=0:=by
      apply hge
      linarith
    rw[this]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simp only [mul_zero, add_zero, mul_one]
    have hdeg:(2 + X ^ 2 * 2 + X ^ 3 :ℕ[X]).natDegree ≤ 3:=by
      compute_degree
    apply lt_of_le_of_lt hdeg
    linarith
    intro hp
    simp only [mul_zero, add_zero, mul_one, Set.mem_singleton_iff] at hp
    simp only [Set.mem_setOf_eq]
    rw[hp]
    simp only [eval_add, eval_ofNat, eval_mul, eval_pow, eval_X, one_pow, one_mul, reduceAdd,
      reducePow, reduceMul, and_self]
  rw[this]
--We evaluate the answer.
  simp only [mul_zero, add_zero, mul_one, Set.mem_singleton_iff, finsum_cond_eq_left, eval_add,
    eval_ofNat, eval_mul, eval_pow, eval_X, reducePow, reduceMul, reduceAdd]
