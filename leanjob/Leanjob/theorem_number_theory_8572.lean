import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat


/- Let  $a_1, a_2,\cdots , a_n$  and  $b_1, b_2,\cdots , b_n$  be (not necessarily distinct) positive integers. We continue the sequences as follows: For every  $i>n$ ,  $a_i$  is the smallest positive integer which is not among  $b_1, b_2,\cdots , b_{i-1}$ , and  $b_i$  is the smallest positive integer which is not among  $a_1, a_2,\cdots , a_{i-1}$ . Prove that there exists  $N$  such that for every  $i>N$  we have  $a_i=b_i$  or for every  $i>N$  we have  $a_{i+1}=a_i$ .-/

theorem number_theory_8572 (n : ℕ) (a b : ℕ → ℕ ) (h₀ : ∀ i, 0 < a i)  (h₁ : ∀ i, 0 < b i)
  (h₂ : ∀ i>n, (∀ j<i, a i ≠ b j) ∧ (∀ x>0, (∀ j<i, x≠ b j)->a i ≤ x)) (h₃ : ∀ i>n, (∀ j<i, b i ≠ a j) ∧ (∀ x>0, (∀ j<i, x≠ a j)->b i ≤ x)) :
  ∃ N, ∀ i>N , (a i = b i) ∨  a (i + 1) = a i := by
--We prove that N=n is the desired one.
  use n; intro i hi
--We prove that (¬ p->q)->(p∨q)
  by_contra! hk;rcases hk with ⟨k1,k2⟩
  contrapose! k2
  simp_all only [gt_iff_lt, ne_eq, not_false_eq_true]
  rw[Nat.eq_iff_le_and_ge]
  rcases h₂ (i+1) (by linarith) with ⟨h21,h22⟩
  rcases h₂ i (by linarith) with ⟨h22',h22''⟩
--We prove that a i and a (i+1) satisfies each others universal property.
  constructor
  · apply h22 (a i) (h₀ i)
    intro j hj
    by_cases jeqi:j=i
    rw[jeqi];exact k1
    replace jeqi :j<i:=by
      apply lt_iff_le_and_ne.mpr
      constructor
      apply Nat.le_of_lt_succ
      exact hj
      exact jeqi
    apply h22';linarith
  · apply h22'';apply h₀;intro j hj;apply h21;linarith
