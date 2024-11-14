import Mathlib

open Set Real

/-Let the set $M = \{x | x^2 - 2x - 3 < 0\}$, and the set $N = \{x | 2x < 2\}$. Find the intersection of set $M$ with the complement of set $N$ in the real numbers $R$, denoted as $M \cap \complement_R N$.-/
theorem algebra_9020 {M N : Set ℝ}
    (hM : M = {x | x ^ 2 - 2 * x - 3 < 0}) (hN : N = {x | 2 * x < 2}) :
    M ∩ (Set.compl N) = {x | 1 ≤ x ∧ x < 3} := by
    rw[hM,hN]
    simp only [sub_neg, Nat.ofNat_pos, mul_lt_iff_lt_one_right,Set.compl,Set.mem_inter]
    simp only [mem_setOf_eq, not_lt]
    rw[←Set.sep_mem_eq]
    simp only [mem_setOf_eq]
    ext x
    simp only [mem_setOf_eq, and_imp]
    rw[pow_two,←sub_mul,←one_mul 3]
    constructor
    rintro ⟨ine1,ine2⟩
    constructor
    linarith
    contrapose! ine1
    apply mul_le_mul
    repeat linarith
    rintro ⟨ine1,ine2⟩
    simp_all only [and_true]
    apply mul_lt_mul
    repeat linarith
