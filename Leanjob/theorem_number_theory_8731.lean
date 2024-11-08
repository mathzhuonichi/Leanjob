import Mathlib
import Aesop

open scoped BigOperators

/- Let  $p_n$  be the  $n$ -th prime. ( $p_1=2$ )
-- Define the sequence  $(f_j)$  as follows:
-- -  $f_1=1, f_2=2$
-- -  $\forall j\ge 2$ : if  $f_j = kp_n$  for  $k< p_n$  then  $f_{j+1}=(k+1)p_n$
-- -  $\forall j\ge 2$ : if  $f_j = p_n^2$  then  $f_{j+1}=p_{n+1}$

-- (a) Show that all  $f_i$  are different
-- (b) from which index onwards are all  $f_i$  at least 3 digits?
-- (c) which integers do not appear in the sequence?
-- (d) how many numbers with less than 3 digits appear in the sequence?-/

-- Define a list with the first 26 known primes
def first_26_primes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
                                 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
                                 73, 79, 83, 89, 97, 101]

-- Define the 26th prime using the manually defined list
def prime_26 := first_26_primes.getD 25 0  -- 0-based indexing, so 25 gives the 26th element

-- Prove that the 26th prime is indeed 101
theorem prime_26_is_101 : prime_26 = 101 := by
  unfold prime_26
  rw [List.getD_eq_getElem?_getD]
  -- Check that the 26th element is 101 in `first_26_primes`
  rfl
theorem aux:Nat.nth Nat.Prime 26=101:=by
  sorry
theorem number_theory_8731
  (p : ℕ → ℕ)
  (f : ℕ → ℕ)
  (h1 : f 0 = 1)
  (h2 : f 1 = 2)
  (hf : ∀ j ≥ 2, ((∃ k < p j, f (j - 1) = k * p j) ∨ (f (j - 1) = (p j) ^ 2)) → f j = (f (j - 1) / p j + 1) * p j)
  (hf' : ∀ j ≥ 2, f (j - 1) = (p j) ^ 2 → f j = p (j + 1)) :
  (∀ i, f i ≠ f (i + 1)) ∧
  (∃ i, ∀ j ≥ i, f j ≥ 100) ∧
  {n | ¬ ∃ j, f j = n} = {2} ∧
  Set.ncard {j | f j < 100} = 10 :=
sorry
