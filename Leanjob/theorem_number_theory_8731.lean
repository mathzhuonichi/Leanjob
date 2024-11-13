import Mathlib

open BigOperators Rat Int Nat
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


noncomputable def p: ℕ->ℕ
  | n => Nat.nth Nat.Prime n

noncomputable def findindex (n k : ℕ) : ℕ :=
  if k = 0 then 0
  else  if k = 1 then
          if n = 0 then 2
          else findindex (n - 1) (p (n - 1))  + 1
        else findindex n (k - 1) + 1
termination_by (n,k)

noncomputable def findindex' : ℕ → ℕ → ℕ
  | _, 0     => 0
  | 0, 1     => 2
  | m + 1, 1 => findindex' m (p m) + 1
  | n, k + 1 => findindex' n k + 1


-- Define the function that maps each natural number to its greatest prime divisor
def gstfac (n : ℕ) : ℕ :=
  if n = 0 ∨ n = 1 then 1
  else Nat.findGreatest (fun d => d ∣ n ∧ Nat.Prime d) n

variable (f : ℕ → ℕ)(h₀ : f 0 = 1)(h₁ : f 1 = 2)  (H1 : ∀ (i : ℕ), (∃ (k m : ℕ), k < p m ∧ f i = k * p m) → f (i + 1) = (k + 1) * p m) (H2 : ∀ (i : ℕ), (∃ (m : ℕ), f i = p m ^ 2) → f (i + 1) = p (m + 1))

include h₀ h₁ H1 H2

theorem number_theory_8731_1 : ∀ (i j : ℕ), i < j → f i ≠ f j := sorry
theorem number_theory_8731_2 : ∀ (i : ℕ), i > 964 → 100 ≤ f i := sorry
theorem number_theory_8731_3 : ∀ (x : ℕ), x > 1 → x > (gstfac x)^2 → ¬(∃ (i : ℕ), f i = x) := sorry
theorem number_theory_8731_4 : (Finset.filter (fun i => f i < 100) (Finset.range 964)).card = 62 := sorry
