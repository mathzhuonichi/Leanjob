-- Find the number of pairs  $(n, q)$ , where  $n$  is a positive integer and  $q$  a non-integer rational number with  $0 < q < 2000$ , that satisfy  $\{q^2\}=\left\{\frac{n!}{2000}\right\}$
import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

-- theorem number_theory_8675 :
--   Set.ncard {p : ℕ × ℚ | p.1 > 0 ∧ ¬ p.2 ∈ ℤ ∧ 0 < p.2 ∧ p.2 < 2000 ∧ Int.fract (p.2^2) = Int.fract (p.1 ! / 2000)} = 189 := by
--   sorry
