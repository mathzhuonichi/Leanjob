import Mathlib

open Real
open scoped BigOperators

theorem number_theory_8538 {p : ℕ} (hp : Odd p) (hp1 : Nat.Prime p) (m : Fin p → ℕ) (hm :(i: Fin p) (i< p-1) →  m (i.succ)=(m i) +1) (σ : Equiv.Perm (Fin p)) :
  ∃ k l : Fin p, k ≠ l ∧ p ∣ m k * m (σ k) - m l * m (σ l) :=by
  sorry
