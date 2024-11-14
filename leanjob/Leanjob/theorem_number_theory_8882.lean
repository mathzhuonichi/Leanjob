import Mathlib
open Mathlib


/-
  Determine all solutions of the diophantine equation
  $a^2 = b \cdot (b + 7)$  in integers  $a\ge 0$  and  $b \ge 0$ .
  (W. Janous, Innsbruck)
-/
theorem number_theory_8882 (a b : ℕ) : a ^ 2 = b * (b + 7) ↔ (a, b) ∈ ({(0, 0), (12, 9)} : Set <| ℕ × ℕ) := by
  constructor
  · -- we begin by solving the equation
    intro hab
    rw [<-Int.ofNat_inj] at hab
    simp at hab
    let m := 2 * b + 7
    -- transform the equation and obtain that
    have : m ^ 2 -  4 * a ^ 2 = (49 : ℤ) := by rw [hab]; simp [m]; ring;
    have hmul : (m + 2 * a) * (m - 2 * a) = (49 : ℤ) := by linarith
    have hdvd : ↑(m + 2 * a) ∣ (49 : ℤ) := by exact Dvd.intro (↑m - 2 * ↑a) hmul

    -- determine that m + 2 * a can only be in {1 , 7, 49}, since it divides 49 = 7 * 7
    have hrange : (m + 2 * a) ∣ 49 →  ↑(m + 2 * a) ∈ ({1, 7, 49} : Set ℤ):= by
      intro hdvd
      have h : m + 2 * a ≤ 49 := by apply Nat.le_of_dvd (Nat.zero_lt_succ 48) hdvd;
      interval_cases (m + 2 * a)
      all_goals
        revert hdvd
        decide
    obtain h := hrange <| Int.ofNat_dvd.mp hdvd
    simp at h

    -- we are done by analyzing the three cases, respectively
    cases h with
    -- m + 2 * a = 1 -/
    | inl h =>
      have : m - 2 * a = (49 : ℤ) := by rw [h, one_mul] at hmul; linarith
      linarith
    -- m + 2 * a = 7
    | inr h =>
      cases h with
      | inl h =>
        have : m - 2 * a = (7 : ℤ) := by rw [h] at hmul; linarith
        have hm : m = (7 : ℤ) := by linear_combination (norm := linarith) h + this;
        have ha' : a = 0 := by rw [hm] at h; linarith
        have hb' : b = 0 := by simp [m] at hm; exact hm
        simp [ha', hb']
      -- m + 2 * a = 49
      | inr h =>
        simp at h
        have : m - 2 * a = (1 : ℤ) := by rw [h] at hmul; linarith
        have hm : m = (25 : ℤ) := by linear_combination (norm := linarith) h + this;
        have ha' : a = 12 := by rw [hm] at h; linarith
        have hb' : b = 9 := by simp [m] at hm; linarith
        simp [ha', hb']
  · -- verify the answer
    intro h
    cases h with
    | inl h => simp_all
    | inr h => simp_all
