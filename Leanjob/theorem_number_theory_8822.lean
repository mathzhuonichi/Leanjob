import Mathlib
open Mathlib


def sum (f : ℕ → ℕ+) (i j : ℕ) : ℕ := ∑ i ∈ Finset.Ico i j, (f i)

def mul (f : ℕ → ℕ+) (op : Finset <| ℕ × ℕ) : ℕ := ∏ x ∈ op, sum f x.fst x.snd

def get_op (a i j m: ℕ) (h : i < j) : Finset <| ℕ × ℕ :=
    match m with
    | 0 => {}
    | k + 1 =>
      if k + 1 = j - a then
        (get_op a i j (i - a) h) ∪ {(i, j)}
      else
        (get_op a i j k h) ∪ {(a + k, a + k + 1)}

def norm_op (a m : ℕ) (op : Finset <| ℕ × ℕ) := ∀ x ∈ op, ((a ≤ x.1 ∧ x.1 < x.2 ∧ x.2 ≤ a + m) ∧
  (∀ y ∈ op, Finset.Ico x.1 x.2 ∩ Finset.Ico y.1 y.2 ≠ ∅ → x = y)) ∧ ⋃ z ∈ op, Finset.Ico z.1 z.2 = ((Finset.Ico a (a + m)) : Set ℕ)

/-
  $101$  positive integers are written on a line. Prove that we can write signs  $ \plus{}$ ,
  signs  $ \times$  and parenthesis between them, without changing the order of the numbers,
  in such a way that the resulting expression makes sense and the result is divisible by  $ 16!$ .
-/

theorem number_theory_8822(f : ℕ → ℕ+) : ∃ op : Finset <| ℕ × ℕ, norm_op 0 101 op ∧ Nat.factorial 16 ∣ mul f op := by

  -- We first prove given any m≥2 and [a, a+m), we can choose a way to fulfill m ∣ mul f op
  have exists_dvd (a m : ℕ) (hm : m ≥ 2) : ∃ op : Finset <| ℕ × ℕ, norm_op a m op ∧ m ∣ mul f op := by
    -- We define the prefix_sum of these numbers, i.e., prefix_sum n = f(0) + ⋯ + f(n)
    let prefix_sum (n : ℕ) : ℕ := ∑ i in Finset.range n, f i

    -- It's trivial that ∑_{i≤ k < j} f(k) = prefix_sum j - prefix_sum i
    have sub_prefix (i j : ℕ) (hi : i ≤ j) : sum f i j = prefix_sum j - prefix_sum i := by
      simp [sum, prefix_sum, <-Finset.sum_range_add_sum_Ico (fun x => (f x).val) hi]

    -- By the pigeonhold principle, we can prove that there exists a≤i< j ≤ a+m such that (prefix_sum j) ≡ (prefix_sum i) mod m -/
    have : ∃ i j : ℕ, a ≤ i ∧ i < j ∧ j ≤ a + m ∧ (prefix_sum j) ≡ (prefix_sum i) [MOD m] := by
      -- we consider the mod of prefix_sum (a+i) for all i
      let mod_m (i : ℕ) := (prefix_sum <| a + i) % m
      -- there are m + 1 such 'i'
      let domain := Finset.range (m + 1)
      -- but only m residue classes
      let img := Finset.range (m)
      have hf (i : ℕ) (_ : i ∈ domain) : mod_m i ∈ img := by
        simp [mod_m, img]
        refine Nat.mod_lt (prefix_sum (a + i)) ?_
        exact Nat.zero_lt_of_lt hm
      have hcard : img.card * 1 < domain.card := by simp [img, domain]
      -- Apply the pigeonhold principle, we get two number i ≠ j such that (prefix_sum i)% m=(prefix_sum j)%m
      obtain ⟨y, ⟨_, h⟩⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hcard
      obtain ⟨i, ⟨j, ⟨hi, ⟨hj, hneq⟩⟩⟩⟩ := Finset.one_lt_card_iff.mp h
      simp [mod_m, domain] at hj hi
      have hmod : (prefix_sum <| a + j) ≡ (prefix_sum <| a + i) [MOD m] := by exact Eq.trans hj.right <| Eq.symm hi.right

      -- By analyzing i < j or j < i, we finish the lemma.
      by_cases h' : i < j
      · use a + i, a + j
        split_ands
        on_goal 4 => exact hmod
        all_goals linarith
      · push_neg at h'
        use a + j, a + i
        split_ands
        on_goal 2 => exact Nat.add_lt_add_left (Nat.lt_of_le_of_ne h' (Ne.symm hneq)) a
        on_goal 3 => exact Nat.ModEq.symm hmod
        all_goals linarith

    -- We choose such i, j obtained by the last lemma and construct op = {(a,a+1),(a+1,a+2),⋯,(i,j),(j,j+1),⋯,(a+m-1,a+m)}
    obtain ⟨i, ⟨j, ⟨hi, ⟨hj, ⟨hm, hmod⟩⟩⟩⟩⟩ := this
    let op := get_op a i j m hj

    -- We prove that construction is correct, i.e., (i,j) ∈ op by induction
    have in_get_op (a m i j : ℕ) (hm : a + m ≥ j) (hj : j > i) (hi : i ≥ a) : (i, j) ∈ get_op a i j m hj := by
      induction m with
      | zero => linarith
      | succ k ih =>
        by_cases hj' : k + 1 + a = j
        · have : k + 1 = j - a := by rw [Nat.sub_eq_of_eq_add]; linarith
          simp [get_op, if_pos this]
        · push_neg at hj'
          rcases Nat.ne_iff_lt_or_gt.mp hj' with hlt | hgt
          · linarith
          · have: a + k ≥ j := by rw [add_comm, <-add_assoc] at hgt; exact Nat.le_of_lt_succ hgt
            have ih := ih this
            have : k + 1 ≠ j - a := by
              apply Nat.ne_of_lt'
              calc
                j - a < (k + 1 + a) - a := by refine Nat.sub_lt_sub_right ?_ hgt; apply Nat.le_trans hi <| Nat.le_of_succ_le hj
                _ ≤ k + 1 := by rw [Nat.add_sub_cancel]
            simp [get_op, if_neg this]
            exact Or.inl ih

    -- We prove that any pair ∈ op is between [a, a+m) and is meaningful by induction
    have norm_ops (a m i j : ℕ) (hj : j > i) (hi : i ≥ a) (h : i < j) :
        norm_op a m (get_op a i j m h) := by
      induction m using Nat.case_strong_induction_on
      · intro x hx
        simp [get_op] at hx
      · intro x hx
        rename_i k ih
        by_cases hj' : k + 1 = j - a
        · simp only [norm_op, get_op, if_pos hj'] at hx
          simp at hx
          have hak : i - a ≤ k := by
            have hj'' := Nat.le_sub_one_of_lt hj
            calc
                i - a ≤ j - 1 - a := by rel [hj'']
                _ ≤ j - a - 1 := by rw [Nat.sub_right_comm]
                _ ≤ (k + 1) + a - a - 1 := by rw [hj', Nat.sub_add_cancel]; apply Nat.le_trans hi <| Nat.le_of_succ_le hj
                _ ≤ k := by rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
          have ih := ih (i - a) hak
          cases hx with
          | inl hx' =>
            simp only [norm_op] at ih
            obtain⟨⟨⟨h1, ⟨h2, h3⟩⟩, h4⟩, h5⟩ := ih x hx'
            simp [Nat.add_sub_cancel' hi] at h3
            split_ands
            · trivial
            · trivial
            · calc
                x.2 ≤ i - a + a := by simp [Nat.sub_add_cancel hi]; exact h3
                _ ≤ k + a := by rel [hak]
                _ ≤  a + (k + 1) := by linarith
            · intro y hy
              simp [get_op, if_pos hj'] at hy
              cases hy with
              | inl hy => exact fun a => h4 y hy a
              | inr hy =>
                intro hcap
                obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
                simp [hy] at hz
                obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
                have : ¬ i ≥ x.2 := by push_neg; exact Nat.lt_of_le_of_lt hz2 hz12
                contradiction
            · sorry
          | inr hx' =>
            simp only [hx', norm_op]
            split_ands
            · trivial
            · trivial
            · simp [hj']; rw [Nat.add_sub_cancel']; linarith
            · intro y hy
              simp [get_op, if_pos hj'] at hy
              cases hy with
              | inl hy =>
                intro hcap
                simp only [norm_op] at ih
                obtain⟨⟨⟨h1, ⟨h2, h3⟩⟩, h4⟩, h5⟩ := ih y hy
                simp [Nat.add_sub_cancel' hi] at h3
                obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
                simp [hy] at hz
                obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
                have : ¬ i ≥ y.2 := by push_neg; exact Nat.lt_of_le_of_lt hz11 hz3
                contradiction
              | inr hy => exact fun a => Eq.symm hy
            · sorry
        · simp [get_op, if_neg hj'] at hx
          have ih := ih k (Nat.le_refl _)
          cases hx with
          | inl hx =>
            obtain⟨⟨⟨h1, ⟨h2, h3⟩⟩, h4⟩, h5⟩ := ih x hx
            split_ands
            · trivial
            · trivial
            · linarith
            · intro y hy
              simp [get_op, if_neg hj'] at hy
              cases hy with
              | inl hy => exact fun a => h4 y hy a
              | inr hy =>
                intro hcap
                obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
                simp [hy] at hz
                obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
                have : ¬ a + k < x.2 := by push_neg; exact h3
                contradiction
            · sorry
          | inr hx =>
            simp only [hx, norm_op]
            split_ands
            · linarith
            · linarith
            · linarith
            · intro y hy
              simp [get_op, if_neg hj'] at hy
              cases hy with
              | inl hy =>
                intro hcap
                simp only [norm_op] at ih
                obtain⟨⟨⟨h1, ⟨h2, h3⟩⟩, h4⟩, h5⟩ := ih y hy
                obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
                simp [hy] at hz
                obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
                have : ¬ a + k < y.2 := by exact Nat.not_lt.mpr h3
                contradiction
              | inr hy => exact fun a_1 => Eq.symm hy
            · sorry


    use op
    -- We prove that m ∣ ∑_{i≤ k < j} f(k) = prefix_sum j - prefix_sum i, which is implied by prefix_sum j ≡ prefix_sum i [mod m]
    have hmdvd : m ∣ prefix_sum j - prefix_sum i := by refine Nat.dvd_of_mod_eq_zero <| Nat.sub_mod_eq_zero_of_mod_eq hmod
    -- Then prove prefix_sum j - prefix_sum i ∣ mul f op, since mul f op = f(a) * f(a+1) * ⋯ ( f(i) + f(i+1) + ⋯ + f(j-1)) * f(j) * ⋯ * f(a+m-1)
    have hsumdvd : prefix_sum j - prefix_sum i ∣ mul f op := by
      simp [mul, <-sub_prefix i j <| Nat.le_of_succ_le hj]
      apply Finset.dvd_prod_of_mem (fun x => sum f x.1 x.2) <| in_get_op a m i j hm hj hi

    -- The set op we obtain exactly gives the way to get the result satifying m ∣ mul f op
    constructor
    · exact norm_ops a m i j hj hi hj
    · exact Nat.dvd_trans hmdvd hsumdvd

  --  Given two disjoint interval [a, a+m₁) and [a+m₁, a+m₁+m₂), and their operations op₁, op₂ such that n₁ ∣ mul f op₁ and n₂ ∣ mul f op₂
  -- we merge them into one interval [a, a+m₁+m₂) and op = op₁ ∪ op₂. All we need to prove is that the new op satisfies n₁ * n₂ ∣ mul f op
  have mul_op (a m₁ m₂ n₁ n₂: ℕ)
      (h₁ : ∃ op₁ : Finset <| ℕ × ℕ, norm_op a m₁ op₁ ∧ n₁ ∣ mul f op₁)
      (h₂ : ∃ op₂ : Finset <| ℕ × ℕ, norm_op (a + m₁) m₂ op₂ ∧ n₂ ∣ mul f op₂) :
      ∃ op : Finset <| ℕ × ℕ, norm_op a (m₁ + m₂) op ∧ n₁ * n₂ ∣ mul f op := by
    simp only [norm_op] at h₁ h₂
    obtain ⟨op₁, h₁⟩ := h₁
    obtain ⟨op₂, h₂⟩ := h₂
    let op := op₁ ∪ op₂
    use op
    constructor
    · intro x hx
      simp [op] at hx
      cases hx with
      | inl hx =>
        split_ands
        · exact h₁.left x hx |>.left.left.left
        · exact h₁.left x hx |>.left.left.right.left
        · apply Nat.le_trans (h₁.left x hx).left.left.right.right; linarith
        · intro y hy
          simp [op] at hy
          cases hy with
          | inl hy => exact h₁.left x hx |>.left.right y hy
          | inr hy =>
            intro hcap
            obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
            simp [hy] at hz
            obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
            have : z < a + m₁ := by apply Nat.lt_of_lt_of_le hz12 <| h₁.left x hx |>.left.left.right.right
            have : ¬ z < a + m₁ := by push_neg; apply Nat.le_trans <| h₂.left y hy |>.left.left.left; exact hz2
            contradiction
        · sorry
      | inr hx =>
        split_ands
        · have h := h₂.left x hx |>.left.left.left; linarith
        · exact h₂.left x hx |>.left.left.right.left
        · apply Nat.le_trans (h₂.left x hx).left.left.right.right; linarith
        · intro y hy
          simp [op] at hy
          cases hy with
          | inl hy =>
            intro hcap
            obtain ⟨z, hz⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hcap
            simp [hy] at hz
            obtain ⟨⟨hz11, hz12⟩, ⟨hz2, hz3⟩⟩ := hz
            have : z < a + m₁ := by apply Nat.lt_of_lt_of_le hz3 <| h₁.left y hy |>.left.left.right.right
            have : ¬ z < a + m₁ := by push_neg; apply Nat.le_trans <| h₂.left x hx |>.left.left.left; exact hz11
            contradiction
          | inr hy => exact h₂.left x hx |>.left.right y hy
        · sorry
    · have : mul f op₁ * mul f op₂ = mul f op := by
        simp [mul, op]
        have : Disjoint op₁ op₂ := by
          refine Finset.disjoint_left.mpr ?_
          intro x hx
          obtain h1 := (h₁.left x hx).left.left.right.left
          obtain h2 := (h₁.left x hx).left.left.right.right
          by_contra hx'
          obtain h3 := (h₂.left x hx').left
          linarith
        rw [Finset.prod_union this]
      rw [<-this]
      exact Nat.mul_dvd_mul h₁.right h₂.right

  --  Generalize the result to the case that m₁ = m₂. Inductively applying the last lemma, we can a new operation in interval
  --  [a, a+mr) such that m^r ∣ mul f op
  have power_op (a m r : ℕ) (hm : m ≥ 2) (hr : r ≥ 1):
      ∃ op : Finset <| ℕ × ℕ, norm_op a (r * m) op ∧ m ^ r ∣ mul f op := by
    induction r with
    | zero => linarith
    | succ k ih =>
      by_cases hk : k = 0
      · rw [hk, zero_add, Nat.pow_one, one_mul]
        exact exists_dvd a m hm
      · have : k ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr hk
        obtain h := mul_op a (k * m) m (m ^ k) m (ih this) (exists_dvd (a + (k * m)) m hm)
        rw [Nat.pow_add_one, add_mul, one_mul]
        exact h

  --  Note that 16! = 2 ^ 15 * 3 ^ 6 * 5 ^ 3 * 7 ^ 2 * 11 * 13 and 15 * 2 + 6 * 3 + 3 * 5 + 2 * 7 + 11 + 13 = 101
  --  Now construction the operations for divisors 2 ^ 15, 3 ^ 6, 5 ^ 3, 7 ^ 2, 11, 13, respectively, in a sequential manner
  --  such that they exactly corespond to the intervals of lenth 15 * 2, 6 *3, ⋯, 11, 13.
  --  Merge them by lemma mul_op to get a new op, which operates interval [0, 101), and 16! ∣ mul f op.
  obtain h₁:= power_op 0 2 15 (show 2 ≥ 2 by decide) (show _ by decide)
  obtain h₂ := power_op (15 * 2) 3 6 (show _ by decide) (show _ by decide)
  obtain h₂ := mul_op 0 (15 * 2) (6 * 3) (2 ^ 15) (3 ^ 6) h₁ h₂
  obtain h₃ := power_op (15 * 2 + 6 * 3) 5 3 (show _ by decide) (show _ by decide)
  obtain h₃ := mul_op 0 (15 * 2 + 6 * 3) (3 * 5) (2 ^ 15 * 3 ^ 6) (5 ^ 3) h₂ h₃
  obtain h₄ := power_op ((15 * 2 + 6 * 3) + 3 * 5) 7 2 (show _ by decide) (show _ by decide)
  obtain h₄ := mul_op 0 ((15 * 2 + 6 * 3) + 3 * 5) (2 * 7) (2 ^ 15 * 3 ^ 6 * 5 ^ 3) (7 ^ 2) h₃ h₄
  obtain h₅ := mul_op 0 ((15 * 2 + 6 * 3) + 3 * 5 + 2 * 7) 11 (2 ^ 15 * 3 ^ 6 * 5 ^ 3 * 7 ^ 2) 11 h₄ (exists_dvd ((15 * 2 + 6 * 3) + 3 * 5 + 2 * 7) 11 (show _ by decide))
  obtain ⟨op, h₆⟩ := mul_op 0 ((15 * 2 + 6 * 3) + 3 * 5 + 2 * 7 + 11) 13 (2 ^ 15 * 3 ^ 6 * 5 ^ 3 * 7 ^ 2 * 11) 13 h₅ (exists_dvd ((15 * 2 + 6 * 3) + 3 * 5 + 2 * 7 + 11) 13 (show _ by decide))
  rw [<-show Nat.factorial 16 = 2 ^ 15 * 3 ^ 6 * 5 ^ 3 * 7 ^ 2 * 11 * 13 by decide, show 15 * 2 + 6 * 3 + 3 * 5 + 2 * 7 + 11 + 13 = 101 by decide] at h₆
  use op
