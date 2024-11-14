import Mathlib

/-
  Given that $y=f(x)$ is an odd function defined on $\mathbb{R}$, $f(-2)=0$,
  and when $x > 0$, $\frac{x{f}^{{'}}(x)-f(x)}{{{x}^{2}}} > 0$, find the solution set for $xf(x) > 0$.
  The final answer is $ \boxed{(-\infty,-2)\cup(2,+\infty)} $
-/
theorem algebra_8987 {f : ℝ → ℝ} (hdif : ∀ x > 0, DifferentiableAt ℝ f x) (hodd : ∀ x, f (-x) = -f x)
    (hf2 : f (-2) = 0) (hfpos : ∀ x > 0, (x * deriv f x - f x) / x ^ 2 > 0) :
    {x | x * f x > 0} = {x | x < -2 ∨ x > 2} := by

  -- definde g(x)=f(x)/x
  let g (x : ℝ) := (f x) / x

  -- f(x) is odd, so f(x)=-f(-x)
  have odd_ext (x : ℝ) : f (- - x) = - f (-x) := by exact hodd <| - x
  simp at odd_ext

  -- g(2)=-f(-2)/2=0
  have zero_point : g 2 = 0 := by
    simp [g]
    rw [odd_ext 2, hf2]
    simp

  -- g(x) is even
  have even_g : ∀ x, g x = g (-x) := by
    intro x
    simp [g]
    rw [hodd x]
    simp

  -- g(0)=0
  have g_at_0 : g 0 = 0 := by simp [g]

  -- g(x) is differentialable at every x ∈ (0,+∞)
  have g_differentiable (x : ℝ) (hx : x > 0) : DifferentiableAt ℝ g x := by
    refine DifferentiableAt.div (hdif x hx) ?hd ?hx
    · exact differentiableAt_id'
    · exact Ne.symm (ne_of_lt hx)

  -- hence, g(x) is continuous on (0,+∞)
  have g_continuous_on : ContinuousOn g (Set.Ioi 0) := by
    apply ContinuousAt.continuousOn
    intro x hx
    exact DifferentiableAt.continuousAt (g_differentiable x hx)

  -- g'(x)>0 on (0,+∞)
  have deriv_pos (x : ℝ) (hx : x > 0): (deriv g) x > 0 := by
    simp [g]
    rw [deriv_div, deriv_id'']
    · simp [mul_comm]; exact hfpos x hx
    · exact hdif x hx
    · exact differentiableAt_id'
    · exact Ne.symm (ne_of_lt hx)

  -- therefore, g' is strict monotone on (0,+∞)
  have strict_on_pos : StrictMonoOn g (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos ?hD ?hf ?hf'
    · exact convex_Ioi 0
    · exact g_continuous_on
    · simp
      exact fun x a ↦ deriv_pos x a

  -- hence, g x >0 ↔ x>2 on (0,+∞)
  have solution_on_pos (x : ℝ) (hx : x > 0) : g x > 0 ↔ x > 2 := by
    constructor
    · intro h
      rw [<-zero_point] at h
      apply (StrictMonoOn.lt_iff_lt strict_on_pos ?_ ?_).mp h
      · simp
      · simp; exact hx
    · intro h
      rw [<-zero_point]
      apply (StrictMonoOn.lt_iff_lt strict_on_pos ?_ ?_).mpr h
      · simp
      · simp; exact hx

  -- since g is even, g x >0 ↔ x<-2 on (-∞, 0)
  have solution_on_neg (x : ℝ) (hx : x < 0) : g x > 0 ↔ x < -2 := by
    have hx : -x > 0 := by exact Left.neg_pos_iff.mpr hx
    have : g x > 0 ↔ -x > 2 := by
      simp [even_g x]
      exact solution_on_pos (-x) hx
    rw [this]
    exact lt_neg

  -- combine two cases g(x)>0 iff x < -2 ∨ x > 2
  have solution_of_g (x : ℝ) : g x > 0 ↔ x < -2 ∨ x > 2 := by
    constructor
    · intro hx
      by_cases h : x > 0
      · apply Or.inr <| (solution_on_pos x h).mp hx
      · by_cases h' : x = 0
        · rw [h', g_at_0] at hx; linarith
        · push_neg at h
          apply Or.inl <| (solution_on_neg x ?_).mp hx
          exact lt_of_le_of_ne h h'
    · intro hx
      cases hx with
      | inl hx =>
        have : x < 0 := by apply lt_trans hx (show -2 < 0 by simp)
        exact solution_on_neg x this |>.mpr hx
      | inr hx =>
        have : x > 0 := by exact lt_trans (show 0 < 2 by simp) hx
        exact solution_on_pos x this |>.mpr hx

  -- xf(x)>0 ↔ g(x)>0, they have the same solutions
  have transform (f : ℝ → ℝ) (x : ℝ): x * f x > 0 ↔ (f x) / x > 0 := by
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hf : f x = 0
      · simp [hf]
      · refine pos_iff_pos_of_smul_pos ?_
        have : (x * f x) • (f x / x) = (f x) ^ 2 := by field_simp; ring
        rw [this]
        exact pow_two_pos_of_ne_zero hf

  -- done
  apply Set.ext
  intro x
  constructor <;> intro hx
  · apply (transform f x).mp at hx
    exact (solution_of_g x).mp hx
  · apply (solution_of_g x).mpr at hx
    exact (transform f x).mpr hx
