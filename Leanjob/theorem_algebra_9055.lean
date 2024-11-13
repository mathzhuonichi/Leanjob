import Mathlib

/-Given that the vertex of a parabola is at the origin and the focus is at $\left(0,2\right)$, the standard equation of the parabola is ______.-/


theorem algebra_9055 (p: ℝ) (hp:p/2=2): {(x,y) : ℝ × ℝ | x^2=2*p*y }={(x,y) : ℝ × ℝ | x^2=8*y }:=by
  field_simp at hp;rw[hp];norm_num

--The final answer is \boxed{x^2 = 8y}
