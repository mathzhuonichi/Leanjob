import Mathlib

open Real Nat Set BigOperators

/-Given the function $f(x)=\sqrt{x^2+4}+ax$ is a monotonic function on $\left[0,+\infty \right)$, the range of $a$ is ______.-/

theorem algebra_9032_1 (a : ℝ) :
  MonotoneOn (λ x => Real.sqrt (x ^ 2 + 4) + a * x) (Ici 0) ↔
  a ≥ 0 := by
  set f:=(λ x => Real.sqrt (x ^ 2 + 4) + a * x) with fdef
  constructor
  pick_goal 2
  intro ha x hx y hy hxy
  rw[fdef]
  simp_all only [pow_two, ge_iff_le, mem_Ici, add_le_add_iff_right]
  apply _root_.add_le_add
  apply Real.sqrt_le_sqrt;apply _root_.add_le_add
  apply mul_le_mul;repeat' linarith
  apply mul_le_mul;repeat' linarith
  · intro fmono
    contrapose! fmono
    simp only [MonotoneOn]
    simp only [mem_Ici, not_forall, Classical.not_imp, not_le]
    by_cases ha:-1< a
    use 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero, add_zero,
    exists_prop, exists_and_left, and_self_left, le_refl, exists_const,true_and]
    set y:=(2*(-a)/Real.sqrt (1-a^2)) with hy
    use y
    constructor
    apply mul_nonneg
    linarith
    simp only [inv_nonneg, sqrt_nonneg]
    set b:=-a with bdef
    have sqab:a^2=b^2:=by rw[bdef];simp only [even_two, Even.neg_pow]
    have hb1:b<1:=by linarith
    have hb2:0< b:=by linarith
    have hbsq:0<1-b^2:=by
      simp only [sub_pos, sq_lt_one_iff_abs_lt_one]
      rw[abs]
      simp only [sup_lt_iff];constructor;linarith;linarith
    rw[sqab] at hy
    have ypos:0< y:=by
      rw[hy]
      apply div_pos
      linarith
      apply sqrt_pos.mpr hbsq
    have aux:0≤y /Real.sqrt (y^2+4):=by
      apply div_nonneg
      rw[hy]
      apply div_nonneg
      linarith
      simp only [sqrt_nonneg]
      simp only [sqrt_nonneg]
    have hb:b= y /Real.sqrt (y^2+4):=by
      rw[←sq_eq_sq]
      field_simp
      rw[←sq_eq_sq] at hy
      field_simp at hy
      rw[mul_sub,mul_pow 2 b 2,mul_one,sub_eq_iff_eq_add] at hy
      nth_rewrite 2[hy]
      ring_nf
      repeat linarith
    replace bdef:a=-b:=by rw[bdef,neg_neg]
    rw[fdef,bdef]
    rw[hb]
    simp only [neg_mul, add_neg_lt_iff_lt_add, gt_iff_lt]
    have :√(y ^ 2 + 4) *√(y ^ 2 + 4)< (√4 + y / √(y ^ 2 + 4) * y)*√(y ^ 2 + 4):=by
      field_simp
      rw[←pow_two]
      rw[add_comm]
      simp
      have :4=√4*√4:=by simp only [Nat.ofNat_nonneg, mul_self_sqrt]
      nth_rewrite 1[this]
      apply mul_lt_mul'
      linarith
      simp
      apply pow_two_pos_of_ne_zero
      linarith
      simp only [sqrt_nonneg]
      simp only [Real.sqrt_pos, Nat.ofNat_pos]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
      neg_zero, add_zero, gt_iff_lt]
    apply lt_of_mul_lt_mul_right this
    simp only [sqrt_nonneg]
--a≤-1
    · use 0
      simp only [exists_prop, exists_and_left, and_self_left, le_refl, exists_const,true_and]
      simp only [not_lt] at ha
      rw[fdef]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
        add_zero]
      use 1
      simp only [zero_le_one, one_pow, mul_one, true_and]
      calc √(1 + 4) + a ≤ √(1 + 4) -1:=by linarith
        _<√4:=by
          rw[sub_lt_iff_lt_add]
          have :√4=2:=by
            have :(4:ℝ)=2^2:=by
              norm_num
            rw[this]
            simp only [ofNat_nonneg, sqrt_sq]
          rw[this]
          simp_all only [gt_iff_lt]
          norm_num
          rw[Real.sqrt_lt]
          repeat' linarith

theorem algebra_9032_2 (a : ℝ) :
  AntitoneOn (λ x => Real.sqrt (x ^ 2 + 4) + a * x) (Ici 0) ↔
  a≤-1 := by
  set f:=(λ x => Real.sqrt (x ^ 2 + 4) + a * x) with fdef
  constructor
  intro fantitone
  contrapose! fantitone
  simp only [AntitoneOn]
  simp only [mem_Ici, not_forall, Classical.not_imp,fdef, not_le]
  by_cases ha:a<0
  have absale:|a|<1:=by
    rw[abs];simp only [sup_lt_iff];constructor;linarith;linarith
  pick_goal 2
  simp_all
  use 0
  simp only [le_refl, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
    add_zero, and_self_left, true_and]
  use 1
  simp
  calc √4 < √(1 + 4) :=by
        norm_num
    _ ≤√(1 + 4)+a:=by linarith

  set x:=2/Real.sqrt (1-a^2) with hx
  use x
  simp only [exists_prop, exists_and_left]
  have xpos:0<x:=by
    rw[hx]
    apply div_pos
    linarith
    apply Real.sqrt_pos.mpr
    rw[sub_pos,←neg_sq,pow_two,← one_mul 1]
    apply mul_lt_mul
    repeat linarith
  constructor

--Given a ≤ -1



  sorry
