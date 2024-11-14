import Mathlib

open Real Nat Set BigOperators

/-Given the function $f(x)=\sqrt{x^2+4}+ax$ is a monotonic function on $\left[0,+\infty \right)$, the range of $a$ is ______.-/

theorem algebra_9032_1 (a:ℝ):
  (MonotoneOn (fun x=>Real.sqrt (x ^ 2 + 4) + x*a) (Ici 0) ↔
  a ≥ 0) := by
  set f:=(fun x=>Real.sqrt (x ^ 2 + 4) + x*a) with f_def
  constructor
  intro fmono
  contrapose! fmono
  simp only [MonotoneOn]
  simp only [mem_Ici, not_forall, Classical.not_imp, not_le]
  by_cases ha:-1< a
  use 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero, add_zero,exists_prop, exists_and_left, and_self_left, le_refl, exists_const,true_and]
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
  rw[f_def,bdef]
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
  simp only [mul_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, zero_mul,
    neg_zero, add_zero, add_neg_lt_iff_lt_add, gt_iff_lt]
  rw[mul_comm]
  apply lt_of_mul_lt_mul_right this
  simp
--a≤-1
  · use 0
    simp only [not_lt] at ha
    simp
    rw[f_def]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
        add_zero]
    use 1
    simp only [zero_le_one, one_pow, mul_one, true_and,one_mul,zero_mul,add_zero]
    calc √(1 + 4) + a ≤ √(1 + 4) -1:=by
          linarith
        _<√4:=by
          norm_num
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
--a≥0
  intro ha x hx y hy hxy
  rw[f_def]
  simp_all only [pow_two, ge_iff_le, mem_Ici, add_le_add_iff_right]
  apply _root_.add_le_add
  apply Real.sqrt_le_sqrt;apply _root_.add_le_add
  apply mul_le_mul;repeat' linarith
  apply mul_le_mul;repeat' linarith
--We finished the monotone part.

theorem algebra_9032_2 (a:ℝ): (AntitoneOn (fun x=>Real.sqrt (x ^ 2 + 4) + x*a) (Ici 0) ↔
  a≤ -1):=by
  set f:=(fun x=>Real.sqrt (x ^ 2 + 4) + x*a) with f_def
  set g:=(fun x=>Real.sqrt (x^2+4)) with g_def
  set g1:=fun (x:ℝ)=>x^2 with g1def
  set g2:=fun (x:ℝ)=>x+4 with g2def
  set g3:=fun (x:ℝ)=>Real.sqrt x with g3def
  have comps:g = g3∘g2∘g1:=by
    rfl
  set h :=fun x=>x*a with h_def
  have gaddh:f=g+h:=by rfl
  have gdiff:Differentiable ℝ g:=by
    simp only [Differentiable]
    intro x
    rw[comps]
    apply DifferentiableAt.comp
    rw[g3def]
    apply DifferentiableAt.sqrt
    simp only [Function.comp_apply, differentiableAt_id']
    rw[g2def,g1def]
    simp only [Function.comp_apply]
    apply _root_.ne_of_gt
    apply add_pos_of_nonneg_of_pos
    apply sq_nonneg
    linarith
    apply Differentiable.comp
    rw[g2def]
    simp only [differentiable_id', differentiable_const, Differentiable.add]
    rw[g1def]
    simp only [differentiable_id', Differentiable.pow]
  have hdiff:Differentiable ℝ h:=by
    have _:Differentiable ℝ (fun x:ℝ=>x):=by
      simp only [differentiable_id']
    apply Differentiable.mul
    simp only [differentiable_id']
    simp only [differentiable_const]
  have fdiff:Differentiable ℝ f:=by
    simp only [Differentiable]
    intro x
    rw[gaddh]
    apply Differentiable.add
    assumption
    assumption
  have derivf (x:ℝ):deriv f x= x/Real.sqrt (x^2+4)+a:=by
    have aux:deriv f x=deriv g x + deriv h x:=by
      rw[gaddh]
      simp_all only [Differentiable, deriv_add, differentiableAt_add_const_iff,
        differentiableAt_id', DifferentiableAt.pow, differentiableAt_const, deriv_mul, deriv_id'',
        one_mul, deriv_const', mul_zero, add_zero, add_right_inj]
      simp only [h]
      simp
    rw[aux]
    have :deriv h x=a:=by
      simp only [h]
      simp
    rw[this];simp;simp only [Differentiable, differentiableAt_add_const_iff, differentiableAt_id',DifferentiableAt.pow] at fdiff gdiff hdiff;rw[comps]
    rw[deriv.comp];rw[deriv.comp]
    rw[g1def,g2def,g3def];simp
    rw[deriv_sqrt]
    simp;field_simp;ring_nf;simp
    apply _root_.ne_of_gt
    apply add_pos_of_nonneg_of_pos
    apply sq_nonneg;linarith
    rw[g2def];simp;rw[g1def];simp;rw[g3def]
    apply DifferentiableAt.sqrt
    simp only [Function.comp_apply, differentiableAt_id']
    rw[g2def,g1def]
    simp only [Function.comp_apply]
    apply _root_.ne_of_gt
    apply add_pos_of_nonneg_of_pos
    apply sq_nonneg;linarith
    apply Differentiable.comp
    rw[g2def];simp;rw[g1def];simp
--Finished results about derivative.
--First, assume it's antitone
  constructor
  intro fanti
  contrapose! fanti
  by_cases ha:0≤ a
  simp only [AntitoneOn]
  simp
  use 0
  simp
  use 1
  simp
  simp only [f]
  simp
  rw[add_comm]
  apply lt_add_of_nonneg_of_lt
  linarith
  norm_num
--We have-1 < a<0 We prove that in this case it has strict monopart.
  simp at ha
  simp only [AntitoneOn]
  simp
  set y:=(2*(-a)/Real.sqrt (1-a^2)) with hy
  set b:=-a with bdef
  have sqab:a^2=b^2:=by rw[bdef];simp only [even_two, Even.neg_pow]
  have hb1:b<1:=by linarith
  have aleone:|a|<1:=by simp only [abs];simp;constructor;linarith;linarith
  have hb2:0< b:=by linarith
  have hbsq:0<1-b^2:=by
      simp only [sub_pos, sq_lt_one_iff_abs_lt_one]
      rw[abs]
      simp only [sup_lt_iff];constructor;linarith;linarith
  have nbdef:a=-b:=by rw[bdef,neg_neg]
  have ypos:0< y:=by
    rw[hy]
    apply div_pos
    linarith
    apply Real.sqrt_pos.mpr
    linarith
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
      rw[sqab,sq_sqrt] at hy
      field_simp at hy
      ring_nf at hy
      ring_nf
      repeat linarith
  have derivzero:deriv f y=0:=by
    rw[derivf]
    rw[hy,sqab,nbdef]
    field_simp
    rw[mul_sub,mul_pow]
    norm_num
    rw[←sub_eq_add_neg,mul_comm,←mul_sub]
    norm_num
    apply Or.inr
    rw[sub_eq_zero]
    have :√4=√(2^2):=by
      norm_num
    rw[this]
    simp only [ofNat_nonneg, sqrt_sq]
  have smonof :StrictMonoOn f (Ici y):=by
    apply strictMonoOn_of_deriv_pos
    apply StrictConvex.convex
    apply strictConvex_Ici
    apply ContinuousAt.continuousOn
    intro x _
    simp only [Differentiable] at fdiff
    apply DifferentiableAt.continuousAt (fdiff x)
    intro x hx
    simp at hx
    have xpos:0<x:=by linarith
    have ynonneg:0≤y:=by linarith
    have xnonneg:0≤x:=by linarith
    rw[←derivzero]
    rw[derivf,derivf]
    simp
    apply (div_lt_div_iff _ _).mpr
    nth_rewrite 1[←mul_self_sqrt ynonneg]
    nth_rewrite 2[←mul_self_sqrt xnonneg]
    rw[←sqrt_mul,←sqrt_mul,←sqrt_mul,←sqrt_mul]
    rw[←pow_two,←pow_two]
    apply sqrt_lt_sqrt
    apply mul_nonneg
    apply sq_nonneg
    apply add_nonneg
    apply sq_nonneg
    linarith
    rw[mul_add,mul_add,mul_comm]
    simp
    apply sq_lt_sq'
    linarith;linarith
    apply mul_self_nonneg
    linarith
    apply mul_self_nonneg
    linarith
    apply sqrt_pos_of_pos
    apply add_pos
    apply pow_pos ypos
    norm_num
    apply sqrt_pos_of_pos
    apply add_pos
    apply pow_pos xpos
    norm_num
  use y
  constructor
  apply mul_nonneg
  linarith
  simp only [inv_nonneg, sqrt_nonneg]
  rw[sqab] at hy
  use y+1
  simp only [StrictMonoOn] at smonof
  constructor;linarith;constructor;linarith
  apply smonof
  simp
  simp
  simp
--We prove the derivative is neg, then the function is strictly antitone.
  intro ha
  have stanti:StrictAntiOn f (Ici 0):=by
    apply strictAntiOn_of_deriv_neg
    apply StrictConvex.convex
    apply strictConvex_Ici
    apply ContinuousAt.continuousOn
    intro x _
    simp only [Differentiable] at fdiff
    apply DifferentiableAt.continuousAt (fdiff x)
    intro x hx
    simp at hx
    rw[derivf]
    rw[←neg_neg a,←sub_eq_add_neg,sub_neg]
    have :1≤-a:=by linarith
    apply lt_of_le_of_lt' this
    rw[div_lt_one]
    rw[lt_sqrt]
    simp
    linarith
    apply sqrt_pos_of_pos
    apply add_pos
    apply sq_pos_of_pos
    repeat linarith
  intro x hx y hy hxy
  by_cases xeqy:x=y
  rw[xeqy]
  apply le_of_lt
  apply stanti hx hy
  apply lt_of_le_of_ne hxy xeqy
