
import Mathlib
import Aesop
open BigOperators Int

/-Find all triples of positive integers  $(x,y,z)$  that satisfy the equation   $$ 2(x+y+z+2xyz)^2=(2xy+2yz+2zx+1)^2+2023. $$  -/

theorem number_theory_8661:
  { (x,y,z):Int×Int×Int | (0<x)∧ (0<y)∧(0<z) ∧(2*(x+y+z+2*x*y*z)^2=(2*x*y+2*y*z+2*x*z+1)^2+2023) }={(3,3,2),(3,2,3),(2,3,3)}:=by
    have nsquare (n:ℕ) (k:ℕ)(hk:k^2<n ∧ n<(k+1)^2): ¬ IsSquare n:=by
      contrapose! hk
      intro h
      rcases hk with ⟨d,hd⟩
      rw[hd,←pow_two];rw[hd,←pow_two] at h
      replace h :k<d:=by
        apply (@Nat.pow_lt_pow_iff_left _ d 2 _).mp h;norm_num
      apply (@Nat.pow_le_pow_iff_left _ d 2 _).mpr
      repeat' linarith
    have sym1 (x y z: Int):(2*(x+y+z+2*x*y*z)^2=(2*x*y+2*y*z+2*x*z+1)^2+2023) ↔(2*(y+z+x+2*y*z*x)^2=(2*y*z+2*z*x+2*y*x+1)^2+2023):=by ring_nf
    have sym2 (x y z: Int):(2*(x+y+z+2*x*y*z)^2=(2*x*y+2*y*z+2*x*z+1)^2+2023) ↔(2*(y+x+z+2*y*x*z)^2=(2*y*x+2*x*z+2*y*z+1)^2+2023):=by ring_nf
    have gonef (y:Int)(ypos:0<y):1≤ (y^2*2-1):=by
      ring_nf
      simp only [reduceNeg, le_neg_add_iff_add_le, reduceAdd, Nat.ofNat_pos, le_mul_iff_one_le_left,
        one_le_sq_iff_one_le_abs]
      apply Int.one_le_abs
      linarith

    have main_lemma (x y z:Int) (xpos:0<x)(ypos:0<y)(zpos:0<z)(heq:(2*(x+y+z+2*x*y*z)^2=(2*x*y+2*y*z+2*x*z+1)^2+2023)):x≤ y->x≤z→ x=2∧y=3∧z=3:=by
      intro xley xlez
      have xlt3:x<3:=by
        have fac: (2023:ℤ) < 63^2:=by norm_num
        have fac0 (a b c:Int) (ha:3 ≤ a)(hb:3 ≤ b)(hc:3 ≤ c):63≤(a+b+c+2*a*b*c):=by
            have t2:3*3*3≤a*b*c:=by
              repeat' (apply mul_le_mul;repeat' linarith)
              apply mul_nonneg
              linarith;linarith
            rw[two_mul,add_mul,add_mul]
            linarith
        contrapose! heq
        have fac1 (a b c:Int) (ha:3 ≤ a)(hb:3 ≤ b)(hc:3 ≤ c):2023<(a+b+c+2*a*b*c)^2:=by
          apply Int.lt_of_lt_of_le fac
          have fac':9≤a+b+c∧ 3*3*3≤a*b*c:=by
            constructor;linarith
            repeat' (apply mul_le_mul;repeat' linarith)
            apply mul_nonneg
            linarith;linarith
          have :63≤a+b+c+a*b*c*2:=by linarith
          rw[pow_two,pow_two]
          apply Int.mul_le_mul
          linarith;linarith;linarith;linarith
        have fac2 (k y z:Int):k * y +y+ y * z + (k * z + z)=(k * y  + y * z + k * z)+ (z+ y):=by ring
        apply ne_of_gt
        rw[two_mul ((x + y + z + 2*x* y * z) ^ 2)]
        apply add_lt_add
        rw[pow_two,pow_two]
        apply Int.mul_lt_mul
        rw[add_comm]
        apply add_lt_add_of_lt_of_le
        linarith
        rw[mul_assoc,mul_assoc,mul_assoc,←mul_add,←mul_add,mul_assoc,_root_.mul_le_mul_left]
        have t3:y*z+y*z+y*z≤x*y*z:=by
          ring_nf
          apply Int.mul_le_mul
          apply Int.mul_le_mul;repeat' linarith;
          apply mul_nonneg;linarith;linarith
        apply le_trans' t3
        apply Int.add_le_add
        apply Int.add_le_add
        rw[mul_comm]
        repeat' (apply Int.mul_le_mul;repeat' linarith)
        linarith;rw[add_comm];apply add_le_add;linarith
        ring_nf;rw[←add_mul,←add_mul];simp only [Nat.ofNat_pos, mul_le_mul_right]
        have :y*z+y*z+y*z ≤ x * y * z:=by
          ring_nf
          apply Int.mul_le_mul;apply Int.mul_le_mul
          repeat' linarith
          apply mul_nonneg;linarith;linarith
        apply le_trans' this
        simp_all only [reducePow, reduceLT, add_le_add_iff_right]
        apply add_le_add
        rw[mul_comm]
        simp_all only [mul_le_mul_left]
        simp_all only [mul_le_mul_right]
        repeat apply add_pos
        repeat' (apply mul_pos;repeat' linarith)
        linarith;apply add_nonneg;linarith
        repeat' apply mul_nonneg
        repeat' linarith
        apply fac1
        repeat' linarith
      replace heq:x^2 + y^2 + z^2 + x^2*y^2*z^2*2*2=1012+(x^2*y^2 + y^2*z^2 + x^2*z^2)*2:=by linarith

      set a:=y^2*2-1 with a_def
      interval_cases x
--x=1 case
      field_simp at heq
      replace heq:(y^2*2-1)*(z^2*2-1)=2023:=by linarith
      have advd2023:a∣2023:=by  use (z^2*2-1);rw[heq]
      have aindiv:a.natAbs ∈ Nat.divisors 2023 :=by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        apply Int.ofNat_dvd.mp
        simp only [natCast_natAbs, Nat.cast_ofNat, abs_dvd,advd2023]
      have aeq:a=Int.ofNat (a.natAbs):=by
        simp only [ofNat_eq_coe, natCast_natAbs]
        rw[abs_of_nonneg]
        apply le_of_lt
        apply Order.one_le_iff_pos.mp
        apply gonef
        linarith
      simp only [ofNat_eq_coe] at aeq
      have dv2023:Nat.divisors 2023={1, 7, 17, 119, 289, 2023}:=by native_decide
      rw[dv2023] at aindiv
      simp only [Finset.mem_insert, Finset.mem_singleton] at aindiv
      rcases aindiv with aval|aval|aval|aval|aval|aval
--a=1 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[←a_def,aeq] at heq
        replace heq :z^2=1012:=by linarith
        have :IsSquare 1012:=by use z.natAbs;rw[←pow_two];apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
        have nsq1012:¬ IsSquare 1012:=by
          apply nsquare 1012 31
          simp only [Nat.reducePow, Nat.reduceLT, Nat.reduceAdd, and_self]
        exfalso;exact nsq1012 this
--a=7 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[←a_def,aeq] at heq
        replace heq:z^2*2-1=289:=by
          have :(2023:ℤ)=7*289:=by ring
          rw[this] at heq
          field_simp at heq
          exact heq
        have :IsSquare 145:=by
          use z.natAbs;rw[←pow_two]
          apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
          linarith
        have nsq145:¬ IsSquare 145:=by
          apply nsquare 145 12;constructor;repeat' linarith
        exfalso;exact nsq145 this
--a=17 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[←a_def,aeq] at heq
        replace heq:z^2*2-1=119:=by
          have :(2023:ℤ)=17*119:=by ring
          rw[this] at heq
          field_simp at heq
          exact heq
        have :IsSquare 60:=by
          use z.natAbs;rw[←pow_two]
          apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
          linarith
        have nsq60:¬ IsSquare 60:=by
          apply nsquare 60 7;constructor;repeat' linarith
        exfalso;exact nsq60 this
--a=119 case
      · rw[aval,a_def] at aeq
        replace aeq:y^2=60:=by simp only [Nat.cast_ofNat] at aeq;linarith
        have :IsSquare 60:=by
          use y.natAbs;rw[←pow_two]
          apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
          linarith
        have nsq60:¬ IsSquare 60:=by apply nsquare 60 7;constructor;repeat' linarith
        exfalso;exact nsq60 this
--a=289 case
      · rw[aval,a_def] at aeq
        replace aeq:y^2=145:=by simp only [Nat.cast_ofNat] at aeq;linarith
        have :IsSquare 145:=by
          use y.natAbs;rw[←pow_two]
          apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
          linarith
        have nsq145:¬ IsSquare 145:=by apply nsquare 145 12;constructor;repeat' linarith
        exfalso;exact nsq145 this
--a=2023 case
      · rw[aval,a_def] at aeq
        replace aeq:y^2=1012:=by simp only [Nat.cast_ofNat] at aeq;linarith
        have :IsSquare 1012:=by
          use y.natAbs;rw[←pow_two]
          apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
          linarith
        have nsq1012:¬ IsSquare 1012:=by apply nsquare 1012 31;constructor;repeat' linarith
        exfalso;exact nsq1012 this
--x=2 case
      ring_nf at heq
      replace heq:(y^2*2-1)*(z^2*2-1)=289:=by linarith
      have advd289:a∣289:=by use (z^2*2-1);rw[heq]
      have aindiv:a.natAbs ∈ Nat.divisors 289 :=by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        apply Int.ofNat_dvd.mp
        simp only [natCast_natAbs, Nat.cast_ofNat, abs_dvd,advd289]
      have aeq:a=Int.ofNat (a.natAbs):=by
        simp only [ofNat_eq_coe, natCast_natAbs]
        rw[abs_of_nonneg]
        apply le_of_lt
        apply gonef
        exact ypos
      have div289:Nat.divisors 289={1,17,289}:=by
        native_decide
      rw[div289] at aindiv
      simp only [ofNat_eq_coe] at aeq
      simp only [Finset.mem_insert, Finset.mem_singleton] at aindiv
      rcases aindiv with aval|aval|aval
--a=1 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[←a_def,aeq] at heq
        replace heq :z^2=145:=by linarith
        have :IsSquare 145:=by use z.natAbs;rw[←pow_two];apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,heq]
        have nsq145:¬ IsSquare 145:=by
          apply nsquare 145 12
          simp only [Nat.reducePow, Nat.reduceLT, Nat.reduceAdd, and_self]
        exfalso;exact nsq145 this
--a=17 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[←a_def,aeq] at heq
        replace aeq:y=3:=by
          simp only [Nat.cast_ofNat] at aeq
          replace aeq :y^2=3^2:=by linarith
          rw[←Int.natAbs_eq_iff_sq_eq,←Int.natCast_inj,Int.natAbs_of_nonneg] at aeq
          rw[aeq]
          simp only [reduceAbs, Nat.cast_ofNat];linarith
        replace heq:z=3:=by
          replace heq :z^2=3^2:=by simp only [Nat.cast_ofNat] at heq;linarith
          simp only [Nat.cast_ofNat] at heq
          rw[←Int.natAbs_eq_iff_sq_eq,←Int.natCast_inj,Int.natAbs_of_nonneg] at heq
          rw[heq]
          simp only [reduceAbs, Nat.cast_ofNat];linarith
        rw[aeq,heq]
        simp only [and_self]
--a=289 case
      · simp only [aval,Nat.cast_one] at aeq
        rw[aeq] at a_def
        replace a_def:y^2=145:=by simp only [Nat.cast_ofNat] at a_def; linarith
        have :IsSquare 145:=by use y.natAbs;rw[←pow_two];apply Int.natCast_inj.mp;simp only [Nat.cast_ofNat, Nat.cast_pow, natCast_natAbs, sq_abs,a_def]
        have nsq145:¬ IsSquare 145:=by
          apply nsquare 145 12;constructor;repeat' linarith
        exfalso;exact nsq145 this
--Main lemma ends here.
    ext ⟨x,y,z⟩
    simp
--We first prove the right hand side implies the left hand side.
    symm
    constructor
    · intro h;rcases h with ⟨hx,hy,hz⟩|⟨hx,hy,hz⟩|⟨hx,hy,hz⟩
      repeat' rw[hx,hy,hz];simp
--We prove by play with the cases
    · rintro ⟨xpos,ypos,zpos,heq⟩
      by_cases xry:x≤y
      by_cases xrz:x≤z
--x≤y,x≤z
      apply Or.inr;apply Or.inr
      apply main_lemma
      repeat' linarith
--z≤x,x≤y
      apply Or.inl;
      rw[←and_assoc,and_comm]
      apply main_lemma
      rw[sym1]
      exact heq;repeat' linarith
      by_cases yrz:y≤z
--y≤z,y≤x
      apply Or.inr;apply Or.inl
      rw[and_comm,and_assoc]
      apply main_lemma
      rw[sym1,sym1]
      exact heq;repeat' linarith
--z≤x,z≤y
      simp only [not_le] at xry yrz
      apply Or.inl
      rw[←and_assoc,and_comm]
      apply main_lemma
      rw[sym1]
      exact heq
      apply le_of_lt
      apply lt_trans yrz xry
      apply le_of_lt yrz
      exact zpos;exact xpos;exact ypos
