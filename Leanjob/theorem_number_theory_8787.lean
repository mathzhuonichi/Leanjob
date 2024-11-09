import Mathlib
import Aesop



open BigOperators Real Nat Topology Rat Int



-- Let  $x$  and  $y$  be relatively prime integers. Show that  $x^2+xy+y^2$  and  $x^2+3xy+y^2$  are relatively prime.

theorem number_theory_8787 (x y : ℤ) (h₀ : IsCoprime x y) :
IsCoprime (x^2 + x * y + y^2) (x^2 + 3 * x * y + y^2) := by
--We replace one side by a product form, so it will be easier to handle.
  have aux:(x ^ 2 + 3 * x * y + y ^ 2)= 2*x*y+(x^2 +x*y+y^2)*1:=by ring
  rw[aux]
  apply IsCoprime.add_mul_left_right
--We prove the coprime property by multiplicity formula.
  apply IsCoprime.mul_right
  apply IsCoprime.mul_right
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  apply Nat.isCoprime_iff_coprime.mp
  apply Nat.isCoprime_iff_coprime.mpr
  simp only [reduceAbs, Nat.cast_ofNat]
  apply Odd.coprime_two_right
  apply Odd.natAbs
--We consider the parity of this sum case by case.
  by_cases evenx:Even x
  · have oddy:Odd y:=by--The only case which is not that trivial
      contrapose! h₀;simp at h₀
      rcases evenx with ⟨r,hr⟩;rcases h₀ with ⟨s,hs⟩
      rw[hr,hs];ring_nf;
      rw[Int.isCoprime_iff_gcd_eq_one,Int.gcd,Int.natAbs_mul,Int.natAbs_mul];norm_num;rw[Nat.gcd_mul_right];norm_num
    rw[Even] at evenx;rcases evenx with ⟨r,hr⟩;
    rw[Odd] at oddy;rcases oddy with ⟨s,hs⟩;
    rw[hr,hs];ring_nf;rw[Odd]
--We prove the parity by explicitly computation which is easy for computer.
    use r  + r * s * 2 + r ^ 2 * 2 + s * 2 + s ^ 2 * 2
    ring_nf
  · by_cases eveny:Even y
    simp at evenx;rw[Even] at eveny;rw[Odd] at evenx;
    rcases evenx with ⟨r,hr⟩;rcases eveny with ⟨s,hs⟩;
    rw[hr,hs];ring_nf;rw[Odd]
    use r * 2 + r * s * 2 + r ^ 2 * 2 + s  + s ^ 2 * 2;ring_nf
    · simp at evenx eveny;rw[Odd] at evenx eveny;
      rcases evenx with ⟨r,hr⟩;rcases eveny with ⟨s,hs⟩
      rw[hr,hs,Odd];ring_nf
      use 1 + r * 3 + r * s * 2 + r ^ 2 * 2 + s * 3 + s ^ 2 * 2
      ring_nf
  rw[pow_two x,←mul_add]
  apply IsCoprime.mul_add_left_left (IsCoprime.pow_left (IsCoprime.symm h₀))
  rw[add_assoc,pow_two y,←add_mul x y y]
  apply IsCoprime.add_mul_right_left (IsCoprime.pow_left h₀)
