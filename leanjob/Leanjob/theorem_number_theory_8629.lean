import Mathlib
import Aesop

/- Let  $N$  be the number if pairs of integers  $(m,n)$  that satisfies the equation  $m^2+n^2=m^3$ Is  $N$  finite or infinite?If  $N$  is finite,what is its value?-/
theorem number_theory_8629 :Set.Infinite {(m,n):ℤ×ℤ| m^2+n^2=m^3}:=by
--We prove that the first coordinate have infinite image
  apply Set.Infinite.of_image fun p=>p.fst
--We prove that the image is not bounded above.
  apply Set.infinite_of_forall_exists_gt
  intro x
  use x^2+1
  simp;constructor;use (x^2+1)*x;ring_nf
  apply lt_of_le_of_lt (Int.le_self_sq x);simp
