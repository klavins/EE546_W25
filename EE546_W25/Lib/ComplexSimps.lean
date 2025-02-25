import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Complex.Basic

open Complex

#check (starRingEnd ℂ) (2 + I) -- wtaf?

def Complex.conj (z:ℂ) := z.re - z.im * I

theorem im_gt_to_sum_gt {x y: ℂ} : x.im > 0 → y.im > 0 → (x + y).im > 0 := by
  intro hx hy
  field_simp; exact Right.add_pos' hx hy

@[simp]
theorem int_im_zero (a:ℤ) : im a = 0 := by
  simp [ofReal, Int.cast]

@[simp]
theorem complex_distr (a:ℂ) (b c:ℝ)
  : a * mk b c = a*b + a*c*I := by
  have h : ({ re := b, im := c } : Complex) = b + c*I :=
    mk_eq_add_mul_I b c
  simp[h]
  ring

@[simp]
theorem re_eq_zero_iff {z:ℂ} : z = 0 → z.re = 0 := by
  intro h
  exact (AddSemiconjBy.eq_zero_iff (re 0)
        (congrFun (congrArg HAdd.hAdd (congrArg re (id (Eq.symm h))))
        (re 0))).mp rfl

@[simp]
theorem im_eq_zero_iff {z:ℂ} : z = 0 → z.im = 0 := by
  intro h
  exact (AddSemiconjBy.eq_zero_iff (im 0)
        (congrFun (congrArg HAdd.hAdd (congrArg im (id (Eq.symm h))))
        (im 0))).mp rfl

@[simp]
theorem re_im_eq_zero_iff {z:ℂ} : z = 0 ↔ z.re = 0 ∧ z.im = 0 := by
  apply Iff.intro
  . intro h
    exact ⟨ re_eq_zero_iff h, im_eq_zero_iff h ⟩
  . intro ⟨ hr, hi ⟩
    exact Eq.symm (ext (id (Eq.symm hr)) (id (Eq.symm hi)))

@[simp]
theorem c_mul_div_arrange (a b c d : ℂ): (a/b)*c/d = (a*c)/(b*d) := by field_simp

theorem z_zconj_mul (z:ℂ) : z*z.conj = z.re^2 + z.im^2 := by
  calc z*z.conj
  _  = (z.re + z.im*I)*(z.re - z.im*I) := by simp[conj]
  _  = z.re*z.re - z.im*z.im*I*I := by ring
  _  = z.re*z.re - z.im*z.im*(I*I) := by ring
  _  = z.re*z.re - z.im*z.im*(-1) := by rw[I_mul_I]
  _  = z.re^2 + z.im^2 := by ring

theorem z_zconj_add (z:ℂ) : z + z.conj = 2 * z.re := by
  calc z + z.conj
  _  = z.re + z.im * I + z.re - z.im * I := by simp[conj]; ring
  _  = 2 * z.re := by ring

theorem mul_by_conj_plus {c d z: ℂ}
  : (c*z.conj + d)*(c*z + d) = (c*z.re + d)^2 + (c*z.im)^2 := by
  calc (c*z.conj + d)*(c*z + d)
  _  = c^2*(z*z.conj) + c*z*d + d*c*z.conj + d*d := by ring
  _  = c^2*(z.re^2+z.im^2) + c*z*d + d*c*z.conj + d*d := by rw[z_zconj_mul]
  _  = c^2*(z.re^2+z.im^2) + c*d*(z + z.conj) + d*d := by ring
  _  = c^2*(z.re^2+z.im^2) + c*d*(2*z.re) + d*d := by rw[z_zconj_add]
  _  = (c*z.re + d)^2 + (c*z.im)^2  := by ring

theorem lift_both_sides {a b:ℤ} : a = b ↔ (a:Complex) = (b:Complex) := by
  exact Iff.symm Int.cast_inj

theorem im_of_sum (a b: ℂ) : (a+b).im = a.im + b.im := by rfl

theorem dstrib_im (a b: ℂ): (a+b).im = a.im + b.im := by
  exact rfl

theorem distrib_im_frac (a b c: ℂ): ((a+b)/c).im = (a/c).im  + (b/c).im := by
  ring_nf
  exact rfl

theorem im_zero_of_sq (a : ℂ) : a.im = 0 → (a^2).im = 0 := by
  intro ha
  have : a = a.re := by exact ext rfl ha
  rw[this,pow_two]
  simp

theorem re_of_sq ( a: ℂ ) : a.im = 0 → (a^2).re = a.re * a.re := by
  intro hai
  have : a = a.re := by exact ext rfl hai
  rw[this,pow_two]
  simp

theorem z_norm_im_zero (z : ℂ) : (((z.re ^ 2):Complex).im + ((z.im ^ 2):Complex).im) = 0 := by
  simp[im_zero_of_sq]

/- A key observation is that multiplying a linear combination of z with a linear combination of the conjugate of z can be split up into real and imaginare parts that are positive as long as $ad-bc$ is positive. -/

--theorem split_helper (a b c d z : ℂ): (c*z.conj + d)*(a * z + b) = a*c*(z.re^2+z.im^2) + (b*c+a*d)*z.re + b*d + (a*d-b*c) * Complex.I := by sorry

theorem im_of_frac1 (a b : ℂ) :  a.im = 0 → b.im = 0 → (a/b).im = 0 := by
  intro ha hb
  have ha1 : a = a.re := by exact ext rfl ha
  have hb1 : b = b.re := by exact ext rfl hb
  rw[ha1,hb1]
  simp

theorem im_of_frac2 (a b: ℂ) : b.im = 0 → 0 < b.re → 0 < a.im → 0 < (a/b).im := by
  intro hbi hbr hai
  have hb1 : b = b.re := by exact ext rfl hbi
  rw[hb1]
  simp
  exact div_pos hai hbr

theorem split_helper (a b c d z : ℂ)
   : (c*z.conj + d)*(a * z + b)
   = a*c*(z.re^2+z.im^2) + (b*c+a*d)*z.re + b*d + (a*d-b*c) * z.im * I := by

   calc (c*z.conj + d)*(a * z + b)
   _  = c*z.conj*a*z + c*z.conj*b + d*a*z + d*b := by ring
   _  = a*c*(z*z.conj) + c*z.conj*b + d*a*z + b*d := by ring
   _  = a*c*(z.re^2+z.im^2) + c*z.conj*b + d*a*z + b*d := by rw[z_zconj_mul]
   _  = a*c*(z.re^2+z.im^2) + c*(z.re-z.im*I)*b + d*a*(z.re+z.im*I) + b*d := by simp[conj]
   _  = a*c*(z.re^2+z.im^2) + c*b*z.re - c*b*z.im*I + d*a*z.re+d*a*z.im*I + b*d := by ring
   _  = a*c*(z.re^2+z.im^2) + (b*c+a*d)*z.re + b*d + (a*d-b*c)*z.im*I := by ring
