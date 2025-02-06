import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- # NOT EVERY NUMBER IS RATIONAL

  Suppose √2 : ℚ

  Then there exists m n : ℕ such that (m/n)^2 = 2

  We can assume that m/n is reduced, so gcd m n = 1

  Rewrite the above as m m = 2 n n

  Then we know that m is a multiple of 2 since m*m is a multiple of 2

  So rewrite m = 2k for some k

  So 4 k k = 2 n n
     2 k k = n n

  So n is a multiple of 2.

  Put n = 2j for some j

  So gcd m n = gcd (2k) (2j) ≥ 2

  But gcd m n = 1

  Contradiction!

-/


/- # WHAT THEOREMS AND TACTICS ARE AVAILABLE? -/

/- Greatest common denominators -/
#eval Nat.gcd 12 14
#check Nat.dvd_gcd
#eval (15:Nat).Coprime 12

/- The divides relationship -/
#eval 12 ∣ 13                        -- \|
#check dvd_mul_right
def h : 2∣12 := by exact (Nat.minFac_eq_two_iff 12).mp rfl
#check dvd_iff_exists_eq_mul_left.mp h
#check Prime.dvd_of_dvd_pow
#check Nat.le_of_dvd (Nat.zero_lt_succ 11) h

/- Useful tactics -/
#help tactic ring
#help tactic convert
#help tactic symm


/- Minimum size of a prime number-/
#check Nat.Prime.two_le
#check trans

/- Other-/
#check zero_lt_one





/- # A PROOF FROM FROM MIL 5.1 -/

theorem prime_not_rat (p: ℕ) {m n: ℕ}
  (coprime_mn : m.Coprime n)
  (prime_p : p.Prime)
  : m ^ 2 ≠ p * n ^ 2 := by

  intro sqr_eq

  -- m is a multiple of p
  have : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right

  have ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this  -- use the previous declaration
                                                       -- without naming it!
  -- n is a multiple of p
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring

  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp this
    exact prime_p.ne_zero

  have : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right

  -- gcd m n is a multiple of p
  have : p ∣ Nat.gcd m n := by apply Nat.dvd_gcd <;> assumption

  -- 1 is a multiple of p
  have : p ∣ 1 := by
    convert this
    symm
    exact coprime_mn

  -- p is less than or equal to 1 since it is a divisor of 1
  have p_le_1 : p ≤ 1 := Nat.le_of_dvd zero_lt_one this

  -- since 2 ≤ p and p ≤ 1, we get 2 ≤ 1
  have : 2 ≤ 1 := by
    have : 2 ≤ p := prime_p.two_le
    exact (trans this) p_le_1

  -- Find the contradiction
  simp at this





example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro h
  exact prime_not_rat 2 coprime_mn (Nat.prime_two) h

theorem root_2_irrat : ¬ ∃ x : Rat, x^2 = 2 := by
  intro ⟨ x, h ⟩
  sorry
