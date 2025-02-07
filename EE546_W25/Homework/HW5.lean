import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 1) Prove the theorem `cauchy_mul` stated below. It will be easier if you use the fact that all Cauchy sequences are bounded.

def IsCauchy (σ : ℕ → ℚ) :=
  ∀ ε > 0 , ∃ N : ℕ , ∀ n m : ℕ,
  n > N → m > N → abs (σ n - σ m) < ε

def mul (a b : ℕ → ℚ) := λ n => (a n)*(b n)

-- 1a) Optional : Prove Cauchy sequences are bounded
theorem cauchy_bounded {σ : ℕ → ℚ}
 : IsCauchy σ → ∃ b, ∀ n, |σ n| < b :=
 sorry

-- 1b) Prove the product of Cauchy sequences is Cauchy
theorem cauchy_mul (s1 s2 : ℕ → ℚ) :
  IsCauchy s1 →
  IsCauchy s2 →
  IsCauchy (mul s1 s2) := by
    sorry

-- 2) Baby Step: With your group, prepare a short presentation using VSCode only (as with the lecture style) describing a basic result for your project. This could the use of a particular type that you are learning to us (such as matricies), an example application of theorem from Mathlib, or similar. Approximately 100 -200 lines of code will suffice. These presenations will be on Thursday Feb 13.
