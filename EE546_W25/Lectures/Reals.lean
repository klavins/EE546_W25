import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
--import Mathlib.Algebra.Order.Floor

/- # SEQUENCES -/

def σ₁ (n : ℕ) : ℚ := (1:ℚ) / n
#eval [σ₁ 0, σ₁ 1, σ₁ 2, σ₁ 3]

#check σ₁

def add (a b : ℕ → ℚ) := λ n => a n + b n
def mul (a b : ℕ → ℚ) := λ n => (a n)*(b n)

def σ₂ := add σ₁ (mul σ₁ σ₁)

#eval [σ₂ 0, σ₂ 1, σ₂ 2, σ₂ 3]






/- # CAUCHY SEQUENCES -/

def IsCauchy (σ : ℕ → ℚ) := ∀ ε > 0 , ∃ N : ℕ , ∀ n m,
  n > N ∧ m > N → abs (σ n - σ m) < ε

example : IsCauchy σ₁ := by
  intro ε hε
  let N := Int.toNat (Rat.ceil (1/ε))
  apply Exists.intro N
  intro n m ⟨ h1, h2 ⟩
  simp[σ₁]
  simp[abs_lt]
  exact ⟨
    sorry,
    sorry
  ⟩























theorem helper {n m N1 N2 : Nat} :
  (n > N1 + N2) →
  (m > N1 + N2) →
  (n > N1 ∧ m > N1) ∧ (n > N2 ∧ m > N2) := by
  intro h1 h2
  exact ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩

theorem cauchy_add (s1 s2 : ℕ → ℚ) : IsCauchy s1 → IsCauchy s2 → IsCauchy (add s1 s2) := by

  -- Introduce everything
  intro h1 h2 ε hε
  have ⟨ N1, h1' ⟩ := h1 (ε/2) (by exact half_pos hε)
  have ⟨ N2, h2' ⟩ := h2 (ε/2) (by exact half_pos hε)
  let N := N1 + N2
  apply Exists.intro N
  intro m n ⟨ gm, gn ⟩

  -- Dispatch assumptions in the hypotheses
  have h1'' := h1' n m (helper gn gm).left
  have h2'' := h2' n m (helper gn gm).right

  -- Break the add up
  simp[add]

  -- Split up the absolute values
  have ⟨ f1, f2 ⟩ := abs_lt.mp h1''
  have ⟨ f3, f4 ⟩ := abs_lt.mp h2''
  simp[abs_lt]

  -- The rest is arithmetic
  apply And.intro
  . linarith
  . linarith

#check abs_add

theorem cauchy_mul (s1 s2 : ℕ → ℚ) : IsCauchy s1 → IsCauchy s2 → IsCauchy (mul s1 s2) := by
