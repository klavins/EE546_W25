import Mathlib.Data.Nat.Prime.Defs

-- 4
example : False → False := λ h => h
example : False → True := λ _ => True.intro
example : True → True := λ h => h

-- 5
theorem tpc : ∀ n, ∃ m, Nat.Prime n ∧ Nat.Prime m ∧ m > n ∧ Nat.Prime (m+2) := sorry

-- Note, many people wrote something like the following, which does not capture the "infinite" part of the conjecture. It just says there exist two primes that differ by 2, which can be proved by choosing, for example, 3 and 5.

theorem not_tpc : ∃ n, Nat.Prime n ∧ Nat.Prime (n+2) := by
  apply Exists.intro 3
  apply And.intro
  . apply Nat.prime_three
  . simp
    apply Nat.prime_five

-- 6
def list_double : List Nat → List Nat
  | [] => []
  | (x::xs) => (2 * x) :: list_double xs

#eval list_double [1,2,3]
