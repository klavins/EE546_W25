

-- 1) Prove the following FOL examples using introduction, elimination, etc using either direct proofs or tactics. Do not use the built in theorems from the standard library that match these, that's too easy.

variable (p q : Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  sorry

-- 2) Consider the following definition of the sum of the first n squares.

def S (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n*n + S x

-- Show the following result using induction.

example (n : Nat) : 6 * (S n) = n * (n+1) * (2*n+1) :=
  sorry

-- 3) Given the definitions of Person, on_right, and next_to:

inductive Person where | mary | steve | ed | jolin
open Person

def on_right (p : Person) := match p with
  | mary => steve
  | steve => ed
  | ed => jolin
  | jolin => mary

def next_to (p q : Person) := on_right p = q ∨ on_right q = p

-- Prove the following examples:

example : ∀ p , ∀ q , on_right p = q → next_to p q :=
  sorry

example : ∀ p : Person, ∃ q : Person, next_to p q :=
  sorry

example : ∀ p : Person, ∃ q : Person, ¬next_to p q :=
  sorry

-- 4 UNDER CONSTRUCTION

-- 5 UNDER CONSTRUCTION
