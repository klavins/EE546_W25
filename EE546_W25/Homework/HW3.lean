

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

/- 4) Besides ∀ and ∃ that are other quantifiers we can define. For example, the "Exists Exactly One" quantifer allows you to state that there is only one of something. We usually written ∃! as in

    ∃! x, P x

which states there is exactly one x such that P x is true.

We can define this quantifer inductively, just as we did for Exists: -/

inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p

/- However, it is a pain to define the notation E!. So we will just have to write

    Exists1 (λ x => P x)

instead of the above. -/

-- a) Prove the elimination theorem for Exists1

theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists1 (λ x => P x)) (h₂ : ∀ (a : α), P a → b) : b := sorry

-- b) Prove the following examples:

example : ∀ x, Exists1 (λ y : Person => ¬next_to y x ) := sorry

example (α : Type) (P : α → Prop) : Exists1 ( λ x => P x ) → ¬ ∀ x, ¬ P x  := sorry

example : Exists1 (λ x => x=0) := sorry

example : ¬Exists1 (λ x => x ≠ 0) := sorry


-- 5 UNDER CONSTRUCTION
