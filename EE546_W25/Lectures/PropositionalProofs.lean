/- # PROPOSITIONS TO PROVE

The following examples are taken from

  https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html

-/

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p := sorry

example : p ∧ q ↔ q ∧ p := sorry

example : p ∨ q ↔ q ∨ p := sorry

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

example : (p → (q → r)) ↔ (p ∧ q → r) := sorry

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

example : ¬(p ∧ ¬p) := sorry

example : p ∧ ¬q → ¬(p → q) := sorry

example : ¬p → (p → q) := sorry

example : (¬p ∨ q) → (p → q) := sorry

example : p ∨ False ↔ p := sorry

example : p ∧ False ↔ False := sorry

example : (p → q) → (¬q → ¬p) := sorry

example : (p → q) → (¬q → ¬p) := sorry

example : (p∧q) → ((p → (q → False)) → False) := sorry

example : ((p → (q → False)) → False) → (p∧q) := sorry
