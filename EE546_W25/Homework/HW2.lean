/- # HOMEWORK 2 : DUE MON JAN 20, 2024 (by Midnight) -/


/- 1) Define a lambda abstraction, called double, that takes a Church numeral and doubles it. Evaluate it on a few examples. -/


/- 2) The following lamdba calculus expressions do not type check in Lean.

  λ x y => x y
  λ x y z => x y z
  λ x y => y (y (y x))
  λ x y z => (y x) z

Rewrite them by giving the variables types. Use #check to make sure they work. -/


/- 3) Prove the following example using only lambda calculus expressions -/

  example (p q : Prop) : p → q → p → q → p := sorry


/- 4) Show two different lambda calculus proofs of the following example. Hint, compare the form of the proposition to the Church numerals. -/

  example (p : Prop) : (p → p) → p → p := sorry


/- 5a) Consider the Not-Or operation also known as Nor. It has the following inference rules:

                 Γ ⊢ ¬p   Γ ⊢ ¬q
  `Nor-Intro` ———————————————————
                  Γ ⊢ Nor p q


                    Γ ⊢ Nor p q                            Γ ⊢ Nor p q
  `Nor-Elim-Left` ——————————————         `Nor-Elim-Right` —————————————
                      Γ ⊢ ¬p                                 Γ ⊢ ¬q

Define these in Lean. Here is a start: -/

  inductive Nor (p q : Prop) : Prop where
    | intro : ¬p → ¬q → Nor p q

  def Nor.elim_left {p q : Prop} (hnpq : Nor p q) := sorry

  def Nor.elim_right {p q : Prop} (hnpq : Nor p q) := sorry


/- 5b) Use the above Nor inference rules, and the regular inference rules from Lean's propopsitional logic, to prove the following examples. Note, *do not* use the Classical logic option for these. It isn't needed.  -/

  example (p : Prop) : ¬p → (Nor p p) := sorry
  example (p q : Prop) : (Nor p q) → ¬(p ∨ q) := sorry
  example (p q : Prop) : ¬(p ∨ q) → (Nor p q) := sorry


/- 6) Using the definition of natural numbers below, define functions that perform multiplication and exponentiation similarly to how addition was defined in the Lecture on Inductive Types. Do *not* use Lean's built in natural numbers to do this. Evaluate your functions on a few examples to show they work. -/

namespace Temp

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat           -- succ stand for `successor`

open Nat

def mult (m n : Nat) : Nat := sorry
def exp (m n : Nat) : Nat := sorry

/- 7) Using Lean's built in Integer class, we can define a new inductive type ComplexInt as follows: -/

inductive ComplexInt where
  | complex : Int → Int → ComplexInt

open ComplexInt

/- For example, we can represent the complex number 1 + 2 i with -/

#check complex 1 2

/- Define real, imaginary, addition, subtraction, complex conjugate, and multiplication operations for ComplexInt: -/

def re (x : ComplexInt) : Int := sorry
def im (x : ComplexInt) : Int := sorry
def cadd (x y : ComplexInt) : ComplexInt := sorry
def csub (x y : ComplexInt) : ComplexInt := sorry
def conjugate (x : ComplexInt) : ComplexInt := sorry
def cmul (x y : ComplexInt) : ComplexInt := sorry

/- Test all of these with eval to make sure they work. -/
