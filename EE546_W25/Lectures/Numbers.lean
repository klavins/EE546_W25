/- --------------------------------------------------------------------------
 -
 -
 -
 -
 -
 -
 -
 -                                       EE 546
 -
 -                                **NUMBERS IN LEAN**
 -
 -                    DEPARTMENT OF ELECTRICAL AND COMPUTER ENGINEERING
 -                              UNIVERISITY OF WASHINGTON
 -                                 PROF.  ERIC KLAVINS
 -
 -                                     WINTER 2025
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 ------/

import Mathlib.Tactic.Linarith
import  Mathlib.Data.Set.Defs


/- # SOME OF THE NUMEBRS PROVIDED BY LEAN

  # Standard
  - Natural Numbers: Nat or ℕ
  - Integers: Int or ℤ
  - Floating Point Numbers: Float, Float32

  # Mathlib
  - Rationals: Rat or ℚ
  - Reals: Real or ℝ
  - Complex: Complex or ℂ -/

import Mathlib.Data.Real.Basic -- includes ℚ and ℝ
import Mathlib.Data.Complex.Basic

variable (n : Nat) (i : Int) (f : Float)

variable (q : ℚ)
#check q.num           -- ℤ
#check q.den           -- ℕ

variable (r : ℝ) (c : ℂ)
#check c.im            -- ℝ
#check c.re            -- ℝ










/- # NATURAL NUMBERS

As we've seen, the Natural Numbers are defined inductively. -/

namespace TempNat

-- Definition
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat



















/- # EXAMPLE NATURAL NUMBER RELATIONS

We have already seen a number of definitions of things like addition and multiplication. Relations on the natural numbers are also definitions. For example, less-than is defined inductively. -/

-- # Less-than is defined by two introduction rules
inductive le (x : Nat) : Nat → Prop
  | refl : le x x
  | step : ∀ y, le x y → le x y.succ

#check le zero zero.succ
#check le.refl            --> returns a proof that x ≤ x for any x
#check le.step            --> takes an x and a proof that x ≤ y
                          --  and returns a proof that x ≤ y.succ

example : le zero zero.succ :=
  sorry

-- # Less than or equal
def lt (x y : Nat) := le x y ∧ x ≠ y

example : lt zero zero.succ :=
  sorry






/- # EXAMPLE NATURAL NUMBER THEOREMS -/

theorem succ_eq_succ {n m : Nat} : n.succ = m.succ → n = m := by
  sorry

theorem succ_le_succ {n m: Nat} : le n m  → le n.succ m.succ := by
  sorry

theorem succ_lt_succ {n m : Nat} : lt n m  → lt n.succ m.succ := by
  sorry

end TempNat









/- # L∃∀N'S NATURAL NUMBERS

Lean defines all the standard `operators` and notation: +, -, *, ^, /, <, >, ...

The standard library and Mathlib provide lots and lots of `theorems`.

For example:

  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Defs.html

Most of the equalities and iffs are known to the simlifier.

The `calc` tactic also allows you to do extended calculuations using these theorems.

-/

example (n m : Nat) : n+m+1 = 1+m+n := by
  sorry






/- # THE INTEGERS

The integers are defined from the natural numbers by two introduction rules. The first, ofNat, says that a natural number can be `lifted` to an integer. The second says that the negation of a successor of a natural number can be introduced as a negative number. -/

namespace TempInt

inductive Int where
  | ofNat : Nat → Int         --> A natural number is an int
  | ns : Nat → Int            --> The negation of a successor is an int
                              --> avoiding two representations of zero
open Int
open Nat

#eval ofNat zero.succ    --> 1
#eval ns zero.succ       --> -2
















/- # ADDITION ON THE INTEGERS -/

def sub_nats (x y : Nat) : Int := match y - x with
  | zero => ofNat (x-y)  -- x ≤ y
  | succ z => ns z

#eval sub_nats 3 2  --> 1
#eval sub_nats 2 3  --> -1

def add (x y : Int) : Int := match x, y with
  | ofNat a, ofNat b => ofNat (a+b)
  | ofNat a, ns b    => sub_nats a b.succ
  | ns a, ofNat b    => sub_nats b a.succ
  | ns a, ns b       => ns (a+b).succ

#eval add (ofNat zero.succ) (ofNat zero.succ.succ)    --> 1+2=3
#eval add (ns zero.succ.succ) (ofNat zero.succ)       --> -3 + 1 = -2
#eval add (ns zero.succ.succ) (ns zero.succ)          --> -3 + -2 = -5












/- # EXAMPLE PROPERTY OF INTEGER ADDITION

You can't do much with addition without a huge number of properties. One of the most fundamental is the commutative property. -/

theorem add_comm (x y: Int): add x y = add y x := by
  sorry





















/- # SUBTRACTION ON THE INTEGERS

To define subtraction, we first define the negation operator. Then subtraction is just addition of a negation. -/

def negate_nat (n : Nat) : Int := match n with
  | zero => ofNat zero
  | succ k => ns k

def negate (x : Int) := match x with
  | ofNat n => negate_nat n
  | ns n => ofNat n.succ

def sub (x y : Int) := add x (negate y)

#eval sub (ofNat zero.succ) (ofNat zero.succ.succ.succ) --> 1-3 = -2
















/- # EXAMPLE THEOREMS ABOUT SUBTRACTION -/

theorem neg_neg (x : Int) : negate (negate x) = x := by
  sorry

/- This next theorm can be done calculationally, using the previous theorem. -/

theorem sub_to_add (x y: Int) : sub x (negate y) = add x y := by
  sorry





















/- # ORDERING OF THE INTEGERS -/

-- Only Ints made directly from Nats are non-negative
inductive non_neg : Int → Prop where
  | intro (n: Nat) : non_neg (ofNat n)

def le (x y : Int) : Prop := non_neg (sub y x)

--  -2 < 1
example : le (ns zero.succ) (ofNat zero.succ) := by
  sorry

end TempInt



















/- # L∃∀N's INTGEGERS

Lean provides all the standard operations, relations, and notation.

Lean has copious theorems about the integers:

  https://leanprover-community.github.io/mathlib4_docs/Init/Data/Int/Lemmas.html

-/

example (x y z : Int) : 2*(x+y) - z = 2*x -z + 2*y := by
  sorry

example (x y z : Int) : 2*(x+y) - z = 2*x -z + 2*y :=
  by linarith









/- # RATIONALS

The (pre) rational numbers are just pairs of an Int and a Nat. But we also have to keep track of whether the denomenator is non-zero. We do that be including in the structure definion the rationals a proof of that property. Thus, every rational number in Lean "knows" it is well-formed. -/

namespace TempRat

structure PreRat where
  intro ::
  num : Int
  den : Nat
  dnz : den ≠ 0 := by decide -- works with constants

@[simp]
def eq (x y :PreRat) :=
  x.num * y.den = y.num * x.den

/- Pre-rational admits many representations of the same number. -/

def p12 : PreRat := PreRat.intro 1 2
def p48 : PreRat := PreRat.intro 4 8

example : eq p12 p48 := sorry

/- Of course, Lean would define notation for all of this. -/




/- # DEFINING THE RATIONALS

One way to define the Rationals from the Pre-Rationals is to form the set of all elements equivalent to a given Pre-Rational. Then that set `is` the rational.

For this to work, we have to show that the equality relation is an `equivalence relation`. This means it needs to be:

  - reflexive: eq x x
  - symmetric: eq x y → eq y x
  - transitive: eq x y ∧ eq y z → eq x z

We define the equivalence class of x to be

  [x] = { y | x = y }

In this case, it is the set of all rationals that reduce to the same number.

The following are equivalent statements

  eq x y
  [x] = [y]
  [x] ∩ [y] = ∅

-/






/- # EQUALITY IS REFLEXIVE AND SYMMETRIC -/

theorem eq_refl {x : PreRat} : eq x x := by
  sorry

theorem eq_symm {x y : PreRat} : eq x y → eq y x := by
  sorry
























/- # TRANSITIVITY IS MORE CHALLENGING.

We want to show

   x  =  y   and   y  =  z  →  x  =  z

Or

   p     m         m     a      p     a
  ——— = ———  and  ——— = ——— →  ——— = ———
   q     n         q     n      q     b

But we can't use fractions.

To show that x = z, which is equivalent to pb = aq.

We have

   pbn = pnb = mqb = qmb = qan = aqn

   Thus pb = aq since n ≠ 0

   Source: https://math.stackexchange.com/questions/1316069/how-do-i-show-that-the-equivalence-relation-defining-the-rational-numbers-is-tra

-/











/- # PROOF OF TRANSITIVITY -/

theorem eq_trans {x y z : PreRat}
  : eq x y → eq y z → eq x z := by
  sorry




/- # ONE WAY TO BUILD THE RATIONALS -/

inductive Rat where
  | of_pre_rat : PreRat → Rat

open Rat

def P12 := of_pre_rat p12
def P48 := of_pre_rat p48


















/- # LIFTING EQUALITY TO THE RATIONALS -/

@[simp]
def LiftRel (r : PreRat → PreRat → Prop) (x y : Rat) : Prop :=
  match x, y with
  | of_pre_rat a, of_pre_rat b => r a b

@[simp]
def req := LiftRel eq

example : req P12 P48 := by
  sorry




















/- # LIFTING FUNTIONS -/

@[simp]
def pre_negate (x : PreRat) : PreRat := ⟨ -x.num, x.den, x.dnz ⟩

def Respects (f : PreRat → PreRat) := ∀ x y : PreRat, eq x y → eq (f x) (f y)

theorem negate_respects : Respects pre_negate := by
  sorry

@[simp]
def LiftFun (f : PreRat → PreRat) (x : Rat) : Rat := match x with
  | of_pre_rat a => of_pre_rat (f a)

@[simp]
def negate := LiftFun pre_negate

example : negate (negate P12) = P12 := by
  sorry


































/- # L∃∀N'S RATIONALS

Instead of defining the rationals as equivalence classes, however, Lean defines them by adding that they all have to be reduced.

-/

structure LeanRat where
  num : Int
  den : Nat
  den_nz : den ≠ 0
  reduced : Nat.gcd den num.natAbs = 1

end TempRat

def q12 : ℚ := 1/2
def q48 : ℚ := 4/8

/- Rats get reduced as soon as you define them. -/

#eval q48.num
#eval q48.den
#eval q48






/- # THERE ARE A HUGE NUMBER OF DEFS AND THEOREMS FOR ℚ -/

example (x y z : ℚ) : (x+y)/z = y/z + x/z := by
  sorry

/- Note: These theorems are not about ℚ specifically -/

#check add_comm  --> Works for any `AddCommMagma`
#check add_div   --> Works for any `DivisionSemiring`
