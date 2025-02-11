/- --------------------------------------------------------------------------
 -
 -
 -
 -
 -
 -
 -
 -                                  EE 546
 -
 -                        **HEIRARCHY EXAMPLE: ZMod**
 -
 -               DEPARTMENT OF ELECTRICAL AND COMPUTER ENGINEERING
 -                          UNIVERISITY OF WASHINGTON
 -                             PROF.  ERIC KLAVINS
 -
 -                                WINTER 2025
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
 -
 ------/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms



/- # CONGRUENCE

Suppose we want to work with the set of integers `modulo` a natural number m. In this setting we say two numbers are `congruent` modulo m if

  (a - b) % m = 0

or said differently,

  ∃ k : ℤ, a-b = m*k

We write a ≡ b mod m and put ⟦a⟧ to be the equivalence class of all numbers congruent to a. In particular,

  ⟦a⟧ = { a + m, a - m, a + 2*m, a-2*m, ... }

The set of all equivalence classes is called ℤ/m. It forms a `Group` and even a `Ring`, which means you can add them, multiply them, take additive inverses, define 0 and 1, and so on. If m is prime, you can also define multiplicative inverses, and the class form a `Field`.

There are tactics for group, abel, ring, and field you can use to simplify expressions.

-/




/- # TWO PATHS

1. You could define add and mul and all the other operations on ℤ/m and then use  `notation` and `infix` and to define notation for +, *, and so on. We did this with ComplexInt. And it was a pain.

2. You could use Mathlib's library of `classes` to show that ℤ/m is a Ring and then use all of Mathlib's infrastructure for Rings. In particular you can use `linarith`.

-/





/- # CONGRUENCE IN LEAN -/

import Mathlib.Data.Int.ModEq

example : -1 ≡ 3 [ZMOD 4] := by rfl
example : 3 ≡ 30 [ZMOD 27] := by rfl
















/- # SETOIDS

The first part of the heirarchy is to show that the relation form a `Setoid`, which is just a set with an equivalence relation. Since ZMOD has all these properties defined already, we can just use them. This is done by creating an `instance` of the structure `Setoid` defined like this: -/

instance mod_equiv {n:Nat} : Setoid ℤ where
  r := Int.ModEq n
  iseqv := {
    refl := Int.ModEq.refl
    symm := Int.ModEq.symm
    trans := Int.ModEq.trans
  }

/- This could equally well have been written

  instance mod_equiv {n:Nat} : Setoid ℤ :=
    ⟨ Int.ModEq n, Int.ModEq.refl, Int.ModEq.symm, Int.ModEq.trans ⟩

-/









/- # QUOTIENT OF ℤ by ≡ₙ

Next, we define ℤ/m to be the `Quotient` of ℤ by the equivalence relation ≡ₘ. This sets up all the equivalence classes and allows us to use the regular = sign. -/

def Zmod (m:Nat) := Quotient (@mod_equiv m)

/- We also define a help function to make elements of the quotient. -/

def mk (n:ℕ) : ℤ → Zmod n := Quotient.mk''

/- Now we can make elements using mk or ⟦⟧. The latter is not standalone. It needs a context to know what Quotient we are using. -/

#check mk 3 4              --> Zmod 3
#check ⟦4⟧                 --> Quotient ?m.256
#check mk 3 4 = ⟦4⟧        --> Type of ⟦4⟧ inferred to be Zmod 3

/- Adding notation -/
notation:100 " ⟦ " lhs:100 " ⟧ " rhs:100 => mk rhs lhs
#check ⟦4⟧27







/- # A THEOREM FOR THE SIMPLIFIER

This theorem seems to be needed for all Quotients to help the simplifier. -/

@[simp]
theorem mod_rep {n:ℕ} {a b :ℤ }
  : mk n a = mk n b ↔ (⟦a⟧ : Zmod n) = ⟦b⟧ :=
  ⟨ id, id ⟩











/- # CHECKING EQUALITY  -/

example : ⟦1⟧4 = ⟦5⟧4 := by
  simp[mod_equiv]
  decide                 -- congruence check is defined algorithmically
                         -- and the `decide` tactic uses the algorithm

example : ⟦1⟧4 ≠ ⟦2⟧4 := by
  simp[mod_equiv]
  exact of_decide_eq_false rfl













/- # ZERO AND INHABITED -/

instance mod_zero_inst {n:Nat}: Zero (Zmod n) := ⟨ ⟦0⟧n ⟩
instance mod_inhabited_inst {n:ℕ}: Inhabited (Zmod n) := ⟨0⟩

#check (0:Zmod 5)

example : Zmod 4 := mod_inhabited_inst.default















/- # ADDITION

To use addition on Zmod m, we need to show that our notion of addition respects the equivalence relation. -/

#check_failure ⟦3⟧4 + ⟦1⟧4  -- Addition doesn't work.

def pre_mod_add {n:ℕ} (x y : ℤ) : Zmod n := mk n (x + y)

theorem mod_add_res_1 {n:ℕ} (a b c : ℤ)
  : b ≡ c [ZMOD n] → @pre_mod_add n a b = @pre_mod_add n a c := by
  intro h
  apply Quot.sound   -- This is a fundamental axiom provided by Lean.
  exact Int.emod_add_cancel_left.mpr h

theorem mod_add_res_2 {n:ℕ} (a b c : ℤ)
  : a ≡ b [ZMOD n] → @pre_mod_add n a c = @pre_mod_add n b c := by
  intro h
  apply Quot.sound
  exact (Int.emod_add_cancel_right c).mpr h

/- The we lift addition tot he quotient -/

instance mod_add_inst {n:ℕ} : Add (Zmod n) :=
  ⟨ λ x y => Quot.lift₂ pre_mod_add mod_add_res_1 mod_add_res_2 x y ⟩

#check ⟦3⟧4 + ⟦1⟧4  -- Addition works!






/- # SUBTRACTION -/

#check_failure ⟦3⟧4 - ⟦1⟧4

def mod_neg {n:ℕ} (x:ℤ) : Zmod n := mk n (-x)

theorem mod_neg_res {n:ℕ} (a b: ℤ)
  : a ≡ b [ZMOD n] → @mod_neg n a = @mod_neg n b := by
  intro h
  apply Quot.sound
  simp_all[mod_equiv]

instance mod_neg_inst {n:ℕ} : Neg (Zmod n) :=
  ⟨ λ x => Quot.lift mod_neg mod_neg_res x ⟩

instance {n:ℕ} : Sub (Zmod n) :=
  ⟨ λ x y => x + (-y) ⟩

instance {n:ℕ} : Inv (Zmod n) :=
  ⟨ λ x => -x ⟩

#check ⟦3⟧4 - ⟦1⟧4





/- # THE ASSOCIATEVE PROPERTY -/

example {m:ℕ} (a b c : Zmod m) : a+b+c = a+(b+c) := by
  apply AddSemigroup.add_assoc

theorem mod_assoc {n:ℕ} (x y z: Zmod n) : (x+y)+z = x+(y+z) := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  let ⟨ b, hb ⟩  := Quotient.exists_rep y
  let ⟨ c, hc ⟩  := Quotient.exists_rep z
  simp[←ha,←hb,←hc]
  apply Quot.sound
  simp[mod_equiv,Int.add_assoc]

instance {n:ℕ} : AddSemigroup (Zmod n) :=
  ⟨ mod_assoc ⟩

example {m:ℕ} (a b c : Zmod m) : a+b+c = a+(b+c) := by
  apply AddSemigroup.add_assoc






/- # PROPERTIES ABOUT ZERO AND INVERSES -/

theorem mod_zero_add {n:ℕ} (x : Zmod n) : 0 + x = x := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  simp[←ha]
  apply Quot.sound
  simp[mod_equiv,Int.ModEq]

theorem mod_add_zero {n:ℕ} (x : Zmod n) : x + 0 = x := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  simp[←ha]
  apply Quot.sound
  simp[mod_equiv,Int.ModEq]

theorem mod_add_neg {n:ℕ} (x y : Zmod n) : x - y = x + -y := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  let ⟨ b, hb ⟩  := Quotient.exists_rep y
  simp[←ha,←hb]
  apply Quot.sound
  simp[mod_equiv,Int.ModEq]

theorem mod_add_inv {n:ℕ} (x : Zmod n) : -x + x = 0 := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  simp[←ha]
  apply Quot.sound
  simp[mod_equiv,Int.ModEq]





/- # GROUPS -/

example {m:ℕ} (a b : Zmod m) : a+(-a+b) = b := by
  apply?

instance {n:ℕ} : AddMonoid (Zmod n) :=
  ⟨ mod_zero_add, mod_add_zero, nsmulRec, λ _ => rfl , λ _ _ => rfl ⟩

instance {n:ℕ} : SubNegMonoid (Zmod n) :=
  ⟨ mod_add_neg, zsmulRec, λ _ => rfl, λ _ _ => rfl, λ _ _ => rfl ⟩

instance mod_add_group {n:ℕ} : AddGroup (Zmod n) :=
  ⟨ mod_add_inv ⟩

example {m:ℕ} (a b : Zmod m) : a+(-a+b) = b  := by
  exact add_neg_cancel_left a b -- from Mathlib.Algebra.Group.Defs




/- # COMMUTATIVITY -/

/- Make this private so it doesn't shadow the Group theorem -/
private theorem mod_add_com {n:ℕ} (x y : Zmod n) : x+y = y+x := by
  let ⟨ a, ha ⟩  := Quotient.exists_rep x
  let ⟨ b, hb ⟩  := Quotient.exists_rep y
  simp[←ha,←hb]
  apply Quot.sound
  simp[mod_equiv,Int.ModEq,Int.add_comm]

instance {n:ℕ} : AddCommMagma (Zmod n)     := ⟨ mod_add_com ⟩
instance {n:ℕ} : AddCommSemigroup (Zmod n) := ⟨ mod_add_com ⟩
instance {n:ℕ} : AddCommMonoid (Zmod n)    := ⟨ mod_add_com ⟩
instance {n:ℕ} : AddCommGroup (Zmod n)     := ⟨ mod_add_com ⟩

-- Prove stuff using AddGroup theorems
#check neg_add_cancel_right
#check AddCommMagma.add_comm



/- # EXAMPLES -/

example {n:ℕ} (x y : Zmod n) : x + -y + y = x := by
  exact neg_add_cancel_right x y

example {n:ℕ} (x y z : Zmod n) : z + x + -y + y = x + z := by
  calc z + x + -y + y
  _ = z + x := by rw[neg_add_cancel_right]
  _ = x + z := AddCommMagma.add_comm z x

example {n:ℕ} (x y : Zmod n) : x + -y + y = x := by
  abel  -- The tactic for additive commutative groups (a.k.a. abelian groups)

example {n:ℕ} (x y z : Zmod n) : z + x + -y + y = x + z := by
  abel


/- # YOU CAN CONTINUE WITH EVERYTHING NEEDED FOR A RING -/

#print NonUnitalSemiring
#print Semiring
#print Ring












/- # DECIDABLE EQUALITY

Checking whether two values are equal requires an algorithm. But all we have defined are relationships.

-/

def f (A:Zmod 4) := if A = ⟦3⟧4 then 1 else 0

instance {n:ℕ} : DecidableEq (Zmod n) := by
  intro x y
  conv =>
    rhs
    unfold mod_equiv
    simp[Quot.sound]
    simp[mod_equiv,mod_equiv.iseqv, Int.ModEq]


  apply Quotient.
  sorry
