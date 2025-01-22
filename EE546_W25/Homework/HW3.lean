
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


/- 4) Besides ∀ and ∃, there are other quantifiers we can define. For example, the "Exists Exactly One" quantifer allows you to state that there is only one of something. We usually written ∃! as in

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

example : ∀ x, Exists1 (λ y : Person => x ≠ y ∧ ¬next_to y x ) :=  by
  sorry

example (α : Type) (P : α → Prop) : Exists1 ( λ x => P x ) → ¬ ∀ x, ¬ P x  := sorry

example : Exists1 (λ x => x=0) := sorry

example : ¬Exists1 (λ x => x ≠ 0) := sorry


/- 5) In this exercise, you will make a simple library, interface with the simplifier, and prove some theorems. -/

/- 5a) Take all of your ComplexInt definitions from HW2 and put them in a file called ComplexInt.lean. Make the operations re, im, cadd, csub, cmul, etc accessible to the simplifier by putting @[simp] just before each definition, as in

@[simp]
def re (x : ComplexInt) : Int := match x with
  | complex a b => a

Add this notation definition to the bottom of the ComplexInt file:

  infixl:65   " + " => cadd
  infixl:85   " * " => cmul

which allows you two write, for example, a*b instead of cmul a b.

To tell Lean where to find your library file, edit EE546_YourLaseName.lean in the base directory of your repo and add

  import EE546_YourLaseName.Homework.ComplexInt

Then, to compile the library to native code (so it runs really fast) do

  lake build

at the command line.

Test your configuration by putting

  import EE546_YourLaseName.Homework.ComplexInt

at the top of your HW3 solutions file and doing

  #eval (complex 1 2) * (complex 3 4) + complex (5 6)

-/

/- 5b) Prove the following using the simplifier and basic logic: -/

open ComplexInt

theorem c_add_comm (a b : ComplexInt) : a + b = b + a := sorry
theorem c_mul_comm (a b : ComplexInt) : a * b = b * a := sorry
theorem c_add_assoc (a b c : ComplexInt) :  a + (b + c) = (a + b) + c := sorry
theorem c_mul_add_distrib (a b c : ComplexInt) : a * (b + c) = (a * b) + (a * c) := sorry

example : (complex 0 1) * (complex 0 (-1)) = complex 1 0 := sorry

/- 5c) Complete the following definition for raising a ComplexInt a to the power of natural number n. Move the resulting definition to your library and rebuild everything. Use match and recursion. Prove the simple theorem after the definition. -/

@[simp]
def cpow (a : ComplexInt) (n: Nat) : ComplexInt := sorry

example : cpow (complex 0 1) 4 = complex 1 0 := sorry

/- 5d) Add the following definition to your library, rebuild everything, prove the example, and prove the theorem stating that only ComplexInts with norm 1 have inverses. -/

@[simp]
def cnorm (a : ComplexInt) : Int := re ( a * (conjugate a) )

example : cnorm (complex 1 1) = 2 := sorry

-- Note: This one is challenging. You might want to make some auxilliary lemmas. Also it's ok to use classical logic.
theorem invertibles (a : ComplexInt)
  : cnorm a = 1 → ∃ x : ComplexInt, a*x = complex 1 0 :=
  sorry
