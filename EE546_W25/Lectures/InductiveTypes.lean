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
 -                                **INDUCTIVE TYPES**
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

/- # NAMESPACES

In this chapter we will be defining several fundamental types in Lean, such as the natural numbers Nat and the propositional connectives And and Or. Since these are part of Lean's standard library (included by default), if we do not take appropriate measures, we will get naming collisions. The easiest way to avoid this is to open a temporary namespace. -/

namespace Temp

/- Now, when we define a new symbol, such as -/

def Thing := Type

/- we are actually defining Temp.Thing. If Thing is defined in some inluded library, our new definition will not collide with it. -/













/- # INDUCTIVE TYPES

So far we have introduced only simple `arrow types` composed Lean's basic type (called Type) and functions from those types into types. We now introduce a powerful way to make types, which covers almost all of mathematics, called `inductive types`.

An inductive type is `generated` by `constructors` that may refer to the type itself. They say how to make objects of the given type.

EXAMPLE A type with only two elements is defined by: -/

inductive Two where
  | thing_1 : Two
  | thing_2 : Two

#check Two.thing_1


/- EXAMPLE: The simplest inductive Type has _no_ constructors, meaning it specifies the empty type. -/

inductive Empty





/- # CONSTRUCTORS WITH ARGUMENTS

You can also have constructors that take arguments and transform them into objects of the given type.

EXAMPLE: The type Nat of `Natural Numbers` is defined by two constructors: -/

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat
#check succ (succ zero)

/- All the constructors in an inductively defined type live in a namespace with the same name as the type. The open command allows us to write succ instead of Nat.succ.


EXAMPLE: The type of `BinaryTree` is defined by two constructors: -/

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

open BinaryTree
#check node leaf (node leaf leaf)



/- # FUNCTIONS OF INDUCTIVE TYPES

To work with objects of inductive types, we usually need to know how the object was constructed. Lean uses the keyword `match` for that.

For example: -/

open Two
def toggle ( x : Two ) := match x with
  | thing_1 => thing_2
  | thing_2 => thing_1

/- Lean also knows how to reduce expressions involving match. -/

#reduce toggle (toggle thing_1)


open Nat
def sub_two ( x : Nat ) := match x with
  | zero => zero
  | succ zero => zero
  | succ (succ k) => k

#reduce sub_two (succ (succ (succ zero)))





/- # INDUCTIVE TYPES MAY DEPEND ON OTHER TYPES

The types we have defined so far do not interact with other types. Here's an example that does: Lists of Nats. -/

inductive NatList where
  | empty : NatList
  | cons : Nat → NatList → NatList

namespace NatList
#check cons zero (cons zero empty)              -- [0, 0]
end NatList


/- Or we can define a List of elements of any type. In the the next bit of code, we implicitly state that List depends on an arbitrary type α. -/

inductive List {α : Type} where
  | empty : List
  | cons : α → List → List

namespace List
#check cons "lean" (cons "is cool" empty)      -- ["lean", "is cool"]
end List





/- # AND IS AN INDUCTIVE TYPE

Recall the inference rule

                 Γ ⊢ φ   Γ ⊢ ψ
    `∧-Intro` ———————————————————
                  Γ ⊢ φ ∧ ψ

It states that whenever we know propositions φ and ψ, then we know φ ∧ ψ. From the point of view of types, it says that if φ and ψ are of type Prop, then so is φ ∧ ψ. In Lean we can write this as an inductive type definition as follows. -/

inductive And (φ ψ : Prop) : Prop where
  | intro : φ → ψ → And φ ψ

/- By the Curry-Howard Isomorphism, You can think of

  h : And p q

as either stating that h is evidence that the type And p q is not empty, or h is a proof of the proposition And p q. This allows us to do our first  propositional logic proof: -/

example : p → q → And p q :=
  λ hp hq => And.intro hp hq






/- # AND ELIMINIATION

Recall the elimination rules

                  Γ ⊢ φ ∧ ψ                            Γ ⊢ φ ∧ ψ
  `∧-Elim-Left` ——————————————         `∧-Elim-Right` —————————————
                    Γ ⊢ φ                                Γ ⊢ ψ

which we can write in Lean as -/

def And.left {p : Prop} {q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro p q => p

def And.right (hpq : And p q) :=
  match hpq with
  | And.intro p q => q

/- With these inference rules, we can do even more proofs: -/

example : (And p q) → p :=
  λ hpq => And.left hpq

example : (And p q) → (And q p) :=
  λ hpq => And.intro hpq.right hpq.left




/- # MATCH IS ENOUGH

Note that the elimination rules above are a convenience we defined to make the proof look more like propositional logic. We could also just write: -/

example : (And p q) → p :=
  λ hpq => match hpq with
    | And.intro p q => p

/- This pattern suggests that with inductive types, we should expect that match is a generic elimination rule.  -/




















/- # OR IS ALSO INDUCTIVE

To introduce new OR propositions, we use the two introduction rules

                   Γ ⊢ φ                                Γ ⊢ ψ
 `∨-Intro-Left` ———————————          `∨-Intro-Right` ————————————
                 Γ ⊢ φ ∨ ψ                            Γ ⊢ φ ∨ ψ

In Lean, we have -/

inductive Or (φ ψ : Prop) : Prop where
  | inl (h : φ) : Or φ ψ
  | inr (h : ψ) : Or φ ψ

/- And use this inference rule in proofs as well. -/

example : And p q → Or p q :=
  λ hpq => Or.inl hpq.left












/- # OR ELIMINATION

Recall the inference rule

             Γ,p ⊢ r    Γ,q ⊢ r    Γ ⊢ p ∨ q
  `∨-Elim` ————————————————————————————————————
                        Γ ⊢ r

It allows us to prove r given proofs that p → r, q → r and p ∨ q. We can define this rule in Lean with: -/

def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) :=
  match hpq with
  | Or.inl hpq => hpr hpq
  | Or.inr hpq => hqr hpq

/- Here is an example proof using introduction and elimination. -/

example : Or p q → Or q p :=
  λ hpq => Or.elim
    hpq
    (λ hp => Or.inr hp)
    (λ hq => Or.inl hq)

/- Once again, the elimination rule is just a convenience and the proof could be written with match. -/







/- # FALSE IS INDUCTIVE

Finally, we have False. Which has no introduction rule, kind of like Empty, except we add the requirement that False is also type of Prop.  -/

inductive False : Prop

/- From False we get the Not connective, which is just syntactic sugar. -/

def Not (p : Prop) : Prop := p → False

/- Here is an example proof: -/

example : (p → q) → (Not q → Not p) :=
  fun hpq hnq hp => hnq (hpq hp)
















/- # FALSE ELIMINATION

To define the elimination rule for false

             Γ ⊢ ⊥
  `⊥-Elim` ——————————
             Γ ⊢ p

we take advantage of the fact that False was defined inductively. -/

def False.elim { p : Prop } (h : False) : p :=
  nomatch h

/- TODO: Explain the nomatch keyword in Lean -/

/- Here is an example proof: -/

example : And p (Not p) → q :=
  λ h => False.elim (h.right h.left)










/- # NOTATION

The main difference between what we have defined here and Lean is that Lean defines notation like ∨ and ∧. We won't redo that entire infrastructure here. But to give a sense of it, here is how Lean defines infix notation for Or and And and Not notation.

  infixr:30 " ∨ "  => Temp.Or
  infixr:35 " ∧ "   => Temp.And
  notation:max "¬" p:40 => Temp.Not p

The numbers define the precedence of the operations. So v has lower precedence than n, which has lower precedence than -.

Now we can write -/

end Temp -- start using Lean's propositions

example : (p ∧ (¬p)) → q :=
  λ h => False.elim (h.right h.left)

















/- # REFERENCES

- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

- Homotypy Type Theory Book
  https://homotopytypetheory.org/book/
  Chapter 5 covers inductive types

-/
