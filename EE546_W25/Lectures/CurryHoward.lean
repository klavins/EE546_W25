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
 -                          **THE CURRY-HOWARD ISOMORPHISM**
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

/- # STATEMENTS, CONTEXTS, JUDGEMENT

When we introduced the Simply Typed Lambda Calculus, we informally defined the type rules VAR, ABST and APPL. Here we define the typing system formally.

  A `type statement` is a pair x : σ where x is a type variable and σ is a type. We say "x is of type sigma".

  A `typing context` Γ is a finite set of type state statements.

  A `judgement` is an expression of the form Γ ⊢ M : σ where Γ is a typing context, M is a simply typed λ-calculus statement, and σ is a type.

For example, here is a judgment that ought to be true

  { f : α → β, x : α }  ⊢ f x : β


-/
















/- # FORMAL TYPING RULES

Typing rules are written the same way as the inference rules in propositional logic.

  `VAR` —————————————————
          Γ,x:τ ⊢ x:τ

               Γ,x:σ ⊢ M : τ
  `ABST`  ——————————————————————————
           Γ ⊢ (λ x:σ => M) : σ→τ

           Γ ⊢ M : σ→τ    Γ ⊢ N : σ
  `APPL` ——————————————————————————————
                   M N : τ

The first rule says that if a context defines x to have type τ then (somewhat obviously) we can conclude x has type τ.

The second rule says that if our context defines x : σ and entails that M : τ, then we can form an abstraction from x and M that has type σ to τ.

The third rule says that if Γ entails both that M : σ→τ and N : σ, then the application of M to N has type τ. -/






/- # EXAMPLE

Q: Find the type of

  λ x : A => x

A: Working backwards from this goal we use ABST with τ=A and M=x to get

  x:A ⊢ x:A

Then we use VAR. So the expression has type A→A and a proof of this is:

  1) x:A ⊢ x:A                  axiomatically
  2) (λ x : A => x) : A→A       by ABST

As we have seen, Lean figures this out automatically. -/

#check λ x : _ => x












/- # EXAMPLE

Q: Find the types of x and y in

  λ x => λ y => x y

A: Using the ABST rule gives

  x : B   ⊢  λ y => x y : A

for some types A and B. Using ABST again gives

  x : B, y : C   ⊢  x y : A

for some type C. Next we use the APPL rule with M = x, N = y, σ = C, τ = A

  x : B, y : C  ⊢  x : C → A
  x : B, y : C  ⊢  y : C

These judgements would hold if B we equal to C→A. So we make that substitution so the above axioms hold to get:

  λ x : C → A => λ y : C => x y

for some types C and A. Generally speaking, type inference involves applying typing rules, accumulating type equations, and then solving the equations, all of which is done very efficiently in Lean's kernel. -/







/- # EXAMPLE

Q: Find the overall type of the previous expression.

A: Following the derivation above in reverse gives the following type inference proof tree:

    ————————————————————————————— VAR    ————————————————————————————— VAR
     x : C → A, y : C  ⊢  x : C → A       x : C → A, y : C  ⊢  y : C
    ———————————————————————————————————————————————————————————————————— APPL
                      x : C → A, y : C   ⊢  x y : A
                 ————————————————————————————————————————— ABST
                    x : C → A  ⊢  λ y : C => x y : C → A
            ————————————————————————————————————————————————————— ABST
             ⊢  λ x : C → A => λ y : C => x y : (C → A) → C → A

Thus, the type of λ x => λ y => x y is (C → A) → C → A. Note that with a little help, Lean can figure this out for us, but we do need to tell it that x is a function type of some kind. -/

#check λ x : _ → _ => λ y : _ => x y











/- # CURRY-HOWARD ISOMORPHISM INTUITION

Consider the two types we just found:

  A → A
  (C → A) → C → A

The first one is the type of a function on. The second one is the type of a function that takes a function on C → A.

Wwe can also read these as propositional formulas which state

  A implies A
  (C implies A) implies C implies A

It is not a coincidence that these are both tautologies.

The Curry-Howard Isomorphism emerges from the observation that the λ expressions that have the above types look a lot like the proofs that the above implications are tautologies!

With this observation, the statement x : A reads "x is a proof of A".

  λ x : A => x

is a method that takes a proof of A and returns a proof of A, proving the implication A → A. -/




/- # CURRY-HOWARD: TYPES → PROPOSITIONS

To state the CHI exacly, we will restrict ourselves to showing that Propositional Logic with only implication (→) is isomorphic to the simply typed λ-calculus. We will ned once definition.

`DEF` Given a context Γ = { x₁: φ₁, x₂ : φ₂, ..., xₙ : φₙ }, the _range_ of Γ, denoted |Γ|, is { φ₁, φ₂, ..., φₙ }.

`THEOREM` If Γ ⊢ M : φ then |Γ| ⊢ φ.

`PROOF` We convert any type derivation tree into a propositional proof by replacing VAR with AX, ABST with →-Intro, and APPL with →-Elim. This is done by induction on the proof tree. Here we just show an example which should be easily generalized. The type proof tree in the previous section can be re-written be removing all "x : "

    ————————————————————— AX       ———————————————————— AX
     C → A, C  ⊢  C → A               C → A, C  ⊢  C
  ——————————————————————————————————————————————————————————— →Elim
                      C → A, C   ⊢  A
                    ——————————————————— →-Intro
                      C → A  ⊢  C → A
                   —————————————————————— →-Intro
                    ⊢  (C → A) → C → A


-/




/- # CURRY-HOWARD: PROPOSITIONS → TYPES

The opposite direction of the CHI is more technical. We have to show how to produce a λ-calculus term M from a proof of φ so that M : φ. For example, suppose we started with the propositional proof tree in the previous section. How would we produce the type derivation from it? Here we will outline how this is done in general.

First we need a way to produce a type context from a propositional context. Suppose that

  Γ = { φ₁, φ₂, ..., φₙ }

and define

  Δ = { x₁ : φ₁, x₂ : φ₂, ..., xₙ : φₙ }

where the xᵢ are introduced as new type variables. The object Δ is a function of Γ of course, but we just don't write it this way.

`THEOREM` If Γ ⊢ φ then there exists a λ-calculus term M such that ∆ ⊢ M:φ.

The proof of this theorem uses induction on the proof tree that shows Γ ⊢ φ. Since there are three rules (AX, →Intro, and →-Elim), we have three cases, which we handle one by one. -/








/- # CASE: The proof ends with Γ,φ ⊢ φ by the VAR rule

Subcase 1: If φ ∈ Γ then there is some type variable x such that x : φ ∈ Δ. By the VAR rule we can conclude

  Δ  ⊢  x : φ

Subcase 2: If φ ∉ Γ then we introduce a new variable x such that x : φ. Once again by the VAR rule

  Δ, x : φ  ⊢  x : φ

(Why do we need two sub-cases? It's because of how we defined Δ on the previous as related to Γ and not to Γ ∪ { x : φ }).

-/














/- # CASE: The proof ends with →Elim

Suppose the proof that Γ ⊢ φ ends with

    Γ ⊢ ρ → φ      Γ ⊢ ρ
  ——————————————————————————
           Γ ⊢ φ

We need to find a λ-term that has type φ. Here the premises of the above rule instance allow us to assume the induction hypothesis that there exists M and N such that

  Δ ⊢ M : ρ → φ
  Δ ⊢ N : ρ

By the ABST rule, we can conclude

  Δ ⊢ M N : φ



-/









/- # CASE: The proof ends with →Intro

Suppose the proposition φ has the form the ρ → ψ and the proof Γ ⊢ ρ → ψ ends with

     Γ, ρ ⊢ ψ
  ——————————————
    Γ ⊢ ρ → ψ

Subcase 1: ψ ∈ Γ. By the induction hypothesis, there is a term M such that Δ ⊢ M : ψ. Introduce a variable x (not used in Δ) such that x : ρ. Then we can conclude

  Δ, x : ρ  ⊢  M : ψ

and by the ABST rule

  Δ ⊢ λ x : ρ => M : ρ →  ψ

Subcase 2: ψ ∉ Γ. Then by the induction hypothesis, there is a term M such that

  Δ, x : ρ ⊢ M : ψ

from which we may also conclude

  Δ ⊢ λ x : ρ => M : ρ →  ψ

-/


/- # PROPOSITIONS, THEOREMS, AND PROOFS IN LEAN

The Curry-Howard approach is exactly how proofs of theorems are done in Lean. We show that the proposition to be proved is inhabited. In the examples below, we use the type Prop, from Lean's standard library. -/

/- We will start by declaring two variables of type Prop. We use curly braces here instead of parentheses for reasons we will explain later. -/

variable { A C : Prop }

/- To prove a proposition like A → A, we define the identity function from A into A, showing the proposition considered as a type is occupied. We have called the bound variable in the lambda expression _proof_, but you could call the bound variable anything you like. -/

def my_theorem : A → A :=
  λ proof : A => proof

/- Lean provides the keyword _theorem_ for definitions intended to be results, which is like def but does requires the type of the theorem being defined to be Prop. The theorem keyword also gives Lean and the user an indication of the intended use of the definition. -/

theorem my_lean_theorem : A → A :=
  λ proof : A => proof





/- # APPLYING THEOREMS TO PROVE OTHER THEOREMS

As another example, we prove the other proposition we encountered above. Here we call the bound variables pca for "proof of c → a" and pc for "proof of c".  -/

theorem another_theorem : (C → A) → C → A :=
  λ pca : C → A =>
  λ pc : C =>
  pca pc

/- Or even better, we can use our first theorem to prove the second theorem: -/

theorem another_theorem_v2 : (C → A) → C → A :=
  λ h : C → A => my_lean_theorem h















/- # MORE EXAMPLES -/

theorem t1 : A → C → A :=
  λ pa : A =>
  λ pc : C =>                                -- Notice that pc is not used
  pa

theorem t2 : A → C → A :=
  λ pa pc  => pa                             -- We can use λ with two arguments

theorem t3 : A → C → A :=
  λ pa _ => pa                               -- We can tell Lean we know pc is not used

example : A → C → A :=                       -- We can state and prove an unnamed theorem
  λ pa _ => pa                               -- using the `example` keyword











/- # NEGATION

There are, of course, only so many theorems we can state using only implication. In the next chapter we will show how the λ-calculus can be extended to include ∧, ∨, and ⊥. To give a sense of how this looks, here is an example using ¬p, which as you will recall is the same as p → ⊥. -/

example : p → ¬p → q :=
  λ pa pna => absurd pa pna

example : (p → q) → (¬q → ¬p) :=
  fun hpq nq hp => absurd (hpq hp) nq

/- Here, absurd is a theorem from the Lean standard library that we will discuss when we get to Lean's `inductive type` system. -/















/- # SIDENOTE ABOUT VARIABLE DECLARATIONS

If we had used

  variable (A C : Prop)

above, then my_lean_theorem would have (A : Prop) as a non-implicit argument, so it would have to be applied as

  my_lean_theorem (C→A) h

which is ugly.

The way Lean uses variables is by putting them silently into all definitions and theorems that use them. So my_theorem internally looks like:

  theorem my_lean_theorem (A : Prop) : A → A :=
    λ proof : A => proof

On the other hand, if we use curly braces in the variable declaration, as we did in the previous examples, then we get

  theorem my_lean_theorem {A : Prop} : A → A :=
    λ proof : A => proof

so that the type of A is an implicit argument to my_lean_theorem. -/



/- # IN CLASS EXERCISES

- TODO

-/





/- # REFERENCES

Morten Heine Sørensen, Pawel Urzyczyn
"Lectures on the Curry-Howard Isomorphism"
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
  - Chapter 4 describes Intuitionistic Propositional Logic

-/
