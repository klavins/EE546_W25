
-- 1
def α := Type
def N := (α → α) → α → α
#check N

def c₁ := λ ( f : α → α ) => λ ( x : α ) => f x
def c₂ := λ ( f : α → α ) => λ ( x : α ) => f (f x)

def double := λ (n : N) => λ (f : α → α) => λ (x: α) => c₂ (n f) x

#reduce (types:=true) double c₁
#reduce (types:=true) double c₂

-- 2
#check λ (x : Type → Type) y => x y
#check λ (x:Type → Type → Type) y z => x y z
#check λ x (y: Type → Type)  => y (y (y x))
#check λ x (y : Type → Type → Type) z => (y x) z

-- 3
example (p q : Prop) : p → q → p → q → p := λ h _ _ _ => h

--4
example (p : Prop) : (p → p) → p → p := λ f x => f x
example (p : Prop) : (p → p) → p → p := λ f x => f (f x)

-- 5a)
inductive Nor (φ ψ : Prop) : Prop where
  | intro : ¬φ → ¬ψ → Nor φ ψ

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) := match hnpq with
  | Nor.intro hnp hnq => hnp

def Nor.elim_right {p q : Prop} (hnpq : Nor p q) := match hnpq with
  | Nor.intro hnp hnq => hnq

-- 5b)
example (p : Prop) : ¬p → (Nor p p) :=
  λ hp => Nor.intro hp hp

example (p q : Prop) : (Nor p q) → ¬(p ∨ q) :=
  λ hnpq h => Or.elim h
              (λ hp => (Nor.elim_left hnpq) hp)
              (λ hq => (Nor.elim_right hnpq) hq)

example (p q : Prop) : ¬(p ∨ q) → (Nor p q):=
  λ hnpq => Nor.intro
            (λ hp =>
              have h : p ∨ q := Or.inl hp
              hnpq h
            )
            (λ hq =>
              have h : p ∨ q := Or.inr hq
              hnpq h
            )

-- 6
namespace Temp

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat           -- succ stand for `successor`

open Nat

def plus (n m : Nat) := match n with
  | zero => m
  | succ x => succ (plus x m)

def mult (m n : Nat) : Nat := match m with
  | zero => zero
  | succ x => plus (mult x n) n            -- (x+1) * n = x*n + n

#eval mult (succ (succ zero)) (succ (succ (succ zero)))

def exp (m n : Nat) : Nat := match n with
  | zero => (succ zero)
  | succ x => mult (exp m x) m              -- m^(n+1) = m^n * m

#eval exp (succ (succ zero)) (succ (succ (succ zero)))

end Temp

-- 7
inductive ComplexInt where
  | complex : Int → Int → ComplexInt

open ComplexInt

#check complex 1 2

def re (x : ComplexInt) : Int := match x with
  | complex a b => a

def im (x : ComplexInt) : Int := match x with
  | complex a b => b

def cadd (x y : ComplexInt) : ComplexInt :=
  complex (re x + re y) (im x + im y)

def csub (x y : ComplexInt) : ComplexInt :=
  complex (re x - re y) (im x - im y)

def conjugate (x : ComplexInt) : ComplexInt :=
  complex (re x) (-im x)

def cmul (x y : ComplexInt) : ComplexInt :=
  complex ((re x) * (re y) - (im x) * (im y))
          ((re x) * (im y) + (im x) * (re y))

#eval re (complex 1 2) -- 1
#eval im (complex 1 2) -- 2
#eval cmul (complex 1 2) (cadd (complex 1 2) (complex 3 4)) -- -8 + 14j
#eval conjugate (csub (complex 1 2) (complex 3 4)) -- -2 + 2j
