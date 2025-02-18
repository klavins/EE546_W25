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
 -                        **HIERARCHY EXAMPLE: SL2**
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



/- # FINITE TYPES  -/

#check Fin 3
#check (0:Fin 3)

def v : Fin 3 := 11234
#eval v















/- # MATRICES -/

#check ![![1,2],![3,4]]
#check !![1,2;3,4]

def H : Matrix (Fin 3) (Fin 3) Real := !![
   1,2,3;
   3,4,5;
   4,5,6
]

#check H*H+H
#check H⁻¹
#check H.det










/- # SL2

Consider the 2x2 matrices with Integer entries of the form

   a b
   c d

where ad - bc = 1. I.e. the determinant of the matrix is 1. This forms a group called the Special Linear Group SL(2,ℤ). First, we define the basic type. First we define a structure to hold the value and a proof the value has determinant 1.

The @[ext] modifier lets you use the `ext` tactic, which states that two structures are equal if their fields are equal.

Then the instance of CoeSort lets you write M instead of M.val when you mean M.val.-/

@[ext]
structure SL2 where
  val : Matrix (Fin 2) (Fin 2) ℤ
  det1 : val.det = 1 := by decide

#check SL2.ext
#check SL2.ext_iff
















/- # ELEMENTS OF SL2

Each element has a matrix value and a proof that value has determinant one. These can be written in a variety of ways.-/

-- use default constructor
#check SL2.mk !![1,1;0,1] rfl
#check ({val:=!![1,1;0,1], det1 := rfl} : SL2)

-- use default constructor with default proof for det1
#check SL2.mk !![1,1;0,1]
#check ({val:=!![1,1;0,1]} : SL2)

#check (⟨!![1,1;0,1], rfl⟩ : SL2)

#check_failure SL2.mk !![1,1;1,1]

-- Defining some elements for later examples
def T := SL2.mk !![1,1;0,1]
def S := SL2.mk !![0, -1; 1, 0]





/- # EXERCISES -/

example : ¬∃ M: SL2 , M.val = !![0,0;0,0] := by
  intro ⟨ M, h ⟩
  have h1 : M.val.det = 0 := by rw[h]; exact rfl
  simp[M.det1] at h1




















/- # CLASSES AND INSTANCES

We would like to use all the notation and theorems associated with groups without reproving everything. Lean does this with classes and instances. We will use the following classes:

  Inhabited         -- SL2 has at least one element
  CoeSort           -- Write A instead of A.val when context is clear
  HMul, Mul         -- SL2 has multiplication
  Inv               -- SL2 has inverses
  One               -- SL2 has an identity
  SemiGroup         -- SL2 multiplication is associative
  MulOneClass       -- 1*A = A
  Group             -- A⁻¹*A = 1 and A*A⁻¹ = 1

One of the simplest classes is `Inhabited`. It is declared just like a structure.

-/

class Inhabited' (α : Sort*) where
  default : α

/- We can show that SL2 is inhabited by assigned the default element. -/
instance mod_inhabited_inst : Inhabited SL2 := ⟨ SL2.mk !![1,0;0,1] ⟩

def SL2.default : SL2 := Inhabited.default











/- # EXERCISE

A nontrivial type has at least two elements. A class noting this is declared like this:
 -/

class Nontrivial' (α : Type*) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

instance mod_non_triv : Nontrivial SL2 :=
  ⟨ by
    use S
    use T
    intro h
    have : S.val 0 0 = T.val 0 0 := by simp[h];
    simp[S,T] at this
  ⟩
















/- # COERCION

When we have M : SL2, we would like use M as a matrix. But we end up having to write M.val in such contexts. For example, in the code below, the first argument to the constructor expects a matrix. -/

def sl2_mul_v1 (A B : SL2) : SL2 := ⟨ A.val * B.val, by simp[A.det1,B.det1] ⟩

/- To make our code more readable, we can provide a coercion from SL2 into a Matrix. -/

instance mod_group_coe: CoeSort SL2 (Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨ λ M => M.val ⟩

/- Now the above definition can be writte a bit more concisely. -/
def sl2_mul (A B : SL2) : SL2 := ⟨ A * B, by simp[A.det1,B.det1] ⟩

















/- # MULTIPLICATION -/

#check_failure S*T

instance m_hmul: HMul SL2 SL2 SL2 :=
  ⟨ sl2_mul ⟩

instance m_mul: Mul SL2 :=
  ⟨ sl2_mul ⟩

@[simp]
theorem mod_mul (A B : SL2) : A * B = ⟨ A*B, by simp[A.det1,B.det1] ⟩ := by
  calc A * B
  _  = ⟨ A, A.det1 ⟩ * ⟨ B, B.det1 ⟩ := rfl
  _  = ⟨ A*B, by simp[A.det1,B.det1] ⟩ := rfl

#check S*T
#eval S*T








/- # EXERCISE -/

example : ¬ ∀ A B : SL2, A*B = B*A := by
  intro h
  have h1 := h S T
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h1]
  simp[S,T] at h2















/- # INVERSES -/

#check_failure T⁻¹

noncomputable                             -- noncomputable because this method does
instance inst_mod_inv: Inv SL2 :=         -- not show how to derive the inverse, just
  ⟨ λ M => ⟨ M⁻¹, by simp[M.det1] ⟩  ⟩    -- that it exists since M.det = 1.

#check T⁻¹

@[simp]
theorem mod_inv (A : SL2) : A⁻¹ = ⟨ A⁻¹, by simp[A.det1] ⟩ := rfl












/- # EXERCISE -/

example : ∀ A B : SL2, (A*B)⁻¹ = B⁻¹ * A⁻¹ := by
  intro A B
  simp[mod_inv]
  exact Matrix.mul_inv_rev A.val B.val
















/- # THE IDENTITY -/

@[simp]
def one : SL2 := ⟨ 1, by simp ⟩

#check_failure T * 1

instance inst_mod_one: One SL2 := ⟨ one ⟩

#check T * 1












/- # TEACHING THE SIMPLIFIER ABOUT 1 -/

@[simp]
theorem mod_one : (1:SL2) = one := rfl

@[simp]
theorem mod_one_expl : (1:SL2) = ⟨ !![(1:ℤ),0;0,1], by simp ⟩ := by
  simp[one]
  exact Matrix.one_fin_two

theorem one_expl : (1:SL2) = !![(1:ℤ),0;0,1] := by
  simp[one]
  exact Matrix.one_fin_two










/- # EXERCISE -/

-- Hint: use Matrix.nonsing_inv_mul

example : ∀ A : SL2, A⁻¹*A = 1 := by
  intro A
  simp[mod_inv]
  apply Matrix.nonsing_inv_mul
  simp[A.det1]


















/- # ASSOCIATIVITY-/

theorem mod_mul_assoc : ∀ A B C : SL2 , A * B * C = A * ( B * C ) := by
  intro A B C
  simp[Matrix.mul_assoc]

instance inst_mod_semi: Semigroup SL2 :=
  ⟨ mod_mul_assoc ⟩

theorem mod_one_left : ∀ A : SL2, 1 * A = A := by
  intro A
  simp[mod_mul,Matrix.mul_assoc]

theorem mod_one_right : ∀ A : SL2, A * 1 = A := by
  intro A
  simp[mod_mul,Matrix.mul_assoc]

instance inst_mul_one : MulOneClass SL2 :=
  ⟨ mod_one_left, mod_one_right ⟩

















/-# EXERCISE SL2 IS NOT COMMUTATIVE -/

#eval S*T
#eval T*S

example : S*T ≠ T*S :=  by
  intro h
  have h2 : (S*T).val 0 0 = (T*S).val 0 0 := by simp[h]
  simp[S,T] at h2













/- # INVERSES AND GROUP INSTANCE-/

theorem mod_inv_left : ∀ A : SL2, A⁻¹ * A = 1 := by
  intro A
  simp[A.det1]

theorem mod_inv_right : ∀ A : SL2, A * A⁻¹ = 1 := by
  intro A
  simp[A.det1]

noncomputable
instance inst_mod_group : Group SL2 :=
  @Group.ofLeftAxioms SL2 _ _ _ mod_mul_assoc mod_one_left mod_inv_left









/- # EXAMPLE -/

example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A :=
  calc (A⁻¹*B*A)⁻¹
  _  = A⁻¹ * (A⁻¹*B)⁻¹   := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A⁻¹⁻¹) := by rw[DivisionMonoid.mul_inv_rev]
  _  = A⁻¹ * (B⁻¹*A)     := by rw[DivisionMonoid.inv_inv]
  _  = A⁻¹ * B⁻¹ * A     := by rw[Semigroup.mul_assoc]

example (A B : SL2): (A⁻¹*B*A)⁻¹ = A⁻¹*B⁻¹*A := by group










/- # EXERCISE -/

example (A B C : SL2) : A * (B * C) * (A * C)⁻¹ * (A * B * A⁻¹)⁻¹ = 1 := by group
