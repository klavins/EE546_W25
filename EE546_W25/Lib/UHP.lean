import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Complex.Basic
import EE546_W25.Lib.ComplexSimps

@[ext]
structure UHP where
  z : ℂ
  pos_im : z.im > 0 := by decide

def uj : UHP := ⟨ Complex.I, by simp ⟩

def uhp_add (x y: UHP) : UHP :=
  ⟨
    x.z + y.z,
    by field_simp; exact Right.add_pos' x.pos_im y.pos_im
  ⟩

@[simp]
instance uhp_hadd_inst : HAdd UHP UHP UHP :=
  ⟨ uhp_add ⟩

@[simp]
instance uhp_add_inst : Add UHP :=
  ⟨ uhp_add ⟩

instance uhp_coe_inst: CoeSort UHP ℂ := ⟨ λ u => u.z ⟩
instance uhp_inhabited_inst : Inhabited UHP := ⟨ uj ⟩

abbrev UHP.re (x:UHP) := x.z.re
abbrev UHP.im (x:UHP) := x.z.im
def UHP.conj (z:UHP) : ℂ := z.re - z.im * Complex.I

/- ### Exercise

A nontrivial type has at least two elements. A class noting this is declared like this: -/

class Nontrivial' (α : Type*) : Prop where
   exists_pair_ne : ∃ x y : α, x ≠ y

@[simp]
theorem uhp_conj_simp {z : UHP} : z.conj = z.z.conj := rfl

theorem uhp_im_nz (z : UHP) : z.im ≠ 0 := by
  match z with
  | ⟨ z, hp ⟩ =>
  exact Ne.symm (ne_of_lt hp)

theorem uhp_conj_im_nz (z : UHP) : z.conj.im ≠ 0 := by
  match z with
  | ⟨ z, hp ⟩ =>
  have : 0 > z.conj.im := by simp[Complex.conj]; exact hp
  exact Ne.symm (ne_of_gt this)
