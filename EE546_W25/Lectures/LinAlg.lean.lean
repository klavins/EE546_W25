import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

def Vect (n:ℕ) := (Fin n) → ℂ

def Mat (m n: ℕ) := (Fin m) → (Fin n) → ℂ

def smul {m n: ℕ} (a:ℂ) (M: Mat m n) := λ i j => a * (M i j)

noncomputable
def mul {m n p:ℕ} (A : Mat m n) (B: Mat n p) : Mat m p :=
  λ i j => ∑ k : (Fin n), (A i k) * (B k j)

def add {m n :ℕ} (A : Mat m n) (B: Mat m n) : Mat m n :=
  λ i j => A i j + B i j

def sub {m n :ℕ} (A : Mat m n) (B: Mat m n) : Mat m n :=
  λ i j => A i j - B i j

def transpose {m n : ℕ} (A : Mat m n) : Mat n m := λ i j => A j i

def A : Mat 2 2 := λ i j => i+j
def B : Mat 2 1 := λ i j => 1

example : smul 2 (mul A B)  = !![2;6] := by
  funext U V
  simp[A,B,smul,mul]
  fin_cases U <;> fin_cases V <;> dsimp
  . ring
  . ring

def R22 := Mat 2 2

namespace R22

def zero : R22 := !![0,0;0,0]

def one : R22 := !![1,0;0,1]

def det (A : R22) : ℂ := (A 0 0)*(A 1 1)-(A 0 1)*(A 1 0)

noncomputable
def invertible (A : R22) : Bool := A.det ≠ 0

def adj (A : R22) : R22 := !![
  A 1 1, -A 0 1;
 -A 1 0,  A 0 0
]

noncomputable
def inv (A : R22) : R22 :=
  if invertible A then smul (1/A.det) A.adj else zero

def char_poly (s:ℂ) (A : R22) := det (sub (smul s one) A)

def is_eigenval (s:ℂ) (A : R22) := char_poly s A = 0

/- # THEOREMS -/

theorem adj_off_diag (A B : R22)
  : (B = mul A A.adj) → (B 0 1 = 0 ∧ B 1 0 = 0) := by
  intro h
  simp[h]
  apply And.intro
  . simp[mul,adj,mul_comm]
  . simp[mul,adj,mul_comm]

theorem adj_diag {A B : R22}
  : (B = mul A A.adj) → (B 0 0 = A.det ∧ B 1 1 = A.det) := by
  intro h
  simp[h]
  apply And.intro
  . simp[mul,adj,mul_comm,det,sub_eq_add_neg]
  . simp[mul,adj,mul_comm,det,sub_eq_add_neg,add_comm]

theorem mul_by_adj_right {A: R22} : (mul A A.adj) = !![A.det,0; 0, A.det] := by
  funext i j
  simp[mul,adj,det]
  fin_cases i <;> fin_cases j <;> dsimp <;> ring

theorem mul_by_adj_left {A: R22} : (mul A.adj A) = !![A.det,0; 0, A.det] := by
  funext i j
  simp[mul,adj,det]
  fin_cases i <;> fin_cases j <;> dsimp <;> ring

theorem adj_comm {A :R22} : mul A A.adj = mul A.adj A := by
  simp[mul_by_adj_right,mul_by_adj_left]

theorem smul_comm (A B:R22) {a:ℂ} : mul A (smul a B) = smul a (mul A B) := by
  funext i j
  simp[mul,smul]
  fin_cases i <;> fin_cases j <;> ring

theorem smul_comm2  {A B: R22} {a:ℂ} : mul A (smul a B) = mul (smul a A) B := by
  funext i j
  simp[mul,smul]
  fin_cases i <;> fin_cases j <;> ring

theorem mul_assoc {A B C: R22} : mul A (mul B C) = mul (mul A B) C := by
  funext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> simp[mul] <;> ring

theorem inv_comm {A : R22} : invertible A → mul A A.inv = mul A.inv A := by
  intro h
  simp[inv,h]
  calc mul A (smul A.det⁻¹ A.adj)
  _  = smul A.det⁻¹ (mul A A.adj) := by simp[smul_comm]
  _  = smul A.det⁻¹ (mul A.adj A) := by simp[adj_comm]
  _  = mul A.adj (smul A.det⁻¹ A) := by simp[smul_comm]
  _  = mul (smul A.det⁻¹ A.adj) A := by simp[smul_comm2]

theorem mul_inv_right {A : R22} : invertible A → mul A A.inv = one := by
  intro h
  simp[inv,h]
  simp[invertible] at h
  simp[smul_comm,mul_by_adj_right,one]
  funext i j
  fin_cases i <;> fin_cases j <;> simp[inv_mul_cancel₀ h,smul]

theorem mul_inv_left (A : R22) : invertible A → mul A.inv A = one := by
  intro h
  rw[←inv_comm h]
  exact mul_inv_right h

theorem char_poly_tr (s:ℂ) (A : R22)
  : char_poly s A = char_poly s (transpose A) := by
  simp[char_poly,det,smul,mul,sub,one,transpose,mul_comm]

theorem eigen_tr {s:ℂ} {A : R22}
  : is_eigenval s A ↔ is_eigenval s (transpose A) := by
  simp[is_eigenval]
  rw[char_poly_tr]

theorem mul_trans {m n p : ℕ} (A : Mat m n) (B : Mat n p)
  : transpose (mul A B) = mul (transpose B) (transpose A) := by
  funext i j
  simp[mul,mul_comm,transpose]

theorem tr_tr {m n: ℕ} (A : Mat m n)
  : transpose (transpose A) = A := by
  unfold transpose
  simp

theorem tr_smul {m n: ℕ} {a:ℂ} {A:Mat m n}
  : transpose (smul a A) = smul a (transpose A) := by
  unfold transpose smul
  simp

theorem trans_eq_trans {m n:ℕ} {A B : Mat m n}
  : A = B ↔ (transpose A) = (transpose B) := by
  apply Iff.intro
  . intro h
    simp[h]
  . intro h
    unfold transpose at h
    funext t s
    let q1 := (fun i j => A j i) s t
    let q2 := (fun i j => B j i) s t
    have g : q1 = q2 := by conv => lhs; unfold q1; rw[h]
    simp[q1,q2] at g
    exact g

theorem det_smul {a:ℂ} {A : R22} : det (smul a A) = a^2 * (det A) := by
  simp[det,smul]
  ring

theorem det_adj {A : R22} : A.det = A.adj.det := by
  simp[det,adj]
  ring

theorem det_mul {A B : R22} : det (mul A B) = (det A)*(det B) := by
  simp[det,mul]
  ring

theorem inv_prod {A B : R22}
  : invertible A → invertible B → invertible (mul A B) := by
  intro h1 h2
  simp_all[invertible]
  intro h3
  simp[det_mul] at h3
  apply Or.elim h3
  . intro ha
    exact h1 ha
  . intro hb
    exact h2 hb

theorem smul_smul {m n :ℕ} {a b:ℂ} {A : Mat m n}
  : smul a (smul b A) = smul (a*b) A := by
  funext i j
  simp[smul]
  group

theorem adj_mul {A B: R22} : adj (mul A B) = mul (adj B) (adj A) := by
  simp[adj,mul]
  funext i j
  fin_cases i <;> fin_cases j <;> simp[mul] <;> ring;

theorem inv_mul {A B : R22}
  : invertible A → invertible B → inv (mul A B) = mul (inv B) (inv A) := by
  intro h1 h2
  have h3 := inv_prod h1 h2
  simp[inv,h1,h2,h3]
  simp[det_mul,smul_comm,←smul_comm2,smul_comm]
  simp[smul_smul,mul_comm,adj_mul]

theorem det_inv {A : R22} : invertible A → (inv A).det = 1 / A.det := by
  intro h
  simp[inv,h,det_smul,←det_adj]
  simp[invertible] at h
  calc (A.det ^ 2)⁻¹ * A.det
  _  = (A.det * A.det)⁻¹ * A.det := by
      field_simp
      exact Eq.symm (pow_two A.det)
  _  = (A.det⁻¹ * A.det⁻¹) * A.det := by simp[inv_mul]
  _  = A.det⁻¹ * (A.det⁻¹ * A.det) := by group
  _  = A.det⁻¹ * 1 := by field_simp
  _  = A.det⁻¹ := by group
