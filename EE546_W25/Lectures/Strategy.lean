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
 -                         **PROJECT STRATEGY IDEAS**
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


import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs



/- # WORK BACK FROM YOUR GOAL

  1. Can you express your goal?

    a. No. The data types provided by Mathlib are too hard to understand
      i.Learn the data types by doing the simplest problems you can
      ii.Make your own version of the data type (e.g. how I did with Reals.lean)
      iii. State a special case of the goal (e.g. using a 2x2 matrix)
    b. No. Mathlib doesn't even have the data types
      i. Maybe your project should be to make the new data type and prove basic theorems (e.g. FSMs)

  2. Can you express your goal but not prove it?

    a. Mathlib doesn't have enough supporting theorems
      i. When you get stuck, break out the current step to a theorem and prove that
    b. Mathlib's has the theorems, but they are hard to understand
      i. Try to make standalone simple examples that use the theorems
    c. Everything is there, but you can't figure it out
      i. Make sure you can prove your theorem by hand
      ii. Back up and try a more specific example

-/



/- # EXAMPLE: MATRIX EXPONENTIALS

  - Can I show something like A*B = B*A → e^A*e^B = e^(A+B)

    - By searching for 15 minutes, it is already in Mathlib!
      - Matrix.exp_add_of_commute
      - Can I use it to prove an example with actual numbers
        - Define C22 = Matrix (Fin 2) (Fin 2) ℂ
        - Seems like it wants C22 to be a Ring, which I though it was
          - Oh, you can't use def C22. Drop that.
        - Now exp_add_of_commute is not unifying
           - Oh, I have a typo B*B should be B+B. -/


namespace ex1
open NormedSpace

def B : Matrix (Fin 3) (Fin 3) ℂ  := !![1,2,1;0,3,4;1,2,3]

example : (exp ℂ (B+B)) = (exp ℂ B) * (exp ℂ B) := by
  apply Matrix.exp_add_of_commute
  rfl





/- # EXAMPLE: SIMILARITY AND MATRIX EXPONENTIALS

  - Can I show A = P * B * P⁻¹ → exp ℂ A = P * (exp ℂ B) * P⁻¹

      - Basically equivalent to Matrix.exp_conj
      - Needs IsUnit? What's that?
        - Found isUnit_iff_exists, which says P needs an inverse
        - Need to show P⁻¹*P = 1. This seems like something that ought
          to be built in. But inv_mul_cancel wants more than P specified
          as having nz det, but it needs to be in a multiplicative group,
          in this case the General Linear Group, GL.
        - Oh, but if you simp[hp] it figures it out. How?? -/

example (n:ℕ) (A B P : Matrix (Fin n) (Fin n) ℂ) (hp : P.det ≠ 0)
  : A = P * B * P⁻¹ → exp ℂ A = P * (exp ℂ B) * P⁻¹ := by
  intro h
  have iu : IsUnit P := by
    simp[isUnit_iff_exists]
    use P⁻¹
    simp[hp]
  calc exp ℂ A
  _  = exp ℂ (P * B * P⁻¹) := by rw[h]
  _  = P * (exp ℂ B) * P⁻¹ := by apply Matrix.exp_conj; exact iu

end ex1







/- # HOW ABOUT EIGENVALUES?

        - Let's try to show eigs of A = eigs of Aᵀ.
          - Mathlib.LinearAlgebra.Eigenspace.Basic and ... Matrix don't
            seem to say anything about matrices
          - Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs.lean seems pretty
            sparce.
          - There is surprisingly little about eigenvalues to be found in Mathlib!
        - Hmm, ok. How about trying to do defining everything myself? -/














/- # WHAT IS A MATRIX ANYWAY? -/

#check (Fin 3)

def Vect (n:ℕ) := (Fin n) → ℂ

def Mat (m n: ℕ) := (Fin m) → (Fin n) → ℂ














/- # HOW ARE OPERATIONS DEFINED? -/

def smul {m n: ℕ} (a:ℂ) (M: Mat m n) := λ i j => a * (M i j)

noncomputable
def mul {m n p:ℕ} (A : Mat m n) (B: Mat n p) : Mat m p :=
  λ i j => ∑ k : (Fin n), (A i k) * (B k j)

def add {m n :ℕ} (A : Mat m n) (B: Mat m n) : Mat m n :=
  λ i j => A i j + B i j

def sub {m n :ℕ} (A : Mat m n) (B: Mat m n) : Mat m n :=
  λ i j => A i j - B i j

def transpose {m n : ℕ} (A : Mat m n) : Mat n m := λ i j => A j i










/- # CAN I DO AN EXAMPLE? -/

def A : Mat 2 2 := λ i j => i+j
def B : Mat 2 1 := λ i j => 1

example : smul 2 (mul A B)  = !![2;6] := by
  funext U V
  simp[A,B,smul,mul]
  fin_cases U <;> fin_cases V <;> dsimp
  . ring
  . ring













/- # HOW DO EIGENVALUES WORK FOR nxn MATRICES

  After a lot of digging, it seems like Mathlib doesn't handle this very well.

  I could define eigenvalues in general, but I'm not sure I am ready.

  How about jsut 2x2 matrices?

-/
















/- # 2x2s -/

def R22 := Mat 2 2

namespace R22

def zero : R22 := !![0,0;0,0]

def one : R22 := !![1,0;0,1]

def det (A : R22) : ℂ := (A 0 0)*(A 1 1)-(A 0 1)*(A 1 0)

noncomputable
def invertible (A : R22) : Bool := A.det ≠ 0

def adj (A : R22) : R22 := !![  -- Oh, cool. Mathlib's !![] notation
  A 1 1, -A 0 1;                -- is not matrix specific, It's just
 -A 1 0,  A 0 0                 -- shorthand for functions that we
]                               -- list out the possibilites for.

noncomputable
def inv (A : R22) : R22 :=
  if invertible A then smul (1/A.det) A.adj else zero









/- # FINALLY, SOME EIGENVALUES -/

def char_poly (s:ℂ) (A : R22) := det (sub (smul s one) A)

def is_eigenval (s:ℂ) (A : R22) := char_poly s A = 0

example : is_eigenval 4 !![2,3;2,1] := by
  simp[is_eigenval,char_poly,det,sub,smul,one]
  ring
















/- # OK, CAN I STATE MY GOAL? -/

theorem eigen_tr_fail {s:ℂ} {A : R22}
  : is_eigenval s A ↔ is_eigenval s (transpose A) := by
  simp[is_eigenval]
  sorry

/- Hmm. This amounts to showing that a matrix and its transpose have the same characteristic polynomial. -/

theorem char_poly_tr (s:ℂ) (A : R22)
  : char_poly s A = char_poly s (transpose A) := by
  simp[char_poly,det,smul,mul,sub,one,transpose,mul_comm]

theorem eigen_tr {s:ℂ} {A : R22}
  : is_eigenval s A ↔ is_eigenval s (transpose A) := by
  simp[is_eigenval]
  rw[char_poly_tr]









/- # THEN I JUST STARTED HAVING FUN

If you are working with matrices, I encourage you to try these. I put the solutions
in LinAlg.lean
 -/


theorem adj_off_diag (A B : R22)
  : (B = mul A A.adj) → (B 0 1 = 0 ∧ B 1 0 = 0) := sorry

theorem adj_diag {A B : R22}
  : (B = mul A A.adj) → (B 0 0 = A.det ∧ B 1 1 = A.det) := sorry

theorem mul_by_adj_right {A: R22}
  : (mul A A.adj) = !![A.det,0; 0, A.det] := sorry

theorem mul_by_adj_left {A: R22}
  : (mul A.adj A) = !![A.det,0; 0, A.det] := sorry

theorem adj_comm {A :R22}
  : mul A A.adj = mul A.adj A := sorry







/- # I LEARNED SOMETHING ABOUT HOW TO PROVE THINGS ABOUT MATRICES-/


theorem smul_comm (A B:R22) {a:ℂ}
  : mul A (smul a B) = smul a (mul A B) := by
    funext i j                               -- remember, matrices are functions
    simp[mul,smul]
    fin_cases i <;> fin_cases j <;> ring     -- apply ring to each i,j pair


















/- # OTHER THEOREMS USE MY PREVIOUS THEOREMS -/

theorem smul_comm2  {A B: R22} {a:ℂ}
  : mul A (smul a B) = mul (smul a A) B := sorry

theorem mul_assoc {A B C: R22}
  : mul A (mul B C) = mul (mul A B) C := sorry

theorem inv_comm {A : R22}
  : invertible A → mul A A.inv = mul A.inv A := by  -- it is satisfiying to use your
  intro h                                           -- own simplification rules!
  simp[inv,h]
  calc mul A (smul A.det⁻¹ A.adj)
  _  = smul A.det⁻¹ (mul A A.adj) := by simp[smul_comm]
  _  = smul A.det⁻¹ (mul A.adj A) := by simp[adj_comm]
  _  = mul A.adj (smul A.det⁻¹ A) := by simp[smul_comm]
  _  = mul (smul A.det⁻¹ A.adj) A := by simp[smul_comm2]

theorem mul_inv_right {A : R22}
  : invertible A → mul A A.inv = one := sorry

theorem mul_inv_left (A : R22)
 : invertible A → mul A.inv A = one := sorry









/- # SUMS

  Then I started wondering how sums work. I actually started thing about this when I defined matrix multiplication, above. It uses ∑.

  First, I jsut started playing with sums. -/

#check ∑ i : (Fin 100) , (i:ℕ)       -- Guass would be proud (or would he?)
#eval ∑ i : Fin (0 + 1), ↑i
#eval 0 + 1 + ∑ i : Fin 0, ↑i
#eval ∑ i ∈ Finset.range 4 , i













/- # PROVING A BASIC RESULT

  My goal was to show S(n) = sum(i=1 to n) = n(n+1)/2.

  I remembered that they way to do this was to separate the sum:

    S(n+1) = n+1 + S(n)

  so first I tried that.

  - I spend a long time hacking, only to find out its in the library.
  - I also found out I needed to use Finset.range instead of Fin, because that's
    how the library uses it. -/

theorem sep {f : ℕ → ℕ} (n:ℕ)
  : ∑ i ∈ Finset.range (n+1) , f i = f n + ∑ i ∈ Finset.range n, f i := by
  exact Finset.sum_range_succ_comm f n



















/- # NEXT I TRIED ANOTHER, SEEMINGLY INNOCUOUS RESULT

  sum (i * a) = (sum i) * a

I am sure there has to be a simpler way to do this. One of the main problems, as we found with the Cauchy proofs, is converting between different number systems. -/

theorem helper {a b c: ℕ} (q:ℚ) : a+b = c → (↑a+↑b)*q = (↑c)*q := by
  intro h
  let d := a+b
  have h1 : (d:ℚ) = (a:ℚ)+(b:ℚ) := by exact Nat.cast_add a b
  have : d*q = c*q := by exact congrFun (congrArg HMul.hMul (congrArg Nat.cast h)) q
  have : (a+b)*q = c*q := by exact Mathlib.Tactic.Ring.mul_congr (id (Eq.symm h1)) rfl this
  exact this







/- # WITH THAT HELPER I COULD SHOW MY RESULT -/

theorem sum_mul {a:ℚ} {n:ℕ}
  : ∑ i ∈ Finset.range (n+1), (i * a) = (∑ i ∈ Finset.range (n+1), i) * a := by
  induction n with
  | zero => simp
  | succ k ih =>
    let f := λ q : ℕ => q * a
    let idq := λ q : ℕ => (q : ℚ)
    have : ∑ i ∈ Finset.range (k + 1), ↑i * a = ∑ i ∈ Finset.range (k + 1), f i := by exact
      rfl
    calc ∑ i ∈ Finset.range (k + 1 + 1), ↑i * a
    _  = ∑ i ∈ Finset.range (k + 1 + 1), f i := by simp[this]
    _  = f (k+1) + ∑ i ∈ Finset.range (k + 1), f i := by
         exact Finset.sum_range_succ_comm f (k+1)
    _  = f (k+1) + ∑ i ∈ Finset.range (k + 1), i * a := by rfl
    _  = f (k+1) + (∑ i ∈ Finset.range (k + 1), i ) * a := by rw[ih]
    _  = (k+1) * a + (∑ i ∈ Finset.range (k + 1), i ) * a := by simp[f]
    _  = ( (k+1) + (∑ i ∈ Finset.range (k + 1), i ) ) * a := by linarith
    _  = ( id (k+1) + (∑ i ∈ Finset.range (k + 1), id i ) ) * a := by simp
    _  = (∑ i ∈ Finset.range (k + 1 + 1), id i ) * a := by
         have w1 := Eq.symm (Finset.sum_range_succ_comm id (k+1))
         have w2 : (id (k + 1) + ∑ x ∈ Finset.range (k + 1), id x)*a = (∑ x ∈ Finset.range (k + 1 + 1), id x)*a := by
           have w3 := helper a w1
           exact w3
         rw[←w2]




/- # BETTER SUMS?

  The built in ∑ relies on multisets and works for any indexing type. It is super general.
  This made me wonder if there is a better way to define sums that doesn't have to be so general.
  Actually, we did this in HW3!!  -/

def my_sum (f : ℕ → ℚ) (n:ℕ) := match n with
  | Nat.zero => f 0
  | Nat.succ k => f k + my_sum f k

#eval my_sum (λ i => i) 10

theorem my_sep {f : ℕ → ℚ} (n:ℕ)
  : my_sum f (n+1) = f n + my_sum f n := by
  induction n with
  | zero => simp[my_sum]
  | succ k ih =>
    unfold my_sum
    rw[ih]                --- boom!

theorem my_sum_mul {a:ℚ} {n:ℕ}
  : my_sum (λ i => i*a) n = a * my_sum (λ i => i) n := by
  induction n with
  | zero => simp[my_sum]
  | succ k ih => calc my_sum (fun i ↦ ↑i * a) (k + 1)
  _ = k*a + my_sum (fun i ↦ ↑i * a) k := by rw[my_sep]
  _ = k*a + a * my_sum (fun i ↦ ↑i) k := by rw[ih]
  _ = a * (k + my_sum (fun i ↦ ↑i) k) := by ring
  _ = a * (my_sum (fun i ↦ ↑i) (k+1)) := by rw[←my_sep] -- yowza!





/- # THOUGHTS

  - So now I'm wondering if the Mathematacians programing Mathlib have our best interests in mind?

  - Maybe we need to make EngrLib?

-/
