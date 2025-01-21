
/- # EXTENDED EXAMPLE: ART GALLERY PROBLEM

     / B —— E —— F
   A   |    |
     \ C —— D

-/

structure Museum where
  Location : Type
  Guarded : Location → Prop
  Adjacent : Location → Location → Prop
  Sym : ∀ x y , Adjacent x y → Adjacent y x

def Seen {M : Museum}
  (x : M.Location)
  := M.Guarded x ∨ ∃ y , M.Adjacent x y ∧ M.Guarded y

def Safe (M : Museum) := ∀ x : M.Location, Seen x











/- # STAR SHAPED MUSEUMS -/

def IsStar (M : Museum) := ∃ center, M.Guarded center
                         ∧ ∀ x, x = center ∨ M.Adjacent center x

example (M : Museum) : IsStar M → Safe M := by
  intro h1
  apply Exists.elim h1
  intro center ⟨ h3, h4 ⟩ x
  have h5 := h4 x
  apply Or.elim h5
  . intro h6
    rw[h6]
    exact Or.inl h3
  . intro h7
    apply Or.inr
    apply Exists.intro center
    apply And.intro
    . exact M.Sym center x h7
    . exact h3





/- # COMPLETE MUSEUMS -/

def IsComplete (M : Museum) :=
  (∀ x y, x = y ∨ M.Adjacent x y) ∧ ∃ z , M.Guarded z

example (M : Museum): IsComplete M → Safe M := by
  intro ⟨ hadj, hg ⟩ x
  apply Exists.elim hg
  intro y hy
  have h := hadj x y
  apply Or.elim h
  . intro hxy
    rw[hxy]
    exact Or.inl hy
  . intro hxy
    apply Or.inr
    apply Exists.intro y
    exact ⟨ hxy, hy ⟩






/- # INFINITE MUSEUMS -/

def G (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ x => ¬G x

def InfMuseum : Museum := {
  Location := Nat,
  Guarded := λ n => match n with
    | Nat.zero => True
    | Nat.succ x => ¬G x
  Adjacent := λ x y => x = y.succ ∨ y = x.succ,
  Sym := by
    intro x y h
    exact id (Or.symm h)
}

example : Safe InfMuseum := by
  intro x
  cases x with
  | zero => exact Or.inl trivial
  | succ y =>
    by_cases h : InfMuseum.Guarded y
    . apply Or.inr
      apply Exists.intro y
      apply And.intro
      . apply InfMuseum.Sym y y.succ
        exact Or.inr rfl
      . exact h
    . apply Or.inl
      match y with
      | Nat.zero => exact h
      | Nat.succ z => exact h

example : Safe InfMuseum := by
  intro x
  induction x with
  | zero => exact Or.inl trivial
  | succ y ih =>
    apply Or.elim ih
    . intro hgy
      apply Or.inr
      apply Exists.intro y
      apply And.intro
      . apply InfMuseum.Sym y y.succ
        exact Or.inr rfl
      . exact hgy
    . intro hgsy
      apply Exists.elim hgsy
      intro z ⟨ h1, h2 ⟩
      apply Or.elim h1
      . sorry
      . sorry
