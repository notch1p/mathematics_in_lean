import MIL.Common
import Mathlib.Data.Real.Basic
import Paperproof

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

example {p} : p -> ¬p -> 0 = 1
  | p, np => False.elim (np p)

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  λ ⟨a', f'lb⟩ =>
    have ⟨a'', p⟩ := h a'
    have np := not_lt_of_ge (f'lb a'')
    show False from np p

example : ¬FnHasUb fun x ↦ x :=
  λ ⟨a, h⟩ =>
    have : a + 1 > a := lt_add_one _
    let p := h (a + 1)
    let np := not_le_of_gt this
    absurd p np

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h' (not_lt_of_ge (h h''))


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hf
  have h'' := hf h
  apply absurd h' (not_lt_of_ge h'')

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro i j ilej
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) <= 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  let h'' := h x h'
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x px
  have : ∃ x, P x := ⟨x, px⟩
  apply absurd this h

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, h'⟩
  apply absurd h' (h x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  push_neg at h
  assumption

#check Classical.byContradiction

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro p
  rcases h with ⟨w, h⟩
  apply absurd (p w) h

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩


example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'

example (h : Q) : ¬¬Q := by
  intro h'
  solve_by_elim

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro x
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  by_contra h'
  have _ := h x
  solve_by_elim

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  assumption

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
