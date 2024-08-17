import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

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

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro ub
  rcases ub with ⟨B, h₀⟩
  rcases h B with ⟨x, h₁⟩
  have : B ≤ f x := h₀ x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro ub
  rcases ub with ⟨b, hb⟩
  have : b + 1 ≤ b := hb (b + 1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro ageb
  have : f b ≤ f a := h ageb
  linarith

example (h : Monotone f) (h' : f a < f b) : a < b :=
  lt_of_not_ge (λ ageb ↦ not_lt_of_ge (h ageb) h')

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f :=
  λ mf ↦ not_lt_of_ge (mf h) h'

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := λ a b _ ↦ le_refl _
  have h' : f 1 ≤ f 0 := le_refl _
  have : 1 ≤ 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
  le_of_not_gt (λ xpos ↦ lt_irrefl x (h x xpos))

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := λ x₀ px₀ ↦ h ⟨x₀, px₀⟩

example (h : ∀ x, ¬P x) : ¬∃ x, P x := λ ⟨x₀, px₀⟩ ↦ h x₀ px₀

example (h : ¬∀ x, P x) : ∃ x, ¬P x :=
  not_not.1 (λ h' ↦ h (λ x ↦ not_not.1 (λ npx ↦ h' ⟨x, npx⟩)))

example (h : ∃ x, ¬P x) : ¬∀ x, P x :=
  λ pxu ↦ match h with | ⟨x, npx⟩ => npx (pxu x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := Function.eval h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  exact h' ⟨x, h''⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  rcases h with ⟨x, h'⟩
  rcases h' with ⟨y, h''⟩
  exact ⟨x, y, h''⟩

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
  have _ : ¬0 < 0 := lt_irrefl 0
  contradiction

end
