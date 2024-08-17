import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h₀ x xs
  simp
  exact h₀ ⟨x, xs, rfl⟩
  intro ssub y ⟨a, b, c⟩
  exact c ▸ ssub b

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
  ⟨
    λ h₀ ↦ λ x xs ↦ h₀ ⟨x, xs, rfl⟩,
    λ h₁ ↦ λ _ ⟨_, ys, ye⟩ ↦ ye ▸ h₁ ys
  ⟩

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := λ _ ⟨_, z, g⟩ ↦ (h g) ▸ z

example : f '' (f ⁻¹' u) ⊆ u := λ _ ⟨_, a, b⟩ ↦ b ▸ a

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) :=
  λ y yu ↦ (h y).elim
    λ x fxy ↦ ⟨x, ⟨fxy.symm.subst yu, fxy⟩⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := λ _ ⟨x, xs, xsy⟩ ↦ ⟨x, h xs, xsy⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := λ _ g ↦ h g

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := ext λ _ ↦ ⟨id, id⟩

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  λ _ ⟨_, xst, fxy⟩ ↦ ⟨⟨_, xst.1, fxy⟩, ⟨_, xst.2, fxy⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
  λ _ ⟨⟨x, sx, fxy⟩, ⟨_, tx', fx'y⟩⟩ ↦
    ⟨x, ⟨sx, (h (fx'y.trans fxy.symm)).subst tx'⟩, fxy⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
  λ _ ⟨yfs, nyft⟩ ↦ yfs.elim λ x ⟨xs, fxy⟩ ↦ ⟨x, ⟨xs, (nyft ⟨x, ·, fxy⟩)⟩, fxy⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := λ _ h ↦ h

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := λ _ ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
  ext λ _ ↦ ⟨
    (·.elim λ ⟨x, xs, fxy⟩ yv ↦ ⟨x, ⟨xs, fxy.symm.subst yv⟩, fxy⟩),
    (·.elim λ x' ⟨⟨x's, fx'v⟩, fx'y⟩ ↦ ⟨⟨x', x's, fx'y⟩, fx'y.subst fx'v⟩)
  ⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
  λ _ h ↦ Or.inr (h.elim λ _ ⟨⟨_, fxu⟩, fxy⟩ ↦ fxy.subst fxu)

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := λ x xh ↦ ⟨⟨x, ⟨xh.1, rfl⟩⟩, xh.2⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
  λ x xh ↦ xh.elim (Or.inl ⟨x, ·, rfl⟩) Or.inr

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, _, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } :=
  λ x xs y ys fxy ↦ by
    have h : sqrt x * sqrt x = sqrt y * sqrt y := by congr
    rw [mul_self_sqrt, mul_self_sqrt] at h
    exact h
    exact ys
    exact xs

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } :=
  λ x xs y ys fxy ↦ by
    dsimp at fxy
    rw [pow_two, pow_two] at fxy
    have h : sqrt (x * x) = sqrt (y * y) := by congr
    rw [sqrt_mul_self, sqrt_mul_self] at h
    exact h
    exact ys
    exact xs

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x; simp
  constructor
  rintro ⟨x₀, _, h⟩
  rw [← h]
  exact sqrt_nonneg x₀
  intro g
  use (x * x)
  constructor
  rw [← pow_two]
  exact sq_nonneg x
  exact sqrt_mul_self g

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp
  constructor
  rintro ⟨x, h⟩
  rw [← h]
  exact sq_nonneg x
  intro g
  use sqrt y
  exact sq_sqrt g
end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]; dsimp; rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨
    λ h x ↦ h (inverse_spec (f x) ⟨x, refl (f x)⟩),
    λ g₀ s t g₁ ↦ g₀ s ▸ g₀ t ▸ (congr (refl (inverse f)) g₁)
  ⟩


example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∉ S := h ▸ h₁
  contradiction

-- COMMENTS: TODO: improve this
end
