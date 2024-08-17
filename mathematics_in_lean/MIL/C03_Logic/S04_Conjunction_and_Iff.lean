import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, λ h ↦ h₁ (h ▸ h₀)⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
      contrapose! h₁
      exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  ⟨h.1, λ ndm ↦ h.right (dvd_antisymm h.1 ndm)⟩

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  ⟨
    λ h₀ ↦ ⟨h₀.1, λ h₁ ↦ (h₁ ▸ h₀.2) (le_refl y)⟩,
    λ g₀ ↦ ⟨g₀.1, λ g₁ ↦ g₀.2 (le_antisymm g₀.1 g₁)⟩
  ⟩

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have h₀ : x ^ 2 = 0 := by
    by_contra h₁
    have h₂: x ^ 2 > 0 := lt_iff_le_and_ne.2 ⟨pow_two_nonneg x, λ g ↦ h₁ g.symm⟩
    exact (lt_iff_le_and_ne.1 (add_pos_of_pos_of_nonneg h₂ (pow_two_nonneg y))).right h.symm
  exact pow_eq_zero h₀

-- theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
--   have h₀ : x ^ 2 = 0 := by
--     by_contra h₁
--     have h₂: x ^ 2 > 0 := lt_iff_le_and_ne.2 ⟨pow_two_nonneg x, λ g ↦ h₁ g.symm⟩
--     have h₃ : x ^ 2 + y ^ 2 > 0 := add_pos_of_pos_of_nonneg h₂ (pow_two_nonneg y)
--     exact (lt_iff_le_and_ne.1 h₃).right h.symm
--   exact pow_eq_zero h₀

-- theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
--   have h' : x ^ 2 = 0 := by
--     apply le_antisymm
--     apply le_of_not_gt
--     intro x2pos
--     have g : x ^ 2 + y ^ 2 > 0 := add_pos_of_pos_of_nonneg x2pos (pow_two_nonneg y)
--     exact (lt_iff_le_and_ne.1 g).right h.symm
--     exact pow_two_nonneg x
--   pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  ⟨
    λ h ↦ ⟨aux h, aux (add_comm (x ^ 2) (y ^ 2) ▸ h)⟩,
    λ ⟨g₀, g₁⟩ ↦ by rw [g₀, g₁]; norm_num
  ⟩

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  intro h₀
  have h₁: (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have h₂: -0 ≤ -1 := h₀ h₁
  linarith

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  exact ⟨
    λ ⟨h₀, h₁⟩ ↦ ⟨h₀, λ h₂ ↦ h₁ (le_antisymm_iff.1 h₂).2⟩,
    λ ⟨g₀, g₁⟩ ↦ ⟨g₀, λ g₂ ↦ g₁ (le_antisymm_iff.2 ⟨g₀, g₂⟩)⟩
  ⟩

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  intro h
  exact h.2 h.1

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  intro h₀ h₁
  exact ⟨le_trans h₀.1 h₁.1, λ h₃ ↦ h₁.2 (le_trans h₃ h₀.1)⟩

end
