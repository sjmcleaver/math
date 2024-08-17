import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match lt_or_ge x 0 with
    | Or.inl lt =>
      rw [abs_of_neg lt]
      exact le_neg_self_iff.2 (lt_iff_le_and_ne.1 lt).1
    | Or.inr gt =>
      rw [le_iff_lt_or_eq]
      right
      exact (abs_of_nonneg gt).symm

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  match le_or_gt x 0 with
    | Or.inl le =>
      rw [le_iff_lt_or_eq]
      right
      exact (abs_of_nonpos le).symm
    | Or.inr gt =>
      rw [le_iff_lt_or_eq]
      left
      rw [abs_of_pos gt]
      exact neg_lt_self gt

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact match le_or_gt 0 (x + y) with
    | Or.inl le =>
       ((abs_of_nonneg le).symm ▸ add_le_add (le_abs_self x) (le_abs_self y))
    | Or.inr gt =>
       (abs_of_neg gt).symm ▸
        ((neg_add x y) ▸ add_le_add (neg_le_abs_self x) (neg_le_abs_self y))

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y :=
  ⟨
    λ g₀ ↦
      Or.casesOn (le_or_gt 0 y)
        (λ f₀ ↦ Or.inl (abs_of_nonneg f₀ ▸ g₀))
        (λ f₁ ↦ Or.inr (abs_of_neg f₁ ▸ g₀)),
    λ g₁ ↦
      Or.casesOn g₁
        (λ h₀ ↦ lt_of_lt_of_le h₀ (le_abs_self y))
        (λ h₁ ↦ lt_of_lt_of_le h₁ (neg_le_abs_self y))
  ⟩

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  have h₀ : |x| < y → -y < x ∧ x < y := by
    intro g₀
    have g₁ : x < y := lt_of_le_of_lt (le_abs_self x) g₀
    have g₂ : -y < -x := by
      calc
        -y = -y + -x + x := by
          rw [add_assoc, add_left_neg, add_zero]
        _ < -y + -x + y := by
            apply add_lt_add_of_le_of_lt
            exact le_refl (-y + -x)
            exact g₁
        _ = -x := by linarith

    have g₃ : -y < x := by
      match le_or_gt 0 x with
        | Or.inl le =>
          calc
            -y < -x := g₂
            _  ≤ |x| := neg_le_abs_self x
            _ = x := abs_of_nonneg le
        | Or.inr gt =>
          rw [abs_of_neg] at g₀
          calc
            -y = x + -y + -x := by
              rw [add_comm, ← add_assoc, add_left_neg, zero_add]
            _ < x + -y + y := by
              apply add_lt_add_of_le_of_lt
              exact le_refl (x - y)
              exact g₀
            _ = x := by
              rw [add_assoc, add_left_neg, add_zero]
          linarith
    exact ⟨g₃, g₁⟩

  have h₁ : -y < x ∧ x < y → |x| < y := by
    intro f₀
    match le_or_gt 0 x with
      | Or.inl le =>
        rw [abs_of_nonneg le]
        exact f₀.2
      | Or.inr gt =>
        rw [abs_of_neg gt]
        calc
          -x = -y + (y + -x) := by rw [← add_assoc, add_left_neg, zero_add]
          _ < x + (y + -x) := by
            apply add_lt_add_of_lt_of_le
            exact f₀.1
            exact le_refl (y + -x)
          _ = y := by rw [← add_assoc, add_comm, ← add_assoc, add_left_neg, zero_add]

  exact ⟨h₀, h₁⟩


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, ⟨h₀, rfl⟩ | ⟨h₁, rfl⟩⟩ <;> linarith[pow_two_nonneg x, pow_two_nonneg y]

lemma sq_eq_or_neg {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g₀ : (x - y) * (x + y) = 0 := by linarith[h]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g₀ with f₀ | f₁
  left; linarith[f₀]; right; linarith[f₁]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  apply sq_eq_or_neg
  linarith [h]

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)


lemma sq_eq_or_neg' (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g₀ : (x - y) * (x + y) = 0 := by ring; rw [h, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g₀ with f₀ | f₁
  left
  rw [← sub_self y, sub_eq_add_neg, sub_eq_add_neg] at f₀
  exact add_right_cancel_iff.1 f₀
  right
  rw [← sub_self y, sub_eq_add_neg, add_comm] at f₁
  exact add_left_cancel_iff.1 f₁

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  apply sq_eq_or_neg'
  rw [pow_two 1, mul_one]
  exact h

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro pq
  exact match em P with
    | Or.inl p => Or.inr (pq p)
    | Or.inr np => Or.inl np
  intro npq
  exact match em Q with
    | Or.inl q => λ _ ↦ q
    | Or.inr nq => match npq with
      | Or.inl np => λ p ↦ absurd p np
      | Or.inr q => absurd q nq
