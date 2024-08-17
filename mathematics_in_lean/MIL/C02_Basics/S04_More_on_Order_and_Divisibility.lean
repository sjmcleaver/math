import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    rw [max_le_iff, le_max_iff, le_max_iff]
    simp

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  apply le_min

  calc
    min (min a b) c ≤ min a b := by apply min_le_left
    _ ≤ a := by apply min_le_left

  have h₀ : min (min a b) c ≤ b
  calc
    min (min a b) c ≤ min a b := by apply min_le_left
    _ ≤ b := by apply min_le_right

  have h₁ : min (min a b) c ≤ c := by apply min_le_right

  apply le_min_iff.2
  exact ⟨h₀, h₁⟩

  have g₀ : min a (min b c) ≤ c
  calc
    min a (min b c) ≤ min b c := by apply min_le_right
    _ ≤ c := by apply min_le_right

  have g₁ : min a (min b c) ≤ min a b := by
    have f₀ : min a (min b c) ≤ a := by apply min_le_left
    have f₁ : min a (min b c) ≤ b :=
    calc
      min a (min b c) ≤ min b c := by apply min_le_right
      _ ≤ b := by apply min_le_left
    apply le_min_iff.2
    exact ⟨f₀, f₁⟩

  apply le_min_iff.2
  exact ⟨g₁, g₀⟩


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min_iff.2
  have h₀ : min a b + c ≤ a + c := by
    apply add_le_add_right
    exact min_le_left a b

  have h₁ : min a b + c ≤ b + c := by
    apply add_le_add_right
    exact min_le_right a b

  exact ⟨h₀, h₁⟩

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  exact aux a b c

  rw [← add_neg_cancel_right (min (a + c) (b + c)) c, add_assoc, add_comm c, ← add_assoc]
  apply add_le_add_right
  apply le_min

  calc
    min (a + c) (b + c) + -c ≤ a + c + -c := by
      apply add_le_add
      exact min_le_left (a + c) (b + c)
      exact le_refl (-c)
    _ ≤ a := by
      rw [add_assoc, add_right_neg, add_zero]

  calc
    min (a + c) (b + c) + -c ≤ b + c + -c := by
      apply add_le_add
      exact min_le_right (a + c) (b + c)
      exact le_refl (-c)
    _ ≤ b := by
      rw [add_assoc, add_right_neg, add_zero]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← sub_add_cancel a b]
  have f : |a - b + b| ≤ |a - b| + |b| := by apply abs_add
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  apply dvd_mul_of_dvd_right
  apply dvd_mul_right
  apply dvd_mul_left
  apply dvd_trans h
  apply dvd_mul_left
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.gcd_greatest
  apply Nat.gcd_dvd_right
  apply Nat.gcd_dvd_left
  intro e h₀ h₁
  exact dvd_gcd h₁ h₀
end
