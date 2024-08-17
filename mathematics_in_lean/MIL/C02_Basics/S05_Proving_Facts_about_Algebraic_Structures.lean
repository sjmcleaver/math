import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  exact le_inf inf_le_right inf_le_left
  exact le_inf inf_le_right inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  exact le_trans inf_le_left inf_le_left
  apply le_inf
  apply le_trans inf_le_left inf_le_right
  exact inf_le_right
  apply le_inf
  apply le_inf
  exact inf_le_left
  exact le_trans inf_le_right inf_le_left
  exact le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  exact sup_le le_sup_right le_sup_left
  exact sup_le le_sup_right le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm

  apply sup_le
  apply sup_le
  exact le_sup_left
  exact le_trans le_sup_left le_sup_right
  exact le_trans le_sup_right le_sup_right

  apply sup_le
  exact le_trans le_sup_left le_sup_left
  apply sup_le
  exact le_trans le_sup_right le_sup_left
  exact le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  exact le_refl x
  exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  exact le_refl x
  exact inf_le_left
  exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  apply le_inf
  apply sup_le
  exact le_sup_left
  exact le_trans inf_le_left le_sup_right
  apply sup_le
  exact le_sup_left
  exact le_trans inf_le_right le_sup_right
  rw [h (a ⊔ b) a c, inf_comm, absorb1]
  apply sup_le
  exact le_sup_left
  rw [inf_comm, h c a b]
  apply sup_le
  apply le_trans inf_le_right le_sup_left
  rw [inf_comm]
  exact le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  rw [h (a ⊓ b) a c]
  have g₀ : (a ⊓ b ⊔ a) = a := by
    apply le_antisymm
    apply sup_le
    exact inf_le_left
    exact le_refl a
    exact le_sup_right
  rw [g₀]
  apply le_inf
  exact inf_le_left
  have g₁ : a ⊓ b ⊔ c = c ⊔ a ⊓ b := by rw[sup_comm]
  rw [g₁, h c a b]
  apply le_inf
  exact le_trans inf_le_left le_sup_right
  rw [sup_comm]
  exact inf_le_right
  apply le_inf
  apply sup_le
  exact inf_le_left
  exact inf_le_left
  apply sup_le
  exact le_trans inf_le_right le_sup_left
  exact le_trans inf_le_right le_sup_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example : a ≤ b → 0 ≤ b - a := by
  intro h
  rw [← add_left_neg a, sub_eq_add_neg, add_comm b]
  exact add_le_add_left h (-a)

example : 0 ≤ b - a → a ≤ b := by
  intro h

  have g : a + 0 ≤ a + (b - a) := add_le_add_left h a
  rw [add_zero, sub_eq_add_neg, add_comm b, ← add_assoc a, add_right_neg a, zero_add] at g
  exact g

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by

  have g : 0 ≤ b * c - a * c := by
    rw [← sub_mul]
    apply mul_nonneg
    rw [← add_left_neg a, sub_eq_add_neg, add_comm b]
    apply add_le_add_left h (-a)
    exact h'

  rw [← add_zero (a * c), ← zero_add (b * c)]
  nth_rw 2 [← add_left_neg (a * c)]
  rw [add_comm (-(a * c)) (a * c), add_assoc, add_comm (-(a * c)) (b * c), ← sub_eq_add_neg]
  apply add_le_add_left g (a * c)

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y * 2
  calc
    0 = dist x x := by rw [dist_self x]
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm]
    _ = 2 * dist x y := by rw [two_mul]
    _ = dist x y * 2 := by rw [mul_comm]

  exact nonneg_of_mul_nonneg_left h (two_pos)

end
