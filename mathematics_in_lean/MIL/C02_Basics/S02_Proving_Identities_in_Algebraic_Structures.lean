import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, add_left_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, ← neg_add_cancel_left a c, h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [add_comm, add_comm c b] at h
  rw [← add_left_cancel h]
  -- rw [← neg_add_cancel_left b a, ← neg_add_cancel_left b c, add_comm b a, h, add_comm b c]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have g : a + -a = a + b := by
    rw [add_comm, add_left_neg, h]
  rw [add_left_cancel g]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have g : a + b = -b + b := by
    rw [add_left_neg, h]
  rw [add_right_cancel g]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  rw [neg_eq_of_add_eq_zero]
  rw [add_left_neg]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a, add_comm, add_left_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_mul a, ← add_mul, one_add_one_eq_two, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have f : a⁻¹⁻¹ * 1 = a :=
    ((mul_left_inv a⁻¹) ▸ (mul_left_inv a) ▸ (mul_assoc a⁻¹⁻¹ a⁻¹ a)) ▸ (one_mul a)
  nth_rw 1 [← f]
  rw [mul_assoc, one_mul, mul_left_inv]

theorem mul_one (a : G) : a * 1 = a := by
  have h : a⁻¹ * (a * a⁻¹ * a) = a⁻¹ * a := by
    rw [mul_left_inv, mul_assoc, mul_left_inv, ← mul_assoc, mul_left_inv, one_mul]
  have g : a * a⁻¹ * a = a := by
    rw [mul_left_cancel h]
  rw [← mul_left_inv a, ← mul_assoc]
  exact g

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have f : (a * b) * (a * b)⁻¹ = (a * b) * (b⁻¹ * a⁻¹) := by
    rw [mul_right_inv, mul_assoc, ← mul_assoc b, mul_right_inv, ← mul_assoc]
    rw [mul_one, mul_right_inv]
  exact mul_left_cancel f

end MyGroup

end
