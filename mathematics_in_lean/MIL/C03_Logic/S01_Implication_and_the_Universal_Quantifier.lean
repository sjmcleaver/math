import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

-- theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
--   sorry

-- section
-- variable (a b δ : ℝ)
-- variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
-- variable (ha : |a| < δ) (hb : |b| < δ)

-- #check my_lemma a b δ
-- #check my_lemma a b δ h₀ h₁
-- #check my_lemma a b δ h₀ h₁ ha hb

-- end

-- theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
--   sorry

-- section
-- variable (a b δ : ℝ)
-- variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
-- variable (ha : |a| < δ) (hb : |b| < δ)

-- #check my_lemma2 h₀ h₁ ha hb

-- end

-- theorem my_lemma3 :
--     ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
--   intro x y ε epos ele1 xlt ylt
--   sorry


theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  have yle : |y| ≤ ε := (lt_iff_le_and_ne.1 ylt).1
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := mul_le_mul (le_refl |x|) yle (abs_nonneg y) (abs_nonneg x)
    _ < 1 * ε := (mul_lt_mul_right epos).2 (lt_of_lt_of_le xlt ele1)
    _ = ε := one_mul ε

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  λ x ↦ add_le_add (hfa x) (hgb x)

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  λ x ↦ mul_nonneg (nnf x) (nng x)

example (hfa : FnUb f a) (hfb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  λ x ↦ mul_le_mul (hfa x) (hfb x) (nng x) nna

end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun _ _ aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro x y h
  dsimp
  have h : 0 ≤ c * f y + c * (-(f x)) := by
    rw [← mul_add]
    apply mul_nonneg nnc
    linarith [mf h]
  linarith

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  λ _ _ h ↦ mf (mg h)

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [of, og]
  norm_num

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og]
  norm_num

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ef, neg_neg]

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := λ _ ↦ id

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
  λ h₀ h₁ _ h₂ ↦ h₁ (h₀ h₂)
end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  λ x g ↦ le_trans (h x g) h'

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x a
  dsimp
  rw [mul_comm, mul_comm c]
  exact (mul_left_inj' h).1

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) :=
  λ _ _ h ↦ injf (injg h)

end
