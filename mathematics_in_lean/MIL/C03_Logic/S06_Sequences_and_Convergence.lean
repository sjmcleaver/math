import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro _ _
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n h
  have r : |s n - a + (t n - b)| = |s n + t n - (a + b)| := by
    congr 1; ring
  have hε : ε / 2 + ε / 2 = ε := by norm_num
  apply r ▸ (lt_of_le_of_lt (abs_add (s n - a) (t n - b)))
  apply hε ▸ (add_lt_add ((hs n) (max_le_iff.1 h).1) ((ht n) (max_le_iff.1 h).2))

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, hN⟩
  use N
  intro n nN
  have j : |c| * |s n - a| < |c| * (ε / |c|) :=
    (mul_lt_mul_left acpos).2 ((hN n) nN)
  rw [← mul_sub, abs_mul]
  rw [mul_comm, mul_div, mul_comm |c|, ← mul_div, div_self, mul_one, mul_comm] at j
  exact j
  exact λ hc ↦ lt_irrefl 0 (hc ▸ acpos)

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nN
  have f := h n nN
  have g : |s n| - |a| < 1 := calc
    |s n| - |a| ≤ |s n - a| := abs_sub_abs_le_abs_sub (s n) a
    _ < 1 := f
  linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nN
  have u := h₀ n (max_le_iff.1 nN).1
  have v := h₁ n (max_le_iff.1 nN).2
  rw [← mul_zero (s n), ← mul_sub, abs_mul]
  have w := (mul_lt_mul'' u v) (abs_nonneg (s n)) (abs_nonneg (t n - 0))
  rw [mul_comm, mul_div, mul_comm B, ← mul_div, div_self, mul_one, mul_comm] at w
  exact w
  linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  by_contra anb
  have : |a - b| > 0 := by
    by_contra le
    have : |a - b| = 0 := by
      linarith[le_of_not_gt le, abs_nonneg (a - b)]
    rw [abs_eq_zero] at this
    apply anb
    linarith
  have : |a - b| / 2 > 0 := by linarith
  rcases sa (|a - b| / 2) this with ⟨N₀, nN₀⟩
  rcases sb (|a - b| / 2) this with ⟨N₁, nN₁⟩
  have h₀ : _ := nN₀ (max N₀ N₁) (le_max_left N₀ N₁)
  have h₁ : _ := nN₁ (max N₀ N₁) (le_max_right N₀ N₁)
  have h₂ : |s (max N₀ N₁) - a| = |a - s (max N₀ N₁)| := by
    rw [← abs_neg (a - s (max N₀ N₁))]
    ring_nf
  have g : |a - b| < |a - b| :=
  calc
    |a - b| = |a - b + (s (max N₀ N₁) - s (max N₀ N₁))| := by
      rw [sub_self (s (max N₀ N₁)), add_zero]
    _ = |a - s (max N₀ N₁) + (s (max N₀ N₁) - b)| := by ring_nf
    _ ≤ |a - s (max N₀ N₁)| + |s (max N₀ N₁) - b| :=
      abs_add (a - s (max N₀ N₁)) (s (max N₀ N₁) - b)
    _ = |s (max N₀ N₁) - a| + |s (max N₀ N₁) - b| := by rw [h₂]
    _ < |a - b| / 2 + |a - b| / 2 := by
      apply add_lt_add h₀ h₁
    _ = |a - b| := by linarith
  exact lt_irrefl |a - b| g


-- theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
--       (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
--     a = b := by
--   by_contra abne
--   have : |a - b| > 0 := by sorry
--   let ε := |a - b| / 2
--   have εpos : ε > 0 := by
--     change |a - b| / 2 > 0
--     linarith
--   rcases sa ε εpos with ⟨Na, hNa⟩
--   rcases sb ε εpos with ⟨Nb, hNb⟩
--   let N := max Na Nb
--   have absa : |s N - a| < ε := by sorry
--   have absb : |s N - b| < ε := by sorry
--   have : |a - b| < |a - b| := by sorry
--   exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end