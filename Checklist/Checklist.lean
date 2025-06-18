import Mathlib
import Checklist.Auxiliary

-- [C9] most basic example
theorem C9 : 1 = 1 := by sorry

-- [QU] `sorry` used as a term
theorem QU : 1 = 1 := sorry

-- [AF] `sorry` in a have statement
theorem AF : 1 = 1 := by
  have h : 1 = 1 := by sorry
  assumption

-- [PP] `sorry` term in constructor brackets
theorem PP : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (rfl) (by sorry) n

-- [HJ] term variant of ex4
theorem HJ : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (rfl) (sorry) n

-- [R3] two `sorry` on same line
theorem R3 : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (by sorry) (by sorry) n

-- [LP] `sorry` in an indented focus block
theorem LP (n : ℕ) : n = n := by
  induction n
  · rfl
  · sorry


-- [EG]: essential definition outside theorem statement
def f : ℝ → ℝ := fun x ↦ x + 30

theorem EG : ∃ x : ℝ, f x = 100 := by sorry

-- [WX] essential definition in imported file
theorem WX : ∃ x : ℝ, g x = 100 := by sorry

-- [SR] essential definition in transitive import
theorem SR : ∃ x : ℕ, h x = 100 := by sorry

-- [GM]: `sorry` requiring disambiguating namespaces
namespace first
def k : ℝ → ℝ := fun x ↦ x + 77
end first

namespace second
def k : ℝ → ℝ := fun x ↦ x + 19
end second

namespace third
def k : ℝ → ℝ := fun x ↦ x + 6
end third

section
open second
theorem GM : ∃ x : ℝ, k x = 100 := by sorry
end

-- [KM] direct application of imported theorem; warning: this can ALSO be proven directly
theorem KM (n : ℕ) (m : ℕ) :
    Nat.factorial (n + m + 2) ≥ Nat.factorial (n + 1) * Nat.pow 2 (m + 1) :=
  by exact factorial_inequality n (m + 1)
