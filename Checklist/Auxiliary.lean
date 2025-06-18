import Mathlib
import Checklist.Auxiliary2

/-
  Definitions imported in the checklist file
-/

def g : ℝ → ℝ  := fun x ↦ x + 49

theorem factorial_inequality (n : ℕ) (m : ℕ) :
    Nat.factorial (n + m + 1) ≥ Nat.factorial (n + 1) * Nat.pow 2 m := by
  induction m with
  | zero => simp only [add_zero, Nat.pow_eq, pow_zero, mul_one, ge_iff_le, le_refl]
  | succ m ih =>
    rw [Nat.factorial_succ]
    have h : 2 ≤ n + m + 2 := by linarith
    calc
    _ = (n + m + 2) * (n + m + 1).factorial  := by rfl
    _ ≥ (n + m + 2) * ((n + 1).factorial * Nat.pow 2 m) := Nat.mul_le_mul_left (n + m + 2) ih
    _ ≥ 2 * ((n + 1).factorial * Nat.pow 2 m) := Nat.mul_le_mul_right _ h
    _ = (n + 1).factorial * ((Nat.pow 2 m) * 2) := by ring
    _ = (n + 1).factorial * Nat.pow 2 (m + 1) := by rfl
