import Mathlib
import Checklist.Auxiliary

-- [C9] most basic example; "rfl"
theorem C9 : 1 = 1 := by sorry


-- [QU] `sorry` used as a term; "by linarith"
theorem QU (n : ℕ) (h : 2 * n < 7) : n ≤ 3 := sorry

-- [AF] `sorry` in a have statement; "rfl"
theorem AF : 1 = 1 := by
  have h : 1 = 1 := by sorry
  assumption



-- [PP] `sorry` tactic in function argument "intro n h; rfl"
theorem PP : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (rfl) (by sorry) n

-- [HJ] `sorry` tactic in function argument "by intro n h; rfl"
theorem HJ : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (rfl) (sorry) n

-- [R3] two `sorry` on same line; "rfl" and "intro n h; rfl"
theorem R3 : ∀ n : ℕ, n = n := fun n ↦ Nat.rec (by sorry) (by sorry) n

-- [LP] `sorry` in an indented focus block
theorem LP (n : ℕ) : n = n := by
  induction n
  · rfl
  · sorry


-- [EG]: essential definition outside theorem statement
-- proof string: "use 70; unfold f; norm_num"
def f : ℝ → ℝ := fun x ↦ x + 30

theorem EG : ∃ x : ℝ, f x = 100 := by sorry

-- [WX] essential definition in imported file
-- proof string: "use 51; unfold g; norm_num"
theorem WX : ∃ x : ℝ, g x = 100 := by sorry

-- [SR] essential definition in transitive import
-- proof string: "use 68; unfold h; norm_num"
theorem SR : ∃ x : ℝ, h x = 100 := by sorry

-- [GM]: `sorry` requiring interpretation of namespaces
-- proof string: "use 81; unfold k; norm_num"
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

-- [KM] solved by exact? because of auxiliary imports
-- proof string "exact factorial_inequality n (m + 1)"
theorem KM (n : ℕ) (m : ℕ) :
    Nat.factorial (n + m + 2) ≥ Nat.factorial (n + 1) * Nat.pow 2 (m + 1) :=
  by sorry

-- [KP] mathlib statement, solved by exact?
-- proof string: "exact MulChar.exists_mulChar_orderOf F h hζ"
variable (F : Type) [Field F] [Fintype F]
variable (R : Type) [CommRing R]
lemma KP (n : ℕ) (h : n ∣ Fintype.card F - 1) (ζ : R)
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ χ : MulChar F R, orderOf χ = n := by sorry


-- [PG] mathlib statement, solved by exact?
-- proof string: "exact ProbabilityTheory.integrable_exp_mul_of_abs_le hu_int_pos hu_int_neg htu"
variable (Ω : Type) (m : MeasurableSpace Ω) (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω)
lemma YF (u t : ℝ) (hu_int_pos : MeasureTheory.Integrable (fun ω ↦ Real.exp (u * X ω)) μ)
    (hu_int_neg : MeasureTheory.Integrable (fun ω ↦ Real.exp (- u * X ω)) μ)
    (htu : |t| ≤ |u|) :
    MeasureTheory.Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by sorry


-- [HK] mathlib statement, solved by exact?
-- proof string: "exact Subgroup.nilpotencyClass_le _"
theorem PG (G : Type u) [Group G] [Group.IsNilpotent G] (H : Subgroup G) :
    Group.nilpotencyClass H ≤ Group.nilpotencyClass G := by sorry
