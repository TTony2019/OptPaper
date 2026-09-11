import Foundation.Analysis.ExtendedRealFunctions
import Mathlib

noncomputable section

/-- The Lasso-type composite objective `x ↦ ‖A x - b‖² / 2 + g x`. -/
def lassoObjective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (g : (n → ℝ) → EReal)
    (_hmn : Fintype.card m ≤ Fintype.card n)
    (_hconvex : ∀ (x y : n → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a • x + b • y) ≤ (a : EReal) * g x + (b : EReal) * g y)
    (_hlsc : LowerSemicontinuous g) (_hproper : ERealFunction.IsProper g) : (n → ℝ) → EReal :=
  fun x ↦ ((1 / 2 : ℝ) * ‖A.mulVec x - b‖ ^ 2 : ℝ) + g x
