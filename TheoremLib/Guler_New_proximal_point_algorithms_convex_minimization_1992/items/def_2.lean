import Mathlib.Tactic

/-- The product sequence `β_k = ∏_{j<k}(1-α_j)`. -/
def betaSequence (α : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (1 - α j)

/-- Estimate-sequence consequence (2.3) of the update inequality (2.1). -/
theorem betaSequence_estimate {H : Type*} (α : ℕ → ℝ) (φ : ℕ → H → ℝ) (f : H → ℝ)
    (hstep : ∀ k x, φ (k + 1) x - f x ≤ (1 - α k) * (φ k x - f x))
    (hα : ∀ k, α k ∈ Set.Ico (0 : ℝ) 1) :
    ∀ k x, φ k x - f x ≤ betaSequence α k * (φ 0 x - f x) := by
  intro k x
  induction k with
  | zero => simp [betaSequence]
  | succ k ih =>
      have hfac_nonneg : 0 ≤ 1 - α k := sub_nonneg.mpr (le_of_lt (hα k).2)
      calc
        φ (k + 1) x - f x ≤ (1 - α k) * (φ k x - f x) := hstep k x
        _ ≤ (1 - α k) * (betaSequence α k * (φ 0 x - f x)) :=
          mul_le_mul_of_nonneg_left ih hfac_nonneg
        _ = betaSequence α (k + 1) * (φ 0 x - f x) := by
          simp only [betaSequence, Finset.prod_range_succ]
          ring
