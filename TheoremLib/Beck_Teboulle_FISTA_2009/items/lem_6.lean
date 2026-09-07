import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Basic

/-- The sequence `{t_k}` defined by the FISTA recurrence:
`t₁ = 1`, `t_{k+1} = (1 + √(1 + 4t_k²)) / 2`.

For `k = 0`, we define `t₀ = 1` as a convenience (the paper only uses `k ≥ 1`). -/
noncomputable def fistaTSeq : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | k + 2 => (1 + Real.sqrt (1 + 4 * fistaTSeq (k + 1) ^ 2)) / 2

/-- Lemma 4.3: The positive sequence `{t_k}` generated via the FISTA recurrence
with `t₁ = 1` satisfies `t_k ≥ (k + 1) / 2` for all `k ≥ 1`. -/
theorem fista_t_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    fistaTSeq k ≥ ((k : ℝ) + 1) / 2 := by
  refine Nat.le_induction ?base ?step k hk
  · simp [fistaTSeq]
  · intro m hm hi
    have hm_pos : m ≠ 0 := by omega
    rcases Nat.exists_eq_succ_of_ne_zero hm_pos with ⟨n, rfl⟩
    have hi' : fistaTSeq (n + 1) ≥ (((n : ℝ) + 1) + 1) / 2 := by
      simpa [Nat.cast_succ] using hi
    simp [fistaTSeq, Nat.cast_succ]
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hn2_nonneg : 0 ≤ (n : ℝ) + 2 := by linarith
    have hS_nonneg : 0 ≤ fistaTSeq (n + 1) := by
      have : 0 ≤ ((n : ℝ) + 2) / 2 := by nlinarith
      linarith
    have h_sq : 4 * (fistaTSeq (n + 1)) ^ 2 ≥ ((n : ℝ) + 2) ^ 2 := by
      have hS_sq : (fistaTSeq (n + 1)) ^ 2 ≥ (((n : ℝ) + 2) / 2) ^ 2 := by
        nlinarith
      calc
        4 * (fistaTSeq (n + 1)) ^ 2 ≥ 4 * (((n : ℝ) + 2) / 2) ^ 2 := by nlinarith
        _ = ((n : ℝ) + 2) ^ 2 := by ring
    have h_inner : 1 + 4 * (fistaTSeq (n + 1)) ^ 2 ≥ 1 + ((n : ℝ) + 2) ^ 2 := by linarith
    have h_sqrt : Real.sqrt (1 + 4 * (fistaTSeq (n + 1)) ^ 2) ≥
        Real.sqrt (1 + ((n : ℝ) + 2) ^ 2) :=
      Real.sqrt_le_sqrt h_inner
    have h_sqrt_ge : Real.sqrt (1 + ((n : ℝ) + 2) ^ 2) ≥ (n : ℝ) + 2 := by
      have h_sq' : 1 + ((n : ℝ) + 2) ^ 2 ≥ ((n : ℝ) + 2) ^ 2 := by nlinarith
      have h' := Real.sqrt_le_sqrt h_sq'
      rw [Real.sqrt_sq hn2_nonneg] at h'
      exact h'
    linarith
