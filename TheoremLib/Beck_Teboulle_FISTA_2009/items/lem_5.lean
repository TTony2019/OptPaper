import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-- Lemma 4.2: Let `{a_k}`, `{b_k}` be positive sequences of reals satisfying
`a_k - a_{k+1} ≥ b_{k+1} - b_k` for all `k ≥ 1`, with `a_1 + b_1 ≤ c`, `c > 0`.
Then `a_k ≤ c` for every `k ≥ 1`. -/
theorem sequence_inequality {a b : ℕ → ℝ} {c : ℝ}
    (hpos_a : ∀ k, 0 < a k) (hpos_b : ∀ k, 0 < b k)
    (hineq : ∀ k, a k - a (k + 1) ≥ b (k + 1) - b k)
    (hbound : a 1 + b 1 ≤ c) (hc_pos : 0 < c) (k : ℕ) (hk : 1 ≤ k) :
    a k ≤ c := by
  have htelescope : a 1 - a k ≥ b k - b 1 := by
    refine Nat.le_induction (by simpa using le_refl (0 : ℝ)) (fun m hm h_ih => ?_) k hk
    have hineq_m := hineq m
    linarith
  have hpos_bk : 0 < b k := hpos_b k
  linarith
