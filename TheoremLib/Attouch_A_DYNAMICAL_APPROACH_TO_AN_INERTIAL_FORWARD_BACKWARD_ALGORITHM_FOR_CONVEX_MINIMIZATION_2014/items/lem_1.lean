import Mathlib

namespace AttouchPeypouquetRedont2014

private theorem sum_Ico_successive_sub (f : ℕ → ℝ) (N L : ℕ) :
    ∑ i ∈ Finset.Ico N (N + L), (f (i + 1) - f i) = f (N + L) - f N := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Nat.add_succ, Finset.sum_Ico_succ_top (Nat.le_add_right N L), ih]
      ring

private theorem linear_bound_of_first_recurrence
    (a ε : ℕ → ℝ) (θ : ℝ) (k₀ : ℕ) (_hk₀ : 1 ≤ k₀)
    (hε : Summable fun k ↦ ‖ε k‖)
    (ha : ∀ k ≥ k₀, a k - a (k - 1) ≤ θ + ε k) :
    ∃ A : ℝ, ∀ m ≥ k₀, a m ≤ (m : ℝ) * θ + A := by
  let C : ℝ := ∑' j : ℕ, ‖ε j‖
  have hC : ∀ s : Finset ℕ, ∑ j ∈ s, ε j ≤ C := by
    intro s
    calc
      ∑ j ∈ s, ε j ≤ ∑ j ∈ s, ‖ε j‖ := by
        exact Finset.sum_le_sum fun j hj => by
          simpa only [Real.norm_eq_abs] using (le_abs_self (ε j))
      _ ≤ ∑' j : ℕ, ‖ε j‖ :=
        hε.sum_le_tsum s fun j hj => norm_nonneg _
      _ = C := rfl
  refine ⟨a (k₀ - 1) + (1 - (k₀ : ℝ)) * θ + C, ?_⟩
  intro m hm
  have hsum : ∑ i ∈ Finset.Ico k₀ (m + 1), (a i - a (i - 1))
      ≤ ∑ i ∈ Finset.Ico k₀ (m + 1), (θ + ε i) := by
    exact Finset.sum_le_sum fun i hi => ha i (Finset.mem_Ico.mp hi).1
  have htel : ∑ i ∈ Finset.Ico k₀ (m + 1), (a i - a (i - 1))
      = a m - a (k₀ - 1) := by
    have hindex : k₀ + (m + 1 - k₀) = m + 1 :=
      Nat.add_sub_of_le (Nat.le_succ_of_le hm)
    simpa [hindex] using
      (sum_Ico_successive_sub (fun n => a (n - 1)) k₀ (m + 1 - k₀))
  have herr : ∑ i ∈ Finset.Ico k₀ (m + 1), ε i ≤ C := hC _
  have hright : ∑ i ∈ Finset.Ico k₀ (m + 1), (θ + ε i)
      = ((m : ℝ) + 1 - k₀) * θ + ∑ i ∈ Finset.Ico k₀ (m + 1), ε i := by
    simp [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      Nat.cast_sub (Nat.le_succ_of_le hm), nsmul_eq_mul]
  rw [htel, hright] at hsum
  nlinarith

private theorem b_tail_le_neg_mul
    (a b : ℕ → ℝ) (k₀ N : ℕ) (c : ℝ) (hkN : k₀ ≤ N)
    (hb : ∀ k ≥ k₀, b (k + 1) - b k ≤ a k)
    (ha_neg : ∀ k ≥ N, a k ≤ -c) (L : ℕ) :
    b (N + L) - b N ≤ - (L : ℝ) * c := by
  have hsum : ∑ i ∈ Finset.Ico N (N + L), (b (i + 1) - b i)
      ≤ ∑ i ∈ Finset.Ico N (N + L), a i := by
    exact Finset.sum_le_sum fun i hi =>
      hb i (le_trans hkN (Finset.mem_Ico.mp hi).1)
  have hneg : ∑ i ∈ Finset.Ico N (N + L), a i
      ≤ ∑ i ∈ Finset.Ico N (N + L), (-c) := by
    exact Finset.sum_le_sum fun i hi => ha_neg i (Finset.mem_Ico.mp hi).1
  have htel : ∑ i ∈ Finset.Ico N (N + L), (b (i + 1) - b i)
      = b (N + L) - b N := sum_Ico_successive_sub b N L
  have hconst : ∑ i ∈ Finset.Ico N (N + L), (-c) = -(L : ℝ) * c := by
    simp [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [htel] at hsum
  rw [hconst] at hneg
  exact hsum.trans hneg

/-- Lemma 5: the two recurrence inequalities force `θ ≥ 0`. -/
theorem lemma5 (a b ε : ℕ → ℝ) (θ : ℝ) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hε : Summable fun k ↦ ‖ε k‖)
    (ha : ∀ k ≥ k₀, a k - a (k - 1) ≤ θ + ε k)
    (hb : ∀ k ≥ k₀, b (k + 1) - b k ≤ a k)
    (hnonneg : ∀ k ≥ k₀, 0 ≤ b k) : θ ≥ 0 := by
  rcases linear_bound_of_first_recurrence a ε θ k₀ hk₀ hε ha with ⟨A, hA⟩
  by_contra hnot
  have hθ : θ < 0 := lt_of_not_ge hnot
  let c : ℝ := -θ / 2
  have hc : 0 < c := by dsimp [c]; nlinarith
  rcases exists_nat_gt (A / c) with ⟨N₀, hN₀⟩
  let N : ℕ := max k₀ (max 1 N₀)
  have hkN : k₀ ≤ N := le_max_left _ _
  have h1N : 1 ≤ N := le_trans (le_max_left 1 N₀) (le_max_right k₀ _)
  have hN₀N : N₀ ≤ N := le_trans (le_max_right 1 N₀) (le_max_right k₀ _)
  have hNc : A < (N : ℝ) * c := by
    apply (div_lt_iff₀ hc).mp
    exact lt_of_lt_of_le hN₀ (by exact_mod_cast hN₀N)
  have hθc : θ = -2 * c := by dsimp [c]; ring
  have ha_neg : ∀ k ≥ N, a k ≤ -c := by
    intro k hk
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hA' := hA k (le_trans hkN hk)
    rw [hθc] at hA'
    have h1Nr : (1 : ℝ) ≤ N := by exact_mod_cast h1N
    nlinarith [mul_nonneg (sub_nonneg.mpr hNk) hc.le,
      mul_nonneg (sub_nonneg.mpr h1Nr) hc.le]
  rcases exists_nat_gt (b N / c) with ⟨L, hL⟩
  have hLc : b N < (L : ℝ) * c := (div_lt_iff₀ hc).mp hL
  have htail := b_tail_le_neg_mul a b k₀ N c hkN hb ha_neg L
  have hnn := hnonneg (N + L) (le_trans hkN (Nat.le_add_right N L))
  nlinarith

end AttouchPeypouquetRedont2014
