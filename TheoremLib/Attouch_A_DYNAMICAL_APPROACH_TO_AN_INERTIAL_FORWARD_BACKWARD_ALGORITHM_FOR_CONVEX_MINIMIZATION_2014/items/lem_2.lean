import Mathlib

namespace AttouchPeypouquetRedont2014

private theorem prefix_le_sum (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    {k k₀ : ℕ} (hk : k < k₀) :
    p k ≤ ∑ i ∈ Finset.range k₀, p i := by
  exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_range.mpr hk)

private theorem bounded_of_nonneg_upper (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    {U : ℝ} (hU : ∀ k, p k ≤ U) :
    Bornology.IsBounded (Set.range p) := by
  apply (Metric.isBounded_iff).2
  refine ⟨U, ?_⟩
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> nlinarith [hp i, hp j, hU i, hU j]

/-- Lemma 7: a nonnegative eventually contractive recurrence is bounded. -/
theorem lemma7 (p : ℕ → ℝ) (ω K : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hω : ω < 1)
    (hrec : ∃ k₀, ∀ k ≥ k₀, p k - ω * p (k - 1) ≤ K) :
    Bornology.IsBounded (Set.range p) := by
  rcases hrec with ⟨k₀, hrec0⟩
  let S : ℝ := ∑ i ∈ Finset.range k₀, p i
  have hprefix : ∀ k, k < k₀ → p k ≤ S := by
    intro k hk
    simpa [S] using prefix_le_sum p hp hk
  by_cases hωnonpos : ω ≤ 0
  · let U : ℝ := max S K
    apply bounded_of_nonneg_upper p hp (U := U)
    intro k
    by_cases hk : k₀ ≤ k
    · have hmul : ω * p (k - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hωnonpos (hp _)
      have htail : p k ≤ K := by
        have := (sub_le_iff_le_add.mp (hrec0 k hk))
        nlinarith
      exact htail.trans (by simp [U])
    · have hpre : p k ≤ S := hprefix k (by omega)
      exact hpre.trans (by simp [U])
  · have hωpos : 0 < ω := lt_of_not_ge hωnonpos
    have hden : 0 < 1 - ω := by nlinarith
    let C : ℝ := max (p k₀) (max K 0 / (1 - ω))
    have hCnonneg : 0 ≤ C := by
      apply le_trans (hp k₀)
      simp [C]
    have hC_K : K ≤ (1 - ω) * C := by
      have hdiv : max K 0 / (1 - ω) ≤ C := by
        simp [C]
      have hmax : max K 0 ≤ C * (1 - ω) := (div_le_iff₀ hden).mp hdiv
      nlinarith [le_max_left K 0]
    have hbarrier : ω * C + K ≤ C := by
      nlinarith
    have htail : ∀ n : ℕ, p (k₀ + n) ≤ C := by
      intro n
      induction n with
      | zero =>
          simp [C]
      | succ n ihn =>
          have hk : k₀ ≤ k₀ + n + 1 := by omega
          have hstep := sub_le_iff_le_add.mp (hrec0 (k₀ + n + 1) hk)
          have hmul : ω * p (k₀ + n) ≤ ω * C :=
            mul_le_mul_of_nonneg_left ihn (le_of_lt hωpos)
          norm_num [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hstep
          have hnext : p (k₀ + n + 1) ≤ C := by
            calc
              p (k₀ + n + 1) ≤ K + ω * p (k₀ + n) := hstep
              _ ≤ K + ω * C := add_le_add_right hmul K
              _ = ω * C + K := add_comm _ _
              _ ≤ C := hbarrier
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext
    let U : ℝ := max S C
    apply bounded_of_nonneg_upper p hp (U := U)
    intro k
    by_cases hk : k₀ ≤ k
    · have htail' : p k ≤ C := by
        rw [← Nat.add_sub_of_le hk]
        exact htail (k - k₀)
      exact htail'.trans (by simp [U])
    · have hpre : p k ≤ S := hprefix k (by omega)
      exact hpre.trans (by simp [U])

end AttouchPeypouquetRedont2014
