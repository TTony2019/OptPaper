import Mathlib

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

/-- Lemma 2.2: telescoping descent gives monotone convergence and summability. -/
theorem lemma_2_2_descent_summable (a b : ℕ → ℝ)
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (ha_bddBelow : BddBelow (Set.range a))
    (hdesc : ∀ n, a (n + 1) + b n ≤ a n) :
    Antitone a ∧ (∃ l : ℝ, Tendsto a atTop (nhds l)) ∧ Summable b := by
  have hbdd : BddBelow (Set.range a) := ha_bddBelow
  obtain ⟨L, hL⟩ := ha_bddBelow
  have hstep : ∀ n, a (n + 1) ≤ a n := by
    intro n
    have hb : 0 ≤ b n := hb_nonneg n
    have hd : a (n + 1) + b n ≤ a n := hdesc n
    linarith
  have hanti : Antitone a := by
    intro m n hmn
    induction hmn with
    | refl => rfl
    | step hmn ih => exact le_trans (hstep _) ih
  have hconv : ∃ l : ℝ, Tendsto a atTop (nhds l) := by
    exact ⟨⨅ n, a n, tendsto_atTop_ciInf hanti hbdd⟩
  have hlower : ∀ n, L ≤ a n := by
    intro n
    exact hL ⟨n, rfl⟩
  have htel : ∀ n, (∑ i ∈ Finset.range n, b i) + a n ≤ a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have hd : a (n + 1) + b n ≤ a n := hdesc n
        linarith
  have hsumbdd : ∀ n, ∑ i ∈ Finset.range n, b i ≤ a 0 - L := by
    intro n
    have ht := htel n
    have hLn := hlower n
    linarith
  exact ⟨hanti, hconv, summable_of_sum_range_le hb_nonneg hsumbdd⟩

end BotCsetnek2015
