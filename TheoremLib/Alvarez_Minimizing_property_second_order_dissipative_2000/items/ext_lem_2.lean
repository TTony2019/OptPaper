import Mathlib

open Filter
open scoped Topology BigOperators

namespace Alvarez2000

/-- Alvarez' scalar inertial recurrence lemma.  It is the discrete sequence
lemma used in the proof of Theorem 3.1: the positive forward increments are
summable and the nonnegative sequence therefore converges. -/
theorem alvarez_sequence_convergence
    (psi delta alphaSeq : ℕ → ℝ)
    (hpsi_nonneg : ∀ n, 0 ≤ psi n)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (halpha_nonneg : ∀ n, 0 ≤ alphaSeq n)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      psi (n + 1) ≤ psi n + alphaSeq n * (psi n - psi (n - 1)) + delta n)
    (hsum_delta : Summable delta)
    (alpha : ℝ)
    (halpha_bound : ∀ n : ℕ, 1 ≤ n → alphaSeq n ≤ alpha)
    (halpha_lt : alpha < 1) :
    Summable (fun n : ℕ => max (psi (n + 2) - psi (n + 1)) 0) ∧
      ∃ psiStar : ℝ, 0 ≤ psiStar ∧ Tendsto psi atTop (nhds psiStar) := by
  let d : ℕ → ℝ := fun n => psi (n + 1) - psi n
  let q : ℕ → ℝ := fun n => max (d n) 0
  let σ : ℕ → ℝ := fun n => delta (n + 1)
  have halpha_nonneg' : 0 ≤ alpha :=
    le_trans (halpha_nonneg 1) (halpha_bound 1 (by omega))
  have hσ_nonneg : ∀ n, 0 ≤ σ n := by
    intro n; exact hdelta_nonneg (n + 1)
  have hσ_sum : Summable σ := by
    simpa [σ] using (summable_nat_add_iff 1).mpr hsum_delta
  have hq_nonneg : ∀ n, 0 ≤ q n := by
    intro n; exact le_max_right _ _
  have hq_rec : ∀ n, q (n + 1) ≤ alpha * q n + σ n := by
    intro n
    have hr := hrec (n + 1) (by omega)
    have hd : d (n + 1) ≤ alphaSeq (n + 1) * d n + σ n := by
      dsimp [d, σ]
      simpa [add_assoc, add_left_comm, add_comm] using hr
    have hmul : alphaSeq (n + 1) * d n ≤ alpha * q n := by
      dsimp [q]
      by_cases hdn : 0 ≤ d n
      · rw [max_eq_left hdn]
        exact mul_le_mul_of_nonneg_right (halpha_bound (n + 1) (by omega)) hdn
      · have hdneg : d n ≤ 0 := le_of_not_ge hdn
        rw [max_eq_right (le_of_not_ge hdn)]
        have ha0 : 0 ≤ alphaSeq (n + 1) := halpha_nonneg _
        nlinarith
    have hdl : d (n + 1) ≤ alpha * q n + σ n := by linarith
    dsimp [q]
    by_cases hp : 0 ≤ d (n + 1)
    · rw [max_eq_left hp]
      exact hdl
    · rw [max_eq_right (le_of_not_ge hp)]
      exact add_nonneg (mul_nonneg halpha_nonneg' (hq_nonneg n)) (hσ_nonneg n)
  have hq_sum : Summable q := by
    let D : ℝ := q 0 + ∑' n, σ n
    have hD : 0 ≤ D := add_nonneg (hq_nonneg 0) (tsum_nonneg hσ_nonneg)
    have hpartial_sigma : ∀ N, (Finset.range N).sum σ ≤ ∑' n, σ n := by
      intro N
      exact hσ_sum.sum_le_tsum _ (fun i _ => hσ_nonneg i)
    have hsum_rec : ∀ N, (Finset.range (N + 1)).sum q ≤
        alpha * (Finset.range N).sum q + D := by
      intro N
      rw [show (Finset.range (N + 1)).sum q = q 0 + (Finset.range N).sum (fun k => q (k + 1)) by
        simpa [add_comm] using (Finset.sum_range_succ' q N)]
      have hrec_sum : (Finset.range N).sum (fun k => q (k + 1)) ≤
          (Finset.range N).sum (fun k => alpha * q k + σ k) := by
        exact Finset.sum_le_sum (fun k hk => hq_rec k)
      have hsplit : (Finset.range N).sum (fun k => alpha * q k + σ k) =
          alpha * (Finset.range N).sum q + (Finset.range N).sum σ := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      rw [hsplit] at hrec_sum
      dsimp [D]
      linarith [hpartial_sigma N]
    have hbound : ∀ N, (Finset.range N).sum q ≤ D / (1 - alpha) := by
      intro N
      have hden : 0 < 1 - alpha := by linarith
      induction N with
      | zero => exact div_nonneg hD hden.le
      | succ N ih =>
          have hs := hsum_rec N
          have hmul := mul_le_mul_of_nonneg_left ih halpha_nonneg'
          have heq : alpha * (D / (1 - alpha)) + D = D / (1 - alpha) := by
            field_simp [ne_of_gt hden]
            ring
          calc
            (Finset.range (N + 1)).sum q ≤ alpha * (Finset.range N).sum q + D := hs
            _ ≤ alpha * (D / (1 - alpha)) + D := by linarith
            _ = D / (1 - alpha) := heq
    exact summable_of_sum_range_le hq_nonneg hbound
  have hpos : Summable (fun n : ℕ => max (psi (n + 2) - psi (n + 1)) 0) := by
    simpa [q, d] using (summable_nat_add_iff 1).mpr hq_sum
  let p : ℕ → ℝ := fun n => max (psi (n + 1) - psi n) 0
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, p i
  let u : ℕ → ℝ := fun n => psi n - S n
  have hp_nonneg : ∀ n, 0 ≤ p n := by intro n; exact le_max_right _ _
  have hu_anti : Antitone u := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [u, S]
    rw [Finset.sum_range_succ]
    have hi : psi (n + 1) - psi n ≤ p n := le_max_left _ _
    linarith
  have hS_le : ∀ n, S n ≤ ∑' i, p i := by
    intro n
    have hp_sum : Summable p := by
      simpa [p] using hq_sum
    exact hp_sum.sum_le_tsum _ (fun i _ => hp_nonneg i)
  have hu_bdd : BddBelow (Set.range u) := by
    refine ⟨-(∑' i, p i), ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp [u]
    linarith [hpsi_nonneg n, hS_le n]
  have hu_lim : Tendsto u atTop (nhds (⨅ n, u n)) := tendsto_atTop_ciInf hu_anti hu_bdd
  have hS_lim : Tendsto S atTop (nhds (∑' i, p i)) := by
    have hp_sum : Summable p := by
      simpa [p] using hq_sum
    simpa [S] using hp_sum.hasSum.tendsto_sum_nat
  obtain ⟨l, hl⟩ : ∃ l : ℝ, Tendsto psi atTop (nhds l) := by
    refine ⟨(⨅ n, u n) + ∑' i, p i, ?_⟩
    have hsum := hu_lim.add hS_lim
    convert hsum using 1 <;> simp [u, S, sub_add_cancel]
  refine ⟨hpos, l, ?_, hl⟩
  exact ge_of_tendsto hl (Filter.Eventually.of_forall hpsi_nonneg)

end Alvarez2000
