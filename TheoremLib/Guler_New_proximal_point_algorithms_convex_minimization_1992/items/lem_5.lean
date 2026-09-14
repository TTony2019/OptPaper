import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_6

private theorem betaSequence_pos_of_Ico (α : ℕ → ℝ)
    (hα : ∀ i, α i ∈ Set.Ico (0 : ℝ) 1) (n : ℕ) : 0 < betaSequence α n := by
  rw [betaSequence]
  exact Finset.prod_pos fun i hi => sub_pos.mpr (hα i).2

private theorem inexact_error_closed_form_all (α ε lam δ : ℕ → ℝ)
    (hα : ∀ i, α i ∈ Set.Ico (0 : ℝ) 1) (hlam : ∀ i, 0 < lam i)
    (hδ : δ 0 = 0)
    (hrec : ∀ i, δ (i + 1) = (1 - α i) * δ i + ε i ^ 2 / (2 * lam i)) :
    ∀ k, δ k = betaSequence α k / 2 * ∑ j ∈ Finset.range k,
      (ε j ^ 2 / lam j) / betaSequence α (j + 1) := by
  intro k
  induction k with
  | zero => simp [hδ, betaSequence]
  | succ k ih =>
      have hβsucc : betaSequence α (k + 1) = betaSequence α k * (1 - α k) := by
        simp [betaSequence, Finset.prod_range_succ]
      rw [hrec, ih]
      rw [hβsucc, Finset.sum_range_succ]
      field_simp [ne_of_gt (betaSequence_pos_of_Ico α hα (k + 1)), ne_of_gt (hlam k)]
      rw [hβsucc]
      ring

/-- Lemma 3.3: the closed form and explicit finite-horizon bound for the
inexactness recurrence.  The paper's final `O(k^(1-2σ))` estimate is not
silently asserted here; the convergence theorem takes that asymptotic bound
as an explicit hypothesis because it requires a separate summation estimate. -/
theorem inexact_error_closed_form (α ε lam δ : ℕ → ℝ) (A : ℝ) (k : ℕ)
    (hA : 0 < A) (hα : ∀ i, α i ∈ Set.Ico (0 : ℝ) 1)
    (hlam : ∀ i, 0 < lam i)
    (hbeta : ∀ i, α i ^ 2 = (1 - α i) * A * betaSequence α i * lam i)
    (hδ : δ 0 = 0) (hrec : ∀ i, δ (i + 1) = (1 - α i) * δ i + ε i ^ 2 / (2 * lam i)) :
    δ k = betaSequence α k / 2 * ∑ j ∈ Finset.range k, (ε j ^ 2 / lam j) / betaSequence α (j + 1) ∧
    δ k ≤ 2 * ∑ j ∈ Finset.range k, ε j ^ 2 / lam j *
      ((1 + Real.sqrt A * ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) /
       (1 + Real.sqrt A * ∑ i ∈ Finset.range k, Real.sqrt (lam i))) ^ 2
    := by
  have hβpos : ∀ n, 0 < betaSequence α n := betaSequence_pos_of_Ico α hα
  have hα' : ∀ i, α i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    constructor
    · have hrhs : 0 < (1 - α i) * A * betaSequence α i * lam i := by
        exact mul_pos (mul_pos (mul_pos (sub_pos.mpr (hα i).2) hA) (hβpos i)) (hlam i)
      have hsquare : 0 < α i ^ 2 := by rw [hbeta i]; exact hrhs
      have hne : α i ≠ 0 := by
        intro hz
        simp [hz] at hsquare
      exact lt_of_le_of_ne (hα i).1 hne.symm
    · exact le_of_lt (hα i).2
  have hclosed := inexact_error_closed_form_all α ε lam δ hα hlam hδ hrec
  refine ⟨hclosed k, ?_⟩
  · rw [hclosed k, Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range k, 2 * (ε j ^ 2 / lam j *
          ((1 + Real.sqrt A * ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) /
           (1 + Real.sqrt A * ∑ i ∈ Finset.range k, Real.sqrt (lam i))) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hlow := (betaSequence_bounds A hA lam α (j + 1) hα' hlam hbeta).1
        have hupp := (betaSequence_bounds A hA lam α k hα' hlam hbeta).2
        have hsum_nonneg (n : ℕ) : 0 ≤ ∑ i ∈ Finset.range n, Real.sqrt (lam i) :=
          Finset.sum_nonneg fun i hi => Real.sqrt_nonneg _
        have hden (n : ℕ) : 0 < 1 + Real.sqrt A * ∑ i ∈ Finset.range n, Real.sqrt (lam i) := by
          have : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
          nlinarith [hsum_nonneg n]
        have hupp' : betaSequence α k / 2 ≤
        2 / (1 + Real.sqrt A * ∑ i ∈ Finset.range k, Real.sqrt (lam i)) ^ 2 := by
          let D := 1 + Real.sqrt A * ∑ i ∈ Finset.range k, Real.sqrt (lam i)
          let E := 1 + (Real.sqrt A / 2) * ∑ i ∈ Finset.range k, Real.sqrt (lam i)
          have hD : 0 < D := hden k
          have hE : 0 < E := by
            dsimp [E]
            have : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
            nlinarith [hsum_nonneg k]
          have hDE : D ≤ 2 * E := by
            dsimp [D, E]
            ring_nf
            linarith
          have hratio : 1 / E ^ 2 ≤ 4 / D ^ 2 := by
            field_simp [ne_of_gt hD, ne_of_gt hE]
            nlinarith [sq_nonneg (D - 2 * E)]
          calc
            betaSequence α k / 2 ≤ (1 / E ^ 2) / 2 := by linarith
            _ ≤ (4 / D ^ 2) / 2 := by gcongr
            _ = 2 / D ^ 2 := by ring
        have hlow' : 1 / betaSequence α (j + 1) ≤
        (1 + Real.sqrt A * ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) ^ 2 := by
          have hp : 0 < betaSequence α (j + 1) := hβpos _
          have hd : 0 < (1 + Real.sqrt A * ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) ^ 2 :=
        sq_pos_of_pos (hden _)
          calc
            1 / betaSequence α (j + 1) ≤ 1 / (1 / (1 + Real.sqrt A *
                ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) ^ 2) :=
              one_div_le_one_div_of_le (by positivity) hlow
            _ = (1 + Real.sqrt A * ∑ i ∈ Finset.range (j + 1), Real.sqrt (lam i)) ^ 2 := by
              field_simp [ne_of_gt (hden _)]
        have he : 0 ≤ ε j ^ 2 / lam j := div_nonneg (sq_nonneg _) (le_of_lt (hlam j))
        have hmul := mul_le_mul hupp' hlow'
          (div_nonneg zero_le_one (le_of_lt (hβpos (j + 1))))
          (div_nonneg (by norm_num) (sq_nonneg _))
        have hmul' := mul_le_mul_of_nonneg_left hmul he
        field_simp [ne_of_gt (hden k)] at hmul' ⊢
        nlinarith
      _ = _ := by simp [Finset.mul_sum]
