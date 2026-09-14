import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_6

theorem betaSequence_pos_of_Ioc_recurrence (A : ℝ) (hA : 0 < A) (lam α : ℕ → ℝ)
    (hα : ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1) (hlam : ∀ j, 0 < lam j)
    (hrec : ∀ j, α j ^ 2 = (1 - α j) * A * betaSequence α j * lam j) :
    ∀ n, 0 < betaSequence α n := by
  have hαlt : ∀ j, α j < 1 := by
    intro j
    rcases hα j with ⟨hαpos, hαle⟩
    apply lt_of_le_of_ne hαle
    intro heq
    have hr := hrec j
    rw [heq] at hr
    norm_num at hr
  intro n
  rw [betaSequence]
  exact Finset.prod_pos fun j hj => sub_pos.mpr (hαlt j)

/-- Lemma 2.2, the two-sided estimate on `β_k`. -/
theorem betaSequence_bounds (A : ℝ) (hA : 0 < A) (lam α : ℕ → ℝ) (k : ℕ)
    (hα : ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1)
    (hlam : ∀ j, 0 < lam j)
    (hrec : ∀ j, α j ^ 2 = (1 - α j) * A * betaSequence α j * lam j) :
    1 / (1 + Real.sqrt A * ∑ j ∈ Finset.range k, Real.sqrt (lam j)) ^ 2 ≤ betaSequence α k ∧
    betaSequence α k ≤ 1 / (1 + (Real.sqrt A / 2) * ∑ j ∈ Finset.range k, Real.sqrt (lam j)) ^ 2 := by
  have hβpos : ∀ n, 0 < betaSequence α n :=
    betaSequence_pos_of_Ioc_recurrence A hA lam α hα hlam hrec
  have hαlt : ∀ j, α j < 1 := by
    intro j
    rcases hα j with ⟨hαpos, hαle⟩
    apply lt_of_le_of_ne hαle
    intro heq
    have hr := hrec j
    rw [heq] at hr
    norm_num at hr
  have hβsucc : ∀ j, betaSequence α (j + 1) = betaSequence α j * (1 - α j) := by
    intro j
    simp [betaSequence, Finset.prod_range_succ]
  let μ : ℕ → ℝ := fun n => 1 / Real.sqrt (betaSequence α n)
  have hμpos : ∀ n, 0 < μ n := by
    intro n
    dsimp [μ]
    exact one_div_pos.mpr (Real.sqrt_pos.2 (hβpos n))
  have hμzero : μ 0 = 1 := by simp [μ, betaSequence]
  have hμrec : ∀ j, μ (j + 1) ^ 2 - μ j ^ 2 = μ (j + 1) * Real.sqrt (A * lam j) := by
    intro j
    have hrec' : α j ^ 2 = betaSequence α (j + 1) * (A * lam j) := by
      rw [hrec j, hβsucc j]
      ring
    have hsquare : (α j) ^ 2 =
        (Real.sqrt (betaSequence α (j + 1)) * Real.sqrt (A * lam j)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (hβpos _)),
        Real.sq_sqrt (le_of_lt (mul_pos hA (hlam j)))]
      exact hrec'
    have hαsqrt : α j = Real.sqrt (betaSequence α (j + 1)) * Real.sqrt (A * lam j) := by
      have hleft : 0 < α j := (hα j).1
      have hright : 0 < Real.sqrt (betaSequence α (j + 1)) * Real.sqrt (A * lam j) :=
        mul_pos (Real.sqrt_pos.2 (hβpos _))
          (Real.sqrt_pos.2 (mul_pos hA (hlam j)))
      nlinarith
    have hdiff : betaSequence α j - betaSequence α (j + 1) = betaSequence α j * α j := by
      rw [hβsucc j]
      ring
    dsimp [μ]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hβpos j)),
      ne_of_gt (Real.sqrt_pos.2 (hβpos (j + 1)))]
    rw [Real.sq_sqrt (le_of_lt (hβpos j)),
      Real.sq_sqrt (le_of_lt (hβpos (j + 1)))]
    rw [hdiff, hαsqrt]
    ring
  have hβmono : ∀ j, betaSequence α (j + 1) ≤ betaSequence α j := by
    intro j
    rw [hβsucc j]
    have hfac : 0 < 1 - α j := sub_pos.mpr (hαlt j)
    have hfac_le : 1 - α j ≤ 1 := by linarith [(hα j).1]
    nlinarith [hβpos j]
  have hμmono : ∀ j, μ j ≤ μ (j + 1) := by
    intro j
    dsimp [μ]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (hβpos (j + 1))) (Real.sqrt_le_sqrt (hβmono j))
  have hstep : ∀ j, Real.sqrt (A * lam j) / 2 ≤ μ (j + 1) - μ j ∧
      μ (j + 1) - μ j ≤ Real.sqrt (A * lam j) := by
    intro j
    have hd : 0 ≤ μ (j + 1) - μ j := sub_nonneg.mpr (hμmono j)
    have hsumle : μ (j + 1) + μ j ≤ 2 * μ (j + 1) := by linarith [hμmono j]
    have hbig : μ (j + 1) * Real.sqrt (A * lam j) ≤
        2 * μ (j + 1) * (μ (j + 1) - μ j) := by
      calc
        μ (j + 1) * Real.sqrt (A * lam j) = μ (j + 1) ^ 2 - μ j ^ 2 :=
          (hμrec j).symm
        _ = (μ (j + 1) - μ j) * (μ (j + 1) + μ j) := by ring
        _ ≤ (μ (j + 1) - μ j) * (2 * μ (j + 1)) :=
          mul_le_mul_of_nonneg_left hsumle hd
        _ = 2 * μ (j + 1) * (μ (j + 1) - μ j) := by ring
    have hlower : Real.sqrt (A * lam j) / 2 ≤ μ (j + 1) - μ j := by
      have hbig' : μ (j + 1) * Real.sqrt (A * lam j) ≤
          μ (j + 1) * (2 * (μ (j + 1) - μ j)) := by
        convert hbig using 1 <;> ring
      have hcancel := le_of_mul_le_mul_left hbig' (hμpos (j + 1))
      nlinarith
    have hsumge : μ (j + 1) ≤ μ (j + 1) + μ j := by linarith [hμpos j]
    have hsmall : μ (j + 1) * (μ (j + 1) - μ j) ≤
        μ (j + 1) * Real.sqrt (A * lam j) := by
      calc
        μ (j + 1) * (μ (j + 1) - μ j) ≤
            (μ (j + 1) + μ j) * (μ (j + 1) - μ j) :=
          mul_le_mul_of_nonneg_right hsumge hd
        _ = μ (j + 1) ^ 2 - μ j ^ 2 := by ring
        _ = μ (j + 1) * Real.sqrt (A * lam j) := hμrec j
    have hupper : μ (j + 1) - μ j ≤ Real.sqrt (A * lam j) :=
      le_of_mul_le_mul_left hsmall (hμpos (j + 1))
    exact ⟨hlower, hupper⟩
  have hsqrt : ∀ j, Real.sqrt (A * lam j) = Real.sqrt A * Real.sqrt (lam j) := by
    intro j
    rw [Real.sqrt_mul (le_of_lt hA)]
  have hμupper : ∀ n, μ n ≤
      1 + Real.sqrt A * ∑ j ∈ Finset.range n, Real.sqrt (lam j) := by
    intro n
    induction n with
    | zero => simp [hμzero]
    | succ n ih =>
      have hstep' : μ (n + 1) - μ n ≤ Real.sqrt A * Real.sqrt (lam n) := by
        simpa [hsqrt n] using (hstep n).2
      calc
        μ (n + 1) = μ n + (μ (n + 1) - μ n) := by ring
        _ ≤ (1 + Real.sqrt A * ∑ j ∈ Finset.range n, Real.sqrt (lam j)) +
            Real.sqrt A * Real.sqrt (lam n) := add_le_add ih hstep'
        _ = 1 + Real.sqrt A * ∑ j ∈ Finset.range (n + 1), Real.sqrt (lam j) := by
          rw [Finset.sum_range_succ]
          ring
  have hμlower : ∀ n, 1 + (Real.sqrt A / 2) *
      ∑ j ∈ Finset.range n, Real.sqrt (lam j) ≤ μ n := by
    intro n
    induction n with
    | zero => simp [hμzero]
    | succ n ih =>
      have hstep' : (Real.sqrt A / 2) * Real.sqrt (lam n) ≤ μ (n + 1) - μ n := by
        calc
          (Real.sqrt A / 2) * Real.sqrt (lam n) =
              (Real.sqrt A * Real.sqrt (lam n)) / 2 := by ring
          _ = Real.sqrt (A * lam n) / 2 := by rw [hsqrt n]
          _ ≤ μ (n + 1) - μ n := (hstep n).1
      calc
        1 + (Real.sqrt A / 2) * ∑ j ∈ Finset.range (n + 1), Real.sqrt (lam j) =
            (1 + (Real.sqrt A / 2) * ∑ j ∈ Finset.range n, Real.sqrt (lam j)) +
              (Real.sqrt A / 2) * Real.sqrt (lam n) := by
          rw [Finset.sum_range_succ]
          ring
        _ ≤ μ n + (μ (n + 1) - μ n) := add_le_add ih hstep'
        _ = μ (n + 1) := by ring
  have hsum_nonneg : ∀ n, 0 ≤ ∑ j ∈ Finset.range n, Real.sqrt (lam j) := by
    intro n
    exact Finset.sum_nonneg fun j hj => Real.sqrt_nonneg _
  have hμsq : ∀ n, μ n ^ 2 = 1 / betaSequence α n := by
    intro n
    dsimp [μ]
    field_simp [ne_of_gt (Real.sqrt_pos.2 (hβpos n))]
    rw [Real.sq_sqrt (le_of_lt (hβpos n))]
    field_simp [ne_of_gt (hβpos n)]
  let D : ℝ := 1 + Real.sqrt A * ∑ j ∈ Finset.range k, Real.sqrt (lam j)
  let E : ℝ := 1 + (Real.sqrt A / 2) * ∑ j ∈ Finset.range k, Real.sqrt (lam j)
  have hD : 0 < D := by
    dsimp [D]
    have hroot : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    nlinarith [hsum_nonneg k]
  have hE : 0 < E := by
    dsimp [E]
    have hroot : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
    nlinarith [hsum_nonneg k]
  have hDsquare : μ k ^ 2 ≤ D ^ 2 := by
    have hu := hμupper k
    change μ k ≤ D at hu
    nlinarith [sq_nonneg (D - μ k), hμpos k]
  have hEsquare : E ^ 2 ≤ μ k ^ 2 := by
    have hl := hμlower k
    change E ≤ μ k at hl
    nlinarith [sq_nonneg (μ k - E), hμpos k, hE]
  constructor
  · have hquot : 1 / betaSequence α k ≤ D ^ 2 := by simpa [hμsq k] using hDsquare
    calc
      1 / D ^ 2 ≤ 1 / (1 / betaSequence α k) :=
        one_div_le_one_div_of_le (one_div_pos.mpr (hβpos k)) hquot
      _ = betaSequence α k := by field_simp [ne_of_gt (hβpos k)]
  · have hquot : E ^ 2 ≤ 1 / betaSequence α k := by simpa [hμsq k] using hEsquare
    calc
      betaSequence α k = 1 / (1 / betaSequence α k) := by
        field_simp [ne_of_gt (hβpos k)]
      _ ≤ 1 / E ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hE) hquot
