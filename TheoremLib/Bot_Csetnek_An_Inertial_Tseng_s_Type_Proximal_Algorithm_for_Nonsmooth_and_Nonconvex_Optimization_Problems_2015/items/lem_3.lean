import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_2

namespace BotCsetnek2015

/-- The strict parameter inequality (19) in Lemma 3.3. -/
def lemma33StrictInequality (sigma Lh Lu lambdaLower alpha nu mu : ℝ) : Prop :=
  2 * lambdaLower * (Lh + nu) +
      lambdaLower ^ 2 * Lh ^ 2 *
        (lambdaLower * (Lh ^ 2 / nu) + Lu + 2 * lambdaLower * (Lh + nu)) +
      2 * alpha *
        (mu + mu * lambdaLower ^ 2 * Lh ^ 2 +
          (1 + lambdaLower * Lh) ^ 2 / (2 * mu)) <
    sigma

/-- Parameters chosen as in Lemma 3.3, including the resulting strict `M2 < M1`. -/
def chosenAsInLemma33 {m : ℕ} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : ℝ) : Prop :=
  0 < nu ∧ 0 < mu ∧
    lemma33StrictInequality A.sigma P.Lgrad_h A.Lgrad_u A.lambdaLower A.alpha nu mu ∧
    A.M2 nu mu < A.M1 nu mu

theorem lemma33_base_scaled_inequality
    (sigma Lh Lu lambdaLower alpha nu mu : ℝ)
    (hnu : 0 < nu) (hmu : 0 < mu) (hlambda : 0 < lambdaLower)
    (hineq : lemma33StrictInequality sigma Lh Lu lambdaLower alpha nu mu) :
    2 * lambdaLower *
      (Lh + nu + (alpha / lambdaLower) * mu +
        lambdaLower ^ 2 * Lh ^ 2 *
          (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
        alpha / lambdaLower *
          (mu * lambdaLower ^ 2 * Lh ^ 2 +
            (1 + lambdaLower * Lh) ^ 2 / (2 * mu))) < sigma := by
  unfold lemma33StrictInequality at hineq
  field_simp [ne_of_gt hnu, ne_of_gt hmu, ne_of_gt hlambda] at hineq ⊢
  ring_nf at hineq ⊢
  exact hineq

theorem lemma33_m2_lt_m1_of_scaled
    (sigma Lh Lu lambdaUpper alpha lambdaLower nu mu : ℝ)
    (hlu : 0 < lambdaUpper)
    (hscaled :
      2 * lambdaUpper *
        (Lh + nu + (alpha / lambdaLower) * mu +
          lambdaUpper ^ 2 * Lh ^ 2 *
            (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
          alpha / lambdaLower *
            (mu * lambdaUpper ^ 2 * Lh ^ 2 +
              (1 + lambdaUpper * Lh) ^ 2 / (2 * mu))) < sigma) :
    M2Value Lh Lu lambdaUpper alpha lambdaLower nu mu <
      M1Value sigma Lh lambdaUpper alpha lambdaLower nu mu := by
  let B : ℝ :=
    Lh + nu + (alpha / lambdaLower) * mu +
      lambdaUpper ^ 2 * Lh ^ 2 *
        (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
      alpha / lambdaLower *
        (mu * lambdaUpper ^ 2 * Lh ^ 2 +
          (1 + lambdaUpper * Lh) ^ 2 / (2 * mu))
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hden : 0 < 2 * lambdaUpper := mul_pos htwo hlu
  have hscaled' : B * (2 * lambdaUpper) < sigma := by
    rw [mul_comm]
    simpa [B] using hscaled
  have hdiv : B < sigma / (2 * lambdaUpper) := (lt_div_iff₀ hden).mpr hscaled'
  rw [M1Value, M2Value]
  nlinarith [hdiv]

/-- Lemma 3.3: choosing `lambdaUpper` close to `lambdaLower` preserves `M2 < M1`. -/
theorem lemma_3_3_parameter_choice
    (sigma Lh Lu lambdaLower alpha nu mu : ℝ)
    (hnu : 0 < nu) (hmu : 0 < mu) (hlambda : 0 < lambdaLower)
    (hineq : lemma33StrictInequality sigma Lh Lu lambdaLower alpha nu mu) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ lambdaUpper : ℝ,
        lambdaLower ≤ lambdaUpper →
        lambdaUpper < lambdaLower + rho →
        M2Value Lh Lu lambdaUpper alpha lambdaLower nu mu <
          M1Value sigma Lh lambdaUpper alpha lambdaLower nu mu := by
  have hbase :=
    lemma33_base_scaled_inequality sigma Lh Lu lambdaLower alpha nu mu hnu hmu hlambda hineq
  let F : ℝ → ℝ := fun t ↦
    2 * t *
      (Lh + nu + (alpha / lambdaLower) * mu +
        t ^ 2 * Lh ^ 2 *
          (Lh ^ 2 / (2 * nu) + nu + Lh + Lu / (2 * lambdaLower)) +
        alpha / lambdaLower *
          (mu * t ^ 2 * Lh ^ 2 +
            (1 + t * Lh) ^ 2 / (2 * mu)))
  have hcont : Continuous F := by
    unfold F
    continuity
  have hopen : IsOpen {t : ℝ | F t < sigma} := isOpen_lt hcont continuous_const
  have hmem : lambdaLower ∈ {t : ℝ | F t < sigma} := by
    simpa [F] using hbase
  rcases (Metric.isOpen_iff.mp hopen lambdaLower hmem) with ⟨eps, heps_pos, hball⟩
  refine ⟨eps, heps_pos, ?_⟩
  intro lambdaUpper hlower hlt
  have hdist : lambdaUpper ∈ Metric.ball lambdaLower eps := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  have hscaled : F lambdaUpper < sigma := hball hdist
  have hlu_pos : 0 < lambdaUpper := lt_of_lt_of_le hlambda hlower
  exact lemma33_m2_lt_m1_of_scaled sigma Lh Lu lambdaUpper alpha lambdaLower nu mu hlu_pos (by
    simpa [F] using hscaled)

end BotCsetnek2015
