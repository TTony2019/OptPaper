import Mathlib.Tactic
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.prop_1

/-!
# Remark 2
-/

namespace Alvarez2004

/-- Remark 2: elementary analysis of the quadratic `p(α)`. -/
theorem remark_2_quadratic_positive_interval
    {R1 R2 : ℝ} (hR1_pos : 0 < R1)
    (hR1_le_R2 : R1 ≤ R2) (hR2_lower : 1 ≤ R2) (hR2_upper : R2 < 2) :
    (0 < pCoeff R1 R2 0) ∧
      ∃ alphaStar : ℝ,
          0 < alphaStar ∧ pCoeff R1 R2 alphaStar = 0 ∧
          (∀ alpha : ℝ, 0 ≤ alpha → alpha < alphaStar →
            0 < pCoeff R1 R2 alpha) ∧
          (∀ beta : ℝ, 0 < beta → pCoeff R1 R2 beta = 0 → beta = alphaStar) := by
  set a : ℝ := 1 / R2 - 1 / 2 with ha_def
  set b : ℝ := 2 / R1 - 1 / 2 with hb_def
  set c : ℝ := 1 - 1 / R2 with hc_def
  have hp_eq : ∀ alpha : ℝ, pCoeff R1 R2 alpha = a - b * alpha - c * alpha ^ 2 := by
    intro alpha
    unfold pCoeff
    rw [ha_def, hb_def, hc_def]
  have hR2_pos : 0 < R2 := by linarith
  have hR1_lt_two : R1 < 2 := lt_of_le_of_lt hR1_le_R2 hR2_upper
  have ha_pos : 0 < a := by
    rw [ha_def]
    field_simp [ne_of_gt hR2_pos]
    nlinarith
  have hb_pos : 0 < b := by
    rw [hb_def]
    field_simp [ne_of_gt hR1_pos]
    nlinarith
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    field_simp [ne_of_gt hR2_pos]
    nlinarith
  have hp0_pos : 0 < pCoeff R1 R2 0 := by
    rw [hp_eq 0]
    simp [ha_pos]
  have hstrict_dec :
      ∀ alpha₁ alpha₂ : ℝ, 0 ≤ alpha₁ → alpha₁ < alpha₂ →
        pCoeff R1 R2 alpha₂ < pCoeff R1 R2 alpha₁ := by
    intro alpha₁ alpha₂ hα₁_nonneg hα₁_lt_α₂
    rw [hp_eq alpha₁, hp_eq alpha₂]
    have hdiff_pos : 0 < alpha₂ - alpha₁ := sub_pos.mpr hα₁_lt_α₂
    have hα₂_nonneg : 0 ≤ alpha₂ := by linarith
    have hsum_nonneg : 0 ≤ alpha₁ + alpha₂ := by linarith
    have hfactor_pos : 0 < b + c * (alpha₁ + alpha₂) := by
      have hprod_nonneg : 0 ≤ c * (alpha₁ + alpha₂) := mul_nonneg hc_nonneg hsum_nonneg
      linarith
    have hsub :
        0 < (a - b * alpha₁ - c * alpha₁ ^ 2) -
          (a - b * alpha₂ - c * alpha₂ ^ 2) := by
      have hmul_pos : 0 < (alpha₂ - alpha₁) * (b + c * (alpha₁ + alpha₂)) :=
        mul_pos hdiff_pos hfactor_pos
      have hidentity :
          (a - b * alpha₁ - c * alpha₁ ^ 2) -
            (a - b * alpha₂ - c * alpha₂ ^ 2) =
          (alpha₂ - alpha₁) * (b + c * (alpha₁ + alpha₂)) := by
        ring
      rwa [hidentity]
    linarith
  have h_negative_point : ∃ alpha₀ : ℝ, 0 < alpha₀ ∧ pCoeff R1 R2 alpha₀ < 0 := by
    set alpha₀ : ℝ := a / b + 1 with hα₀_def
    have hα₀_pos : 0 < alpha₀ := by
      rw [hα₀_def]
      have hdiv_pos : 0 < a / b := div_pos ha_pos hb_pos
      linarith
    have hp_α₀_neg : pCoeff R1 R2 alpha₀ < 0 := by
      rw [hp_eq alpha₀, hα₀_def]
      have hb_ne : b ≠ 0 := ne_of_gt hb_pos
      have hcalc :
          a - b * (a / b + 1) - c * (a / b + 1) ^ 2 =
            -b - c * (a / b + 1) ^ 2 := by
        field_simp [hb_ne]
        ring
      rw [hcalc]
      have hterm_nonneg : 0 ≤ c * (a / b + 1) ^ 2 :=
        mul_nonneg hc_nonneg (sq_nonneg _)
      nlinarith
    exact ⟨alpha₀, hα₀_pos, hp_α₀_neg⟩
  rcases h_negative_point with ⟨alpha₀, hα₀_pos, hp_α₀_neg⟩
  have h_cont : Continuous (fun alpha : ℝ => pCoeff R1 R2 alpha) := by
    unfold pCoeff
    continuity
  have h_exists_root :
      ∃ alphaStar ∈ Set.Ioo (0 : ℝ) alpha₀, pCoeff R1 R2 alphaStar = 0 := by
    have hsubset :=
      intermediate_value_Ioo' (show (0 : ℝ) ≤ alpha₀ by linarith)
        (f := fun alpha : ℝ => pCoeff R1 R2 alpha) h_cont.continuousOn
    have hzero_mem :
        (0 : ℝ) ∈ Set.Ioo (pCoeff R1 R2 alpha₀) (pCoeff R1 R2 (0 : ℝ)) := by
      exact ⟨hp_α₀_neg, hp0_pos⟩
    simpa using hsubset hzero_mem
  rcases h_exists_root with ⟨alphaStar, h_alphaStar_interval, h_alphaStar_zero⟩
  have h_alphaStar_pos : 0 < alphaStar := h_alphaStar_interval.1
  have h_pos_on_interval :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha < alphaStar → 0 < pCoeff R1 R2 alpha := by
    intro alpha hα_nonneg hα_lt_alphaStar
    have hp_lt : pCoeff R1 R2 alphaStar < pCoeff R1 R2 alpha :=
      hstrict_dec alpha alphaStar hα_nonneg hα_lt_alphaStar
    rw [h_alphaStar_zero] at hp_lt
    linarith
  have h_unique : ∀ beta : ℝ, 0 < beta → pCoeff R1 R2 beta = 0 → beta = alphaStar := by
    intro beta hbeta_pos hbeta_zero
    by_cases hlt : beta < alphaStar
    · have hpos := h_pos_on_interval beta (le_of_lt hbeta_pos) hlt
      linarith
    · by_cases heq : beta = alphaStar
      · exact heq
      · have hgt : alphaStar < beta := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        have hdec := hstrict_dec alphaStar beta (le_of_lt h_alphaStar_pos) hgt
        rw [h_alphaStar_zero, hbeta_zero] at hdec
        linarith
  exact ⟨hp0_pos, alphaStar, h_alphaStar_pos, h_alphaStar_zero, h_pos_on_interval,
    h_unique⟩

/-- In the unrelaxed case `ρ_k = 1`, one gets `p(α) = 1 / 2 - 3α / 2`
and the positive root is `1 / 3`. -/
theorem remark_2_unrelaxed_root (alpha : ℝ) :
    pCoeff 1 1 alpha = 1 / 2 - (3 / 2) * alpha ∧
      pCoeff 1 1 (1 / 3) = 0 := by
  constructor
  · unfold pCoeff
    ring
  · unfold pCoeff
    ring

end Alvarez2004
