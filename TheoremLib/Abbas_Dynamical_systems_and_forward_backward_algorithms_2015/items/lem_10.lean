import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.def_3
import Mathlib

namespace AbbasDynamical2015

private theorem averagedWith_mono_parameter {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {D : Set H} {a b : ℝ} {T : D → H} (hT : AveragedWith a T)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hab : a ≤ b) : AveragedWith b T := by
  rcases averagedWith_iff.mp hT with ⟨ha, R, hR, hT_eq⟩
  let lam : ℝ := a / b
  let S : D → H := fun x ↦ (1 - lam) • (x : H) + lam • R x
  have hlam_nonneg : 0 ≤ lam := div_nonneg ha.1.le hb.1.le
  have hlam_le_one : lam ≤ 1 := (div_le_one hb.1).mpr hab
  have h_one_sub_lam_nonneg : 0 ≤ 1 - lam := sub_nonneg.mpr hlam_le_one
  have hS : LipschitzWith 1 S := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
    have hSxy :
        S x - S y = (1 - lam) • ((x : H) - y) + lam • (R x - R y) := by
      simp [S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [Subtype.dist_eq, dist_eq_norm] using
      calc
        ‖S x - S y‖ = ‖(1 - lam) • ((x : H) - y) + lam • (R x - R y)‖ := by rw [hSxy]
        _ ≤ ‖(1 - lam) • ((x : H) - y)‖ + ‖lam • (R x - R y)‖ := norm_add_le _ _
        _ = (1 - lam) * ‖(x : H) - y‖ + lam * ‖R x - R y‖ := by
              rw [norm_smul, norm_smul]
              simp [abs_of_nonneg h_one_sub_lam_nonneg, abs_of_nonneg hlam_nonneg]
        _ ≤ (1 - lam) * ‖(x : H) - y‖ + lam * ‖(x : H) - y‖ := by
              nlinarith [hRxy, norm_nonneg ((x : H) - y)]
        _ = ‖(x : H) - y‖ := by ring
  refine averagedWith_iff.mpr ⟨hb, S, hS, ?_⟩
  ext x
  rw [hT_eq]
  dsimp [S, lam]
  have hb0 : b ≠ 0 := ne_of_gt hb.1
  rw [smul_add, smul_smul, smul_smul]
  rw [← add_assoc, ← add_smul]
  have hleft : (1 - b) + b * (1 - a / b) = 1 - a := by
    field_simp [hb0]
    ring
  have hright : b * (a / b) = a := by
    field_simp [hb0]
  rw [hleft, hright]

/-- Lemma 3.2: the composition of two averaged operators is averaged. -/
theorem averaged_composition_constant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T1 T2 : H → H) (alpha1 alpha2 : ℝ)
    (halpha1 : 0 < alpha1 ∧ alpha1 < 1) (halpha2 : 0 < alpha2 ∧ alpha2 < 1)
    (hT1 : IsAveragedOperator T1 alpha1 halpha1) (hT2 : IsAveragedOperator T2 alpha2 halpha2) :
    let delta := (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)
    let alpha := 1 / delta
    IsAveragedOperator (T1 ∘ T2) alpha (by
      change 0 < 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) ∧
        1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) < 1
      have hrecip1 : 1 < (1 / alpha1 : ℝ) := (one_lt_div halpha1.1).mpr halpha1.2
      have hrecip2 : 1 < (1 / alpha2 : ℝ) := (one_lt_div halpha2.1).mpr halpha2.2
      have hdelta_gt_one :
          1 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
        nlinarith [lt_min hrecip1 hrecip2]
      have hdelta_pos :
          0 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
        linarith
      exact ⟨one_div_pos.mpr hdelta_pos,
        (div_lt_one hdelta_pos).mpr hdelta_gt_one⟩) := by
  dsimp only
  have hrecip1 : 1 < (1 / alpha1 : ℝ) := (one_lt_div halpha1.1).mpr halpha1.2
  have hrecip2 : 1 < (1 / alpha2 : ℝ) := (one_lt_div halpha2.1).mpr halpha2.2
  have hdelta_gt_one : 1 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
    nlinarith [lt_min hrecip1 hrecip2]
  have hdelta_pos : 0 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
    linarith
  have halpha :
      0 < 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) ∧
        1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) < 1 :=
    ⟨one_div_pos.mpr hdelta_pos, (div_lt_one hdelta_pos).mpr hdelta_gt_one⟩
  let U1 : ↥(Set.univ : Set H) → ↥(Set.univ : Set H) :=
    fun x => ⟨T1 (x : H), Set.mem_univ _⟩
  let U2 : ↥(Set.univ : Set H) → ↥(Set.univ : Set H) :=
    fun x => ⟨T2 (x : H), Set.mem_univ _⟩
  have hU1 : AveragedWith alpha1 (fun x : Set.univ => (U1 x : H)) := by
    simpa [U1] using
      (isAveragedOperator_iff_averagedWith T1 alpha1 halpha1).mp hT1
  have hU2 : AveragedWith alpha2 (fun x : Set.univ => (U2 x : H)) := by
    simpa [U2] using
      (isAveragedOperator_iff_averagedWith T2 alpha2 halpha2).mp hT2
  let c : ℝ := compositionAveragingConstant alpha1 alpha2
  have hcomp : AveragedWith c (fun x : Set.univ => (U1 (U2 x) : H)) := by
    simpa [c] using (averagedWith_comp (T₁ := U1) (T₂ := U2) hU1 hU2)
  have hden_pos : 0 < 1 - alpha1 * alpha2 := by
    nlinarith [halpha1.1, halpha1.2, halpha2.1, halpha2.2]
  have h_c_le_alpha :
      c ≤ 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) := by
    rcases le_total alpha1 alpha2 with h12 | h21
    · have hrecip : 1 / alpha2 ≤ 1 / alpha1 := one_div_le_one_div_of_le halpha1.1 h12
      rw [min_eq_right hrecip]
      dsimp [c, compositionAveragingConstant]
      have hsum_pos : 0 < 1 + alpha2 := by linarith [halpha2.1]
      have hpaper_alpha : 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (1 / alpha2)) =
          2 * alpha2 / (1 + alpha2) := by
        field_simp [ne_of_gt halpha2.1, ne_of_gt hsum_pos]
        rw [add_comm alpha2 1]
        exact div_self (ne_of_gt hsum_pos)
      have hnonneg : 0 ≤ (alpha2 - alpha1) * (1 - alpha2) :=
        mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr halpha2.2.le)
      rw [hpaper_alpha]
      apply (div_le_div_iff₀ hden_pos hsum_pos).2
      nlinarith
    · have hrecip : 1 / alpha1 ≤ 1 / alpha2 := one_div_le_one_div_of_le halpha2.1 h21
      rw [min_eq_left hrecip]
      dsimp [c, compositionAveragingConstant]
      have hsum_pos : 0 < 1 + alpha1 := by linarith [halpha1.1]
      have hpaper_alpha : 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (1 / alpha1)) =
          2 * alpha1 / (1 + alpha1) := by
        field_simp [ne_of_gt halpha1.1, ne_of_gt hsum_pos]
        rw [add_comm alpha1 1]
        exact div_self (ne_of_gt hsum_pos)
      have hnonneg : 0 ≤ (alpha1 - alpha2) * (1 - alpha1) :=
        mul_nonneg (sub_nonneg.mpr h21) (sub_nonneg.mpr halpha1.2.le)
      rw [hpaper_alpha]
      apply (div_le_div_iff₀ hden_pos hsum_pos).2
      nlinarith
  have hpaper : AveragedWith (1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)))
      (fun x : Set.univ => (U1 (U2 x) : H)) :=
    averagedWith_mono_parameter hcomp halpha h_c_le_alpha
  simpa [U1, U2, Function.comp_def] using hpaper

end AbbasDynamical2015
