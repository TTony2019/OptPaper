import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

/-- Lemma A.1, the vanishing weighted-average estimate. -/
theorem lemma_A_1 {s₀ α : ℝ} (hα : 1 < α) (a : ℝ → ℝ)
    (ha : ∀ s ∈ Set.Ici s₀, 0 < a s)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) (hs₀ : 0 ≤ s₀)
    (hInt : ∀ t : ℝ, IntervalIntegrable (fun u : ℝ => u ^ (α - 2) * a u) MeasureTheory.volume s₀ t) :
    Filter.Tendsto
      (fun s : ℝ => (s ^ (α - 1))⁻¹ * ∫ u in s₀..s, u ^ (α - 2) * a u)
      Filter.atTop (nhds 0) := by
  let q : ℝ := α - 1
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hr : -1 < α - 2 := by linarith
  have hnonneg : ∀ᶠ s : ℝ in Filter.atTop,
      0 ≤ (s ^ q)⁻¹ * ∫ u in s₀..s, u ^ (α - 2) * a u := by
    filter_upwards [Filter.eventually_gt_atTop (max s₀ 0)] with s hs
    have hs₀s : s₀ ≤ s := le_trans (le_max_left _ _) hs.le
    have hsnonneg : 0 ≤ s := le_trans (le_max_right _ _) hs.le
    apply mul_nonneg
    · exact inv_nonneg.mpr (Real.rpow_nonneg hsnonneg _)
    · apply intervalIntegral.integral_nonneg hs₀s
      intro u hu
      exact mul_nonneg (Real.rpow_nonneg (le_trans hs₀ hu.1) _) (le_of_lt (ha u hu.1))
  rw [show α - 1 = q by rfl, tendsto_order]
  refine ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [hnonneg] with s hs
    linarith
  · intro b hb
    let ε : ℝ := b * q / 2
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hea : ∀ᶠ u : ℝ in Filter.atTop, a u < ε :=
      ha0.eventually_lt tendsto_const_nhds hε
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hea
    let T : ℝ := max (max s₀ 0) T₀
    have hT : 0 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have htail : ∀ u ≥ T, a u ≤ ε := by
      intro u hu
      exact (hT₀ u (le_trans (le_max_right _ _) hu)).le
    let f : ℝ → ℝ := fun u => u ^ (α - 2) * a u
    have hfix : Filter.Tendsto (fun s : ℝ => (s ^ q)⁻¹ * ∫ u in s₀..T, f u)
        Filter.atTop (nhds 0) := by
      have hpow := (tendsto_rpow_neg_atTop hq).congr' <| by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
        rw [Real.rpow_neg hs.le]
      simpa using hpow.mul
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => ∫ u in s₀..T, f u) Filter.atTop
          (nhds (∫ u in s₀..T, f u)))
    have hfixlt : ∀ᶠ s : ℝ in Filter.atTop, (s ^ q)⁻¹ * ∫ u in s₀..T, f u < b / 2 :=
      hfix.eventually_lt tendsto_const_nhds (by linarith)
    filter_upwards [hfixlt, Filter.eventually_gt_atTop T] with s hsfix hs
    have hTs : T ≤ s := hs.le
    have hspos : 0 < s := lt_of_le_of_lt hT hs
    have hIntTs : IntervalIntegrable f MeasureTheory.volume T s := by
      exact ((hInt T).symm.trans (hInt s))
    have hWeightInt : IntervalIntegrable (fun u : ℝ => u ^ (α - 2) * ε) MeasureTheory.volume T s := by
      exact (intervalIntegral.intervalIntegrable_rpow' (a := T) (b := s) hr).mul_const ε
    have hmono : ∫ u in T..s, f u ∂MeasureTheory.volume ≤ ∫ u in T..s, u ^ (α - 2) * ε ∂MeasureTheory.volume := by
      apply intervalIntegral.integral_mono_on hTs hIntTs hWeightInt
      intro u hu
      exact mul_le_mul_of_nonneg_left (htail u hu.1) (Real.rpow_nonneg (le_trans hT hu.1) _)
    have htailbound : ∫ u in T..s, f u ≤ (ε / q) * s ^ q := by
      calc
        ∫ u in T..s, f u ≤ ∫ u in T..s, u ^ (α - 2) * ε := hmono
        _ = ε * ((s ^ q - T ^ q) / q) := by
          rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl hr)]
          dsimp [q]
          ring_nf
        _ ≤ (ε / q) * s ^ q := by
          have hsub' : s ^ q - T ^ q ≤ s ^ q := sub_le_self _ (Real.rpow_nonneg hT _)
          have hdiv : (s ^ q - T ^ q) / q ≤ s ^ q / q := (div_le_div_iff_of_pos_right hq).2 hsub'
          have hmul' : ε * ((s ^ q - T ^ q) / q) ≤ ε * (s ^ q / q) :=
            mul_le_mul_of_nonneg_left hdiv hε.le
          calc
            ε * ((s ^ q - T ^ q) / q) ≤ ε * (s ^ q / q) := hmul'
            _ = (ε / q) * s ^ q := by ring
    have hnormtail : (s ^ q)⁻¹ * ∫ u in T..s, f u ≤ b / 2 := by
      have hmul := mul_le_mul_of_nonneg_left htailbound
        (inv_nonneg.mpr (Real.rpow_nonneg hspos.le q))
      have hsq : s ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hspos _)
      calc
        (s ^ q)⁻¹ * ∫ u in T..s, f u ≤ (s ^ q)⁻¹ * ((ε / q) * s ^ q) := hmul
        _ = ε / q := by
          rw [← mul_assoc, mul_comm (s ^ q)⁻¹, mul_assoc, inv_mul_cancel₀ hsq, mul_one]
        _ = b / 2 := by
          dsimp [ε]
          field_simp [ne_of_gt hq]
    change (s ^ q)⁻¹ * ∫ u in s₀..s, f u < b
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hInt T) hIntTs
    simp only [f]
    rw [← hadd]
    change (s ^ q)⁻¹ * (_ + _) < b
    rw [mul_add]
    have hfix' : (s ^ q)⁻¹ * ∫ u in s₀..T, u ^ (α - 2) * a u < b / 2 := by simpa [f] using hsfix
    have hnormtail' : (s ^ q)⁻¹ * ∫ u in T..s, u ^ (α - 2) * a u ≤ b / 2 := by
      simpa [f] using hnormtail
    nlinarith

end AttouchAdlyDryFrictionDynamics2023
