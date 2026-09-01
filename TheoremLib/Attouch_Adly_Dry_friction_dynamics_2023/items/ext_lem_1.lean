import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

private theorem tendsto_tail_setIntegral_Ici {t₀ : ℝ} {h : ℝ → ℝ}
    (h_int : MeasureTheory.IntegrableOn h (Set.Ici t₀)) :
    Filter.Tendsto (fun a : ℝ => ∫ u in Set.Ici a, h u) Filter.atTop (nhds 0) := by
  have hlimit := MeasureTheory.tendsto_setIntegral_of_antitone
    (f := h) (μ := MeasureTheory.volume) (fun a : ℝ => measurableSet_Ici)
    (fun a b hab => Set.Ici_subset_Ici.mpr hab) ⟨t₀, h_int⟩
  have hinter : ⋂ a : ℝ, Set.Ici a = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    rcases exists_nat_gt x with ⟨n, hn⟩
    exact (not_le_of_gt hn) (Set.mem_iInter.mp hx (n : ℝ))
  simpa [hinter] using hlimit

private theorem half_interval_le_tail {t₀ t : ℝ} {h : ℝ → ℝ}
    (ht₀ : t₀ ≤ t / 2) (ht : 0 ≤ t)
    (h_nonneg : ∀ u ∈ Set.Ici t₀, 0 ≤ h u)
    (h_int : MeasureTheory.IntegrableOn h (Set.Ici t₀)) :
    (∫ u in t / 2..t, h u) ≤ ∫ u in Set.Ici (t / 2), h u := by
  have hhalf : t / 2 ≤ t := by linarith
  rw [intervalIntegral.integral_of_le hhalf]
  apply MeasureTheory.setIntegral_mono_set
  · exact h_int.mono_set (Set.Ici_subset_Ici.mpr ht₀)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with u hu
    exact h_nonneg u (ht₀.trans hu)
  · exact Filter.Eventually.of_forall fun u hu => le_of_lt hu.1

/-- Lemma 3.1: a nonincreasing integrable nonnegative function satisfies `t * h t → 0`. -/
theorem lemma_3_1 {t₀ : ℝ} (h : ℝ → ℝ) (h_nonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ h t)
    (h_mono : AntitoneOn h (Set.Ici t₀)) (h_int : MeasureTheory.IntegrableOn h (Set.Ici t₀)) :
    Filter.Tendsto (fun t : ℝ => t * h t) Filter.atTop (nhds 0) := by
  have htail := tendsto_tail_setIntegral_Ici h_int
  have htail_half : Filter.Tendsto (fun t : ℝ => ∫ u in Set.Ici (t / 2), h u)
      Filter.atTop (nhds 0) := by
    convert htail.comp (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)) using 1
  have htail_bound : Filter.Tendsto (fun t : ℝ => 2 * ∫ u in Set.Ici (t / 2), h u)
      Filter.atTop (nhds 0) := by
    simpa using htail_half.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    htail_bound ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * t₀) 0)] with t ht
    have ht₀ : t₀ ≤ t / 2 := by
      have : 2 * t₀ ≤ t := le_trans (le_max_left _ _) ht
      linarith
    have ht_nonneg : 0 ≤ t := le_trans (le_max_right _ _) ht
    exact mul_nonneg ht_nonneg (h_nonneg t (ht₀.trans (by linarith)))
  · filter_upwards [Filter.eventually_ge_atTop (max (2 * t₀) 0)] with t ht
    have ht₀ : t₀ ≤ t / 2 := by
      have : 2 * t₀ ≤ t := le_trans (le_max_left _ _) ht
      linarith
    have ht_nonneg : 0 ≤ t := le_trans (le_max_right _ _) ht
    have hhalf : t / 2 ≤ t := by linarith
    have hconst_int : IntervalIntegrable (fun _ : ℝ => h t) MeasureTheory.volume (t / 2) t := by
      simp
    have hint : IntervalIntegrable h MeasureTheory.volume (t / 2) t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
      apply h_int.mono_set
      intro u hu
      exact ht₀.trans (le_of_lt hu.1)
    have hlower : (t / 2) * h t ≤ ∫ u in t / 2..t, h u := by
      have hmono : ∀ u ∈ Set.Icc (t / 2) t, h t ≤ h u := by
        intro u hu
        exact h_mono (ht₀.trans hu.1) (ht₀.trans (by linarith)) hu.2
      calc
        (t / 2) * h t = ∫ _u in t / 2..t, h t := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        _ ≤ ∫ u in t / 2..t, h u :=
          intervalIntegral.integral_mono_on hhalf hconst_int hint hmono
    have hupper := half_interval_le_tail ht₀ ht_nonneg h_nonneg h_int
    nlinarith [hlower, hupper]

end AttouchAdlyDryFrictionDynamics2023
