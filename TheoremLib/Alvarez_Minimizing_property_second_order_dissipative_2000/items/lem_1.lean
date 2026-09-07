import Mathlib

namespace Alvarez2000

open Filter MeasureTheory

private theorem rawW_antitoneOn_Ici (theta : ℝ → ℝ)
    (hDiff : ContDiffOn ℝ 1 theta (Set.Ici 0)) (g : ℝ → ℝ)
    (hg : ∀ x, deriv theta x ≤ g x)
    (hgInt : ∀ s t, 0 ≤ s → s ≤ t → IntervalIntegrable g volume s t) :
    AntitoneOn (fun u => theta u - ∫ x in 0..u, g x) (Set.Ici 0) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · rfl
  have hDiffIcc : ContDiffOn ℝ 1 theta (Set.Icc s t) := by
    apply hDiff.mono
    intro x hx
    exact hs.trans hx.1
  have hderivInt : IntervalIntegrable (deriv theta) volume s t := by
    have hcont :=
      (hDiffIcc.derivWithin (m := 0) (uniqueDiffOn_Icc hst) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hst.le).congr_ae
    simp only [hst.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have htheta : theta t - theta s = ∫ x in s..t, deriv theta x := by
    simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hDiffIcc hst.le).symm
  have hcomp : theta t - theta s ≤ ∫ x in s..t, g x := by
    rw [htheta]
    exact intervalIntegral.integral_mono hst.le hderivInt (hgInt s t hs hst.le) hg
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hgInt 0 s (by linarith) hs) (hgInt s t hs hst.le)
  dsimp
  rw [← hadd]
  linarith

private theorem intervalIntegral_le_integral_Ioi_of_nonneg {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi 0)) (hgnonneg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in 0..t, g x) ≤ ∫ x in Set.Ioi 0, g x := by
  have htail : 0 ≤ ∫ x in Set.Ioi t, g x :=
    MeasureTheory.integral_nonneg (fun x => hgnonneg x)
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hg ht
  linarith

/-- Lemma 2.2: an eventually lower-bounded `C¹` function with integrable positive derivative
has a finite limit at infinity. -/
theorem converges_of_integrable_positive_derivative (theta : ℝ → ℝ)
    (hDiff : ContDiffOn ℝ 1 theta (Set.Ici 0))
    (hLower : ∃ m : ℝ, ∀ t ∈ Set.Ici 0, m ≤ theta t)
    (hInt : IntegrableOn (fun t => max (deriv theta t) 0) (Set.Ici 0)) :
    ∃ l : ℝ, Tendsto theta atTop (nhds l) := by
  let g : ℝ → ℝ := fun x => max (deriv theta x) 0
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hderiv_le_g : ∀ x, deriv theta x ≤ g x := fun x => le_max_left _ _
  have hIntIoi : IntegrableOn g (Set.Ioi 0) := by
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mp hInt
  have hgInt : ∀ s t, 0 ≤ s → s ≤ t → IntervalIntegrable g volume s t := by
    intro s t hs hst
    apply IntegrableOn.intervalIntegrable
    apply hInt.mono_set
    intro x hx
    exact hs.trans (by simpa [min_eq_left hst] using hx.1)
  let rawW : ℝ → ℝ := fun u => theta u - ∫ x in 0..u, g x
  have hrawW : AntitoneOn rawW (Set.Ici 0) := by
    simpa [rawW] using rawW_antitoneOn_Ici theta hDiff g hderiv_le_g hgInt
  let W : ℝ → ℝ := fun t => rawW (max t 0)
  have hWanti : Antitone W := by
    intro s t hst
    change rawW (max t 0) ≤ rawW (max s 0)
    refine hrawW ?_ ?_ (max_le_max_right 0 hst)
    · exact le_max_right s 0
    · exact le_max_right t 0
  obtain ⟨m, hm⟩ := hLower
  let G : ℝ := ∫ x in Set.Ioi 0, g x
  have hWbdd : BddBelow (Set.range W) := by
    refine ⟨m - G, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hu : 0 ≤ max t 0 := le_max_right _ _
    have hprim : (∫ x in 0..max t 0, g x) ≤ G := by
      exact intervalIntegral_le_integral_Ioi_of_nonneg hIntIoi hg_nonneg hu
    dsimp [W, rawW]
    exact sub_le_sub (hm _ hu) hprim
  have hWlim : Tendsto W atTop (nhds (⨅ t : ℝ, W t)) :=
    tendsto_atTop_ciInf hWanti hWbdd
  have hPlim : Tendsto (fun t => ∫ x in 0..t, g x) atTop (nhds G) := by
    simpa [G] using intervalIntegral_tendsto_integral_Ioi 0 hIntIoi tendsto_id
  refine ⟨(⨅ t : ℝ, W t) + G, ?_⟩
  apply (hWlim.add hPlim).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [W, rawW, max_eq_left ht]

end Alvarez2000
