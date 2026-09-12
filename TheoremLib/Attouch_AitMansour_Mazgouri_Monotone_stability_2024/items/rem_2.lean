import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_3
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_8
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter MeasureTheory

open scoped Topology

/-- A continuous function on `[0,T]` which is bounded by a constant almost
  everywhere on `[0,T]` is bounded by it everywhere: otherwise continuity gives
  an interval of positive length on which the bound fails, contradicting the
  a.e. statement. -/
theorem le_of_ae_le_const_of_continuousOn {f : ℝ → ℝ} {T M : ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hae : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → f t ≤ M) :
    ∀ t ∈ Set.Icc 0 T, f t ≤ M := by
  by_contra h
  push_neg at h
  obtain ⟨t, ht, hlt⟩ := h
  have hev : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) T] t, M < f s :=
    (hf.continuousWithinAt ht).eventually (isOpen_Ioi.mem_nhds hlt)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp hev
  set a : ℝ := max 0 (t - δ / 2) with ha
  set b : ℝ := min T (t + δ / 2) with hb
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hab : a < b := by
    rw [ha, hb]
    exact max_lt (lt_min hT (by linarith)) (lt_min (by linarith) (by linarith))
  have hsub : Set.Icc a b ⊆ {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ M < f s} := by
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨le_trans (le_max_left _ _) hs.1, le_trans hs.2 (min_le_left _ _)⟩
    have hdist : dist s t < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      have hsa : t - δ / 2 ≤ s := le_trans (le_max_right _ _) hs.1
      have hsb : s ≤ t + δ / 2 := le_trans hs.2 (min_le_right _ _)
      constructor <;> linarith
    exact ⟨hsT, hδf hdist hsT⟩
  have hpos : 0 < MeasureTheory.volume (Set.Icc a b) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hnull : MeasureTheory.volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ M < f s} = 0 := by
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with s hs
    rintro ⟨hsT, hsM⟩
    exact absurd (hs hsT) (not_le.mpr hsM)
  have hle : MeasureTheory.volume (Set.Icc a b) ≤ 0 := by
    rw [← hnull]
    exact MeasureTheory.measure_mono hsub
  exact absurd hle (not_le.mpr hpos)

/-- Remark 5.3: If μ_n→μ̄, x_n(t)=x_{μ_n}(t), and x(t)=x_{μ̄}(t),
  Theorem 5.1 ensures x_n converges uniformly on [0,T] to x whenever
  u₀^n→u₀, ṿ₀^n→v₀, the values belong to B(0,r) and (A_{μ_n}) converges to A
  relative to D_r.

  The uniform estimate is *derived* here from Theorem 5.1 (`thm_2`), not
  assumed: the sup-norm difference is bounded by the right-hand side of (3),
  whose limit is computed from the convergence of the initial data and of
  `D_r(A_μ, A_μ̄)`.  The additional hypothesis `hα_bound` keeps the coefficient
  `m = (1 + 2γ² + 2/α²)^{1/2}` of (3) bounded near `μ̄` (in the paper `α` is a
  fixed constant), which is exactly what makes that right-hand side tend to 0. -/
theorem rem_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (μbar : M) (r T : ℝ)
    (hr : 0 < r) (hT : 0 < T)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hu₀ : Tendsto u₀ (nhds μbar) (nhds (u₀ μbar)))
    (hv₀ : Tendsto v₀ (nhds μbar) (nhds (v₀ μbar)))
    (hball : ∀ μ ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r)
    (hV : V ∈ nhds μbar) (hμbar : μbar ∈ V)
    (hconv_A : Tendsto (fun μ : M => def_6 r hr (A μ) (A μbar)) (nhds μbar) (nhds 0))
    (hα_bound : ∀ᶠ μ in nhds μbar, α μbar ≤ α μ) :
    Tendsto (fun μ : M => pathSupNorm T (fun t => x μ t - x μbar t)) (nhds μbar) (nhds 0) := by
  let m₀ : ℝ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2)
  have hm₀_pos : 0 < m₀ := by
    have hαbar : 0 < α μbar := (hC₁ μbar hμbar).1
    dsimp [m₀]
    apply Real.sqrt_pos.mpr
    have h2 : 0 < 2 / (α μbar) ^ 2 := by positivity
    nlinarith [sq_nonneg γ]
  -- the right-hand side of (3) tends to 0
  have hsqrt : Tendsto (fun μ : M =>
      Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2)) (nhds μbar) (nhds 0) := by
    have ha : Tendsto (fun μ : M => ‖u₀ μ - u₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hu₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => u₀ μbar)
        (nhds μbar) (nhds (u₀ μbar)))).norm
    have hb : Tendsto (fun μ : M => ‖v₀ μ - v₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hv₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => v₀ μbar)
        (nhds μbar) (nhds (v₀ μbar)))).norm
    simpa using ((ha.pow 2).add (hb.pow 2)).sqrt
  have hRHS : Tendsto (fun μ : M =>
      Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar))
      (nhds μbar) (nhds 0) := by
    have h1 : Tendsto (fun μ : M =>
        Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2))
        (nhds μbar) (nhds (Real.exp (m₀ * T) * 0)) := hsqrt.const_mul _
    have h2 : Tendsto (fun μ : M =>
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar))
        (nhds μbar) (nhds (m₀⁻¹ * (Real.exp (m₀ * T) - 1) * 0)) :=
      hconv_A.const_mul _
    simpa using h1.add h2
  -- the uniform estimate of Theorem 5.1
  have hbound : ∀ᶠ μ in nhds μbar, pathSupNorm T (fun t => x μ t - x μbar t) ≤
      Real.exp (m₀ * T) * Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
        m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar) := by
    filter_upwards [hV, hα_bound] with μ hμV hαμ
    have hpt := thm_2 V A γ x dx ddx u₀ v₀ α r T hC₁ hsol hr hT hball μ hμV μbar hμbar
    have hαμ' : 0 < α μ := (hC₁ μ hμV).1
    have hαbar' : 0 < α μbar := (hC₁ μbar hμbar).1
    have hm : max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2))
        (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2)) = m₀ := by
      have hle : Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2) ≤
          Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μbar) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hsq : (α μbar) ^ 2 ≤ (α μ) ^ 2 := by nlinarith
        have hdiv : 2 / (α μ) ^ 2 ≤ 2 / (α μbar) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
        linarith
      rw [max_eq_right hle]
    have hcont : ContinuousOn (fun t => ‖x μ t - x μbar t‖) (Set.Icc (0 : ℝ) T) := by
      have hμac := ((hsol μ hμV).2).1 T hT
      have hbarac := ((hsol μbar hμbar).2).1 T hT
      exact (((hμac.1.continuousOn).mono Set.Icc_subset_uIcc).sub
        ((hbarac.1.continuousOn).mono Set.Icc_subset_uIcc)).norm
    have hall : ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖x μ t - x μbar t‖ ≤ Real.exp (m₀ * T) *
            Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖v₀ μ - v₀ μbar‖ ^ 2) +
          m₀⁻¹ * (Real.exp (m₀ * T) - 1) * def_6 r hr (A μ) (A μbar) :=
      le_of_ae_le_const_of_continuousOn hT hcont (hpt.mono fun s hs hsT => by
        simpa only [hm] using hs hsT)
    exact pathSupNorm_le_of_forall hT.le hall
  refine squeeze_zero' ?_ hbound hRHS
  filter_upwards with μ
  unfold pathSupNorm
  exact Real.sSup_nonneg fun q hq => by
    obtain ⟨t, _, rfl⟩ := hq
    exact norm_nonneg _

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
