import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_8

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter MeasureTheory

/-- Theorem 7.4: Assume for some α>0 that A_μ is α-cocoercive for each μ.
  Given T>0 with γT+T²/α∈[0,1), suppose the operator discrepancy along the
  reference trajectory vanishes uniformly in time:
  `‖A_μ(x_{μ̄}(t)) − A_{μ̄}(x_{μ̄}(t))‖ ≤ D_μ` on `[0,T]` with `D_μ → 0`.
  Then x_μ converges uniformly on [0,T] to x_{μ̄} as μ→μ̄, u₀^μ→u₀ and v₀^μ→v₀.

  Compared with the paper: the estimate is *derived* from Theorem 7.1
  (`thm_8_general`) instead of being assumed; the paper's hypothesis is the
  a.e.-in-`t` continuity of `μ ↦ A_μ(x_{μ̄}(t))`, and its proof appeals to
  "dominant convergence ... uniformly in t and x".  This uniform-in-time
  vanishing of the operator discrepancy is exactly what the argument uses, and
  it is made an explicit hypothesis here (`hD`, `hDbound`); a.e. pointwise
  continuity alone does not imply it. -/
theorem thm_9 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (V : Set M) (μbar : M) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ : M, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hγT : γ * T + T ^ 2 / α < 1)
    (hsol : ∀ μ : M,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hV : V ∈ nhds μbar) (hμbar : μbar ∈ V)
    (hD : M → ℝ) (hD_lim : Tendsto hD (nhds μbar) (nhds 0))
    (hDbound : ∀ μ : M, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖A μ (x μbar s) - A μbar (x μbar s)‖ ≤ hD μ)
    (hu₀ : Tendsto u₀ (nhds μbar) (nhds (u₀ μbar)))
    (hv₀ : Tendsto v₀ (nhds μbar) (nhds (v₀ μbar))) :
    Tendsto (fun μ : M => pathSupNorm T (fun t => x μ t - x μbar t))
      (nhds μbar) (nhds 0) := by
  -- The discrepancy bound required by `thm_8_general`, obtained from the
  -- Lipschitz continuity (cocoercivity) and the uniform bound along `x μbar`.
  have hdisc : ∀ μ ∈ V, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v : H,
      ‖v - x μbar s‖ ≤ ‖u₀ μ - u₀ μbar‖ →
        ‖A μ v - A μbar v‖ ≤ 2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ := by
    intro μ _ s hs v hv
    have hLμ (a b : H) : ‖A μ a - A μ b‖ ≤ α⁻¹ * ‖a - b‖ := by
      have h := (cocoercive_implies_lipschitz (A μ) α (hcoco μ)).dist_le_mul a b
      simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
    have hLbar (a b : H) : ‖A μbar a - A μbar b‖ ≤ α⁻¹ * ‖a - b‖ := by
      have h := (cocoercive_implies_lipschitz (A μbar) α (hcoco μbar)).dist_le_mul a b
      simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
    have htri : ‖A μ v - A μbar v‖ ≤
        (α⁻¹ * ‖v - x μbar s‖ + hD μ) + α⁻¹ * ‖x μbar s - v‖ := by
      have h1 : ‖A μ v - A μbar v‖ ≤
          ‖A μ v - A μ (x μbar s)‖ + ‖A μ (x μbar s) - A μbar (x μbar s)‖ +
            ‖A μbar (x μbar s) - A μbar v‖ := by
        rw [show A μ v - A μbar v = (A μ v - A μ (x μbar s)) +
            (A μ (x μbar s) - A μbar (x μbar s)) + (A μbar (x μbar s) - A μbar v)
            by abel]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have h2 := hLμ v (x μbar s)
      have h3 : ‖A μ (x μbar s) - A μbar (x μbar s)‖ ≤ hD μ := hDbound μ s hs
      have h4 := hLbar (x μbar s) v
      linarith
    refine htri.trans ?_
    have hsym : ‖x μbar s - v‖ = ‖v - x μbar s‖ := norm_sub_rev _ _
    have hpos : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    rw [hsym]
    nlinarith [hv, norm_nonneg (v - x μbar s), hDbound μ s hs, norm_nonneg (A μ (x μbar s) - A μbar (x μbar s))]
  -- Theorem 7.1's estimate with that discrepancy bound
  have hest : ∀ᶠ μ in nhds μbar, pathSupNorm T (fun t => x μ t - x μbar t) ≤
      α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)) := by
    filter_upwards [hV] with μ hμ
    exact thm_8_general V A x dx ddx u₀ v₀ α γ T hα hT (fun μ _ => hcoco μ)
      (fun μ _ => hsol μ) hγT μ hμ μbar hμbar
      (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ) (hdisc μ hμ)
  -- the right-hand side tends to 0
  have hRHS : Tendsto (fun μ : M =>
      α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)))
      (nhds μbar) (nhds 0) := by
    have h1 : Tendsto (fun μ : M => ‖u₀ μ - u₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hu₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => u₀ μbar)
        (nhds μbar) (nhds (u₀ μbar)))).norm
    have h2 : Tendsto (fun μ : M => ‖v₀ μ - v₀ μbar‖) (nhds μbar) (nhds 0) := by
      simpa using (hv₀.sub (tendsto_const_nhds : Tendsto (fun _ : M => v₀ μbar)
        (nhds μbar) (nhds (v₀ μbar)))).norm
    have h3 : Tendsto (fun μ : M => T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ))
        (nhds μbar) (nhds 0) := by
      have h4 : Tendsto (fun μ : M => 2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)
          (nhds μbar) (nhds 0) := by
        simpa using (h1.const_mul (2 * α⁻¹)).add hD_lim
      simpa using h4.const_mul (T ^ 2)
    have hsum : Tendsto (fun μ : M =>
        ‖u₀ μ - u₀ μbar‖ + T * ‖v₀ μ - v₀ μbar‖ +
          T ^ 2 * (2 * α⁻¹ * ‖u₀ μ - u₀ μbar‖ + hD μ)) (nhds μbar) (nhds 0) := by
      simpa using (h1.add (h2.const_mul T)).add h3
    simpa using hsum.const_mul (α / (α - α * γ * T - T ^ 2))
  refine squeeze_zero' ?_ hest hRHS
  filter_upwards with μ
  unfold pathSupNorm
  exact Real.sSup_nonneg fun q hq => by
    obtain ⟨t, _, rfl⟩ := hq
    exact norm_nonneg _

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
