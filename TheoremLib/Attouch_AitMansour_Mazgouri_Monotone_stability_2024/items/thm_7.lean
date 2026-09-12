import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_9
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_6
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-- Theorem 6.7: Assume the conditions of Theorem 6.1 (βγ>1, each φ(⋅,μ)
  differentiable and δ_μ-strongly convex, (9)) and that x̄ is Lyapunov stable
  for (DIN).
  (i) If lim_{μ→μ̄}(u₀^μ,v₀^μ)=(u₀,v₀), then x̄ is Lyapunov uniformly μ̄-stable.
  (ii) If moreover (u₀^μ,v₀^μ)=(u₀,v₀) for all μ, then x̄ is asymptotically
  uniformly μ̄-stable.

  Deviations from the paper (the previous degenerate proof deduced
  `Subsingleton H` from the Lyapunov hypothesis, trivializing the statement):

  * the Lyapunov hypothesis is imposed on *genuine* strong solutions of
    `DIN(φ,μ̄)` — those whose `dz` is the a.e. derivative of `z` — which is the
    paper's notion of solution; this rules out the formal artifact of the weak
    `DIN` predicate, which does not relate `dx` to `x`;
  * it also records that the reference data `(u₀^μ̄, v₀^μ̄)` lies in the
    stability neighbourhood, which the paper leaves implicit;
  * a uniform lower bound `δmin ≤ δ_μ` is assumed, as the μ̄-uniform statement
    requires;
  * part (ii) is stated in its correct form: the perturbed trajectories
    converge to the minimizers `x̄_μ` of their own functionals (not to `x̄_{μ̄}`,
    which is false for `μ ≠ μ̄`), and `x̄_μ` is Hölder-close to `x̄_{μ̄}`. -/
theorem thm_7 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (xbar : M → H)
    (β γ : ℝ) (δ : M → ℝ) (cmin k₁ γ₁ : ℝ) (μbar : M)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hcmin_pos : 0 < cmin) (hcmin : ∀ μ : M, cmin ≤ energyRate β γ (δ μ))
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ : M,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ : M,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hcrit : ∀ μ : M, gradφ μ (xbar μ) = 0)
    (hlyap : ∀ ε > 0, ∃ η > 0,
      ‖u₀ μbar - xbar μbar‖ < η ∧ ‖v₀ μbar‖ < η ∧
      ∀ z₀ w₀ : H, ‖z₀ - xbar μbar‖ < η → ‖w₀‖ < η →
        ∀ z dz ddz : ℝ → H,
          DIN (φ μbar) (gradφ μbar) (hessφ μbar) γ β z₀ w₀ z dz ddz →
          (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt z (dz t) t) →
          ∀ t ≥ 0, ‖z t - xbar μbar‖ < ε)
    (hconv_init : Tendsto (fun μ : M => (u₀ μ, dinAuxInitial gradφ β γ u₀ v₀ μ))
      (nhds μbar) (nhds (u₀ μbar, dinAuxInitial gradφ β γ u₀ v₀ μbar))) :
    (∀ ε > 0, ∃ δ > 0, ∀ μ : M, dist μ μbar < δ → ‖u₀ μ - xbar μbar‖ < δ →
      ∀ t ≥ 0, ‖x μ t - xbar μbar‖ < ε) ∧
    ((∀ μ : M, u₀ μ = u₀ μbar ∧ v₀ μ = v₀ μbar) →
      ∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ)) ∧
        ‖xbar μ - xbar μbar‖ ≤ (β * k₁ / cmin) * dist μ μbar ^ γ₁) := by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  constructor
  · -- (i) Lyapunov uniform μ̄-stability, by the paper's argument
    intro ε hε
    obtain ⟨η, hη_pos, hbase_u, hbase_v, htraj⟩ := hlyap (ε / 3) (by positivity)
    have hε₁ : 0 < ε / (3 * Real.sqrt 2) := by positivity
    have hev : ∀ᶠ μ in nhds μbar,
        dist (u₀ μ, dinAuxInitial gradφ β γ u₀ v₀ μ)
          (u₀ μbar, dinAuxInitial gradφ β γ u₀ v₀ μbar) < ε / (3 * Real.sqrt 2) :=
      (Metric.tendsto_nhds.mp hconv_init) _ hε₁
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hev
    -- stability radius enforcing the Hölder term of (17) to be < ε/3
    set δrate : ℝ := min 1 (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) with hδrate_def
    have hr_pos : 0 < ((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hδrate_pos : 0 < δrate := lt_min one_pos hr_pos
    have hrate : (β * k₁ / cmin) * δrate ^ γ₁ ≤ ε / 3 := by
      have hle : δrate ≤ ((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁) := min_le_right _ _
      have hpow : δrate ^ γ₁ ≤ (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) ^ γ₁ :=
        Real.rpow_le_rpow hδrate_pos.le hle hγ₁_pos.le
      have hval : (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) ^ γ₁ = (ε * cmin) / (3 * β * k₁) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (ε * cmin) / (3 * β * k₁))]
        rw [one_div_mul_cancel hγ₁_pos.ne', Real.rpow_one]
      calc (β * k₁ / cmin) * δrate ^ γ₁ ≤ (β * k₁ / cmin) * ((ε * cmin) / (3 * β * k₁)) := by
            rw [← hval]
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ε / 3 := by
            field_simp [hcmin_pos.ne', hk₁.ne', hβ.ne']
    refine ⟨min (min δ₁ η) δrate, lt_min (lt_min hδ₁_pos hη_pos) hδrate_pos, ?_⟩
    intro μ hμ _ t ht
    have hμ₁ : dist μ μbar < δ₁ :=
      lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hμη : dist μ μbar < η :=
      lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hμrate : dist μ μbar < δrate := lt_of_lt_of_le hμ (min_le_right _ _)
    -- the μ̄-trajectory stays within ε/3 of x̄
    have href : ‖x μbar t - xbar μbar‖ < ε / 3 :=
      htraj (u₀ μbar) (v₀ μbar) hbase_u hbase_v (x μbar) (dx μbar) (ddx μbar)
        (hDIN μbar) (hderiv μbar) t ht
    -- the (transformed) initial data of the two trajectories are ε/3-close
    have hinit : Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) < ε / 3 := by
      have hdist := hδ₁ (show dist μ μbar < δ₁ from hμ₁)
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hdist
      set m : ℝ := max ‖u₀ μ - u₀ μbar‖
        ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ with hm_def
      have hm_nonneg : 0 ≤ m :=
        le_trans (norm_nonneg _) (le_max_left _ _)
      have hsqrt : Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) ≤
          Real.sqrt 2 * m := by
        rw [← Real.sqrt_sq hm_nonneg, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        apply Real.sqrt_le_sqrt
        rw [hm_def]
        nlinarith [le_max_left ‖u₀ μ - u₀ μbar‖
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖,
          le_max_right ‖u₀ μ - u₀ μbar‖
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖,
          norm_nonneg (u₀ μ - u₀ μbar),
          norm_nonneg (dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar)]
      have hm : m < ε / (3 * Real.sqrt 2) := hdist
      have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      calc Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2)
          ≤ Real.sqrt 2 * m := hsqrt
        _ < Real.sqrt 2 * (ε / (3 * Real.sqrt 2)) := by
            exact mul_lt_mul_of_pos_left hm hsqrt2
        _ = ε / 3 := by
            field_simp
    -- Theorem 6.1's estimate, with the exponential terms bounded by 1
    have hexp_le : Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar)) :=
        lt_of_lt_of_le hcmin_pos (le_trans (hcmin μ) (le_max_left _ _))
      nlinarith
    have hone : 1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) ≤ 1 := by
      linarith [Real.exp_nonneg (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)]
    have hrpow : 0 ≤ ‖μ - μbar‖ ^ γ₁ := Real.rpow_nonneg (norm_nonneg _) _
    have hest := thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ
      hdiff hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μbar t ht
    have hterm1 : Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) *
        Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) ≤
        Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) :=
      mul_le_of_le_one_left (Real.sqrt_nonneg _) hexp_le
    have hterm2 : (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
            ‖μ - μbar‖ ^ γ₁ ≤
        (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := by
      have h1 : (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) ≤
          (β * k₁ / cmin) * 1 :=
        mul_le_mul
          (div_le_div_of_nonneg_left (by positivity) hcmin_pos (le_trans (hcmin μ) (le_max_left _ _)))
          hone (sub_nonneg.mpr hexp_le) (div_nonneg (by positivity) hcmin_pos.le)
      calc (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
            ‖μ - μbar‖ ^ γ₁
          ≤ (β * k₁ / cmin) * 1 * ‖μ - μbar‖ ^ γ₁ := mul_le_mul_of_nonneg_right h1 hrpow
        _ = (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := by ring
    have hfirst : ‖x μ t - x μbar t‖ < ε / 3 + ε / 3 := by
      have h2 : (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ ≤ (β * k₁ / cmin) * δrate ^ γ₁ :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _)
            (show ‖μ - μbar‖ ≤ δrate by rw [← dist_eq_norm]; exact hμrate.le) hγ₁_pos.le)
          (by positivity)
      calc ‖x μ t - x μbar t‖ ≤
            Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) *
              Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
                dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) +
          (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
              ‖μ - μbar‖ ^ γ₁ := hest
        _ ≤ Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) +
            (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := add_le_add hterm1 hterm2
        _ < ε / 3 + ε / 3 := by
            linarith [hinit, h2, hrate]
    have htri : ‖x μ t - xbar μbar‖ ≤
        ‖x μ t - x μbar t‖ + ‖x μbar t - xbar μbar‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x μ t) (x μbar t) (xbar μbar)
    have hsum := add_lt_add hfirst href
    linarith
  · -- (ii) asymptotic μ̄-stability in the corrected form
    intro _ μ
    refine ⟨din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
      (fun p q => energyStrong_of_strongConvex hβ hβγ (hstrong μ) (hgrad μ) p q) hβ
      (energyRate_pos hβ hγ (hstrong μ).1 hβγ) (hcrit μ), ?_⟩
    have hgap := (thm_6 φ gradφ hessφ x dx ddx u₀ v₀ xbar β γ δ k₁ γ₁ hβγ hβ hγ hdiff
      hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 hcrit).2.2 μ μbar
    have hcoef : β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar)) ≤ β * k₁ / cmin :=
      div_le_div_of_nonneg_left (by positivity) hcmin_pos (le_trans (hcmin μ) (le_max_left _ _))
    calc ‖xbar μ - xbar μbar‖ ≤
          (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * ‖μ - μbar‖ ^ γ₁ := hgap
      _ ≤ (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (β * k₁ / cmin) * dist μ μbar ^ γ₁ := by rw [dist_eq_norm]

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
