import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_5

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Corollary 4.2: Assume T(⋅,μ) is a contraction for all μ and (12).
  Then system (11) admits a unique strong global solution and the estimate
  holds with m=(1+2γ²+8)^{1/2}.

  Deviations: the contraction hypothesis is expressed by `ext_def_5`, whose
  constant is required to be *strictly* smaller than `1`, whereas the paper
  (Definition 2.1) calls every 1-Lipschitz map a contraction and its proof only
  uses non-expansiveness — the boundary case `c = 1` is therefore not covered
  here.  Existence/uniqueness of the solution of (11) is supplied by `hsol`,
  only the forward-half-axis uniqueness and the estimate being concluded. -/
theorem cor_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (Tmap : M → H → H) (γ : ℝ) (x dx ddx : M → ℝ → H)
    (u₀ v₀ : M → H) (θ₁ θ₂ : ℝ)
    (hcontr : ∀ μ ∈ V, ext_def_5 (Tmap μ))
    (hsol : ∀ μ ∈ V, ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hθ₁ : 0 < θ₁) (hθ₂_pos : 0 < θ₂) (hθ₂_le : θ₂ ≤ 1)
    (h12 : ∀ u : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖Tmap μ u - Tmap μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂) :
    let m := Real.sqrt (1 + 2 * γ ^ 2 + 8)
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂) := by
  dsimp
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ₀, hμ₀⟩
    have hC₁ : ∀ μ ∈ V, 0 < (1 / 2 : ℝ) ∧ ∀ u v : H,
        (1 / 2 : ℝ) * ‖(u - Tmap μ u) - (v - Tmap μ v)‖ ^ 2 ≤
          inner ℝ ((u - Tmap μ u) - (v - Tmap μ v)) (u - v) := by
      intro μ hμ
      rcases hcontr μ hμ with ⟨c, hc0, hc1, hc⟩
      have hLip : LipschitzWith 1 (fun z : (Set.univ : Set H) => Tmap μ (z : H)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simp only [dist_eq_norm, Subtype.dist_eq]
        calc
          ‖Tmap μ (z : H) - Tmap μ (w : H)‖ ≤ c * ‖(z : H) - w‖ := by
            simpa only [dist_eq_norm, Subtype.dist_eq] using hc (z : H) (w : H)
          _ ≤ 1 * ‖(z : H) - w‖ := by
            gcongr
      have hresidual :=
        (lipschitzWith_one_iff_residualMap_cocoerciveOn_half
          (fun z : (Set.univ : Set H) => Tmap μ (z : H))).mp hLip
      have hpoint :=
        (CocoerciveOn.pointwise_iff (fun z : H => z - Tmap μ z)
          (1 / 2 : ℝ) (by norm_num)).mp (by simpa [residualMap] using hresidual)
      refine ⟨by norm_num, ?_⟩
      intro u v
      simpa using hpoint v u
    have hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
        ∀ u μ μ', μ ∈ V → μ' ∈ V →
          ‖(u - Tmap μ u) - (u - Tmap μ' u)‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂ := by
      refine ⟨hθ₁, hθ₂_pos, hθ₂_le, ?_⟩
      intro u μ μ' hμ hμ'
      have hres : (u - Tmap μ u) - (u - Tmap μ' u) =
          -(Tmap μ u - Tmap μ' u) := by abel
      rw [hres, norm_neg]
      exact h12 u μ hμ μ' hμ'
    have hmain := thm_1 V (fun μ u => u - Tmap μ u) γ u₀ v₀
      (fun _ => (1 / 2 : ℝ)) θ₁ θ₂ (hsol μ₀ hμ₀).1 hC₁ hC₂
    refine ⟨hmain.1, ?_⟩
    intro μ hμ μ' hμ'
    rcases hmain.2 μ hμ μ' hμ' with ⟨x₁, x₂, hx₁, hx₂, hbound⟩
    rcases hx₁ with ⟨dx₁, ddx₁, hx₁sol⟩
    rcases hx₂ with ⟨dx₂, ddx₂, hx₂sol⟩
    obtain ⟨z₁, dz₁, ddz₁, hz₁, hz₁uniq⟩ := hmain.1 μ hμ
    have hx₁eq : Set.EqOn (x μ) x₁ (Set.Ici 0) := fun t ht =>
      (hz₁uniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
        (hz₁uniq x₁ dx₁ ddx₁ hx₁sol ht)
    obtain ⟨z₂, dz₂, ddz₂, hz₂, hz₂uniq⟩ := hmain.1 μ' hμ'
    have hx₂eq : Set.EqOn (x μ') x₂ (Set.Ici 0) := fun t ht =>
      (hz₂uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
        (hz₂uniq x₂ dx₂ ddx₂ hx₂sol ht)
    have hrate : Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((1 / 2 : ℝ) ^ 2)) =
        Real.sqrt (1 + 2 * γ ^ 2 + 8) := by
      congr 1
      norm_num
    filter_upwards [hbound] with t ht
    intro ht_nonneg
    have ht_bound := ht ht_nonneg
    rw [← hx₁eq ht_nonneg, ← hx₂eq ht_nonneg] at ht_bound
    simpa only [max_self, hrate] using ht_bound
  · simp [Set.not_nonempty_iff_eq_empty.mp hV]

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
