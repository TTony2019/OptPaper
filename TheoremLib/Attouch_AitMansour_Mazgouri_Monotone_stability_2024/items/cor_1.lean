import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_thm_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Corollary 4.1: Assume each φ(⋅,μ) is convex, differentiable with 1/β_μ-Lipschitz
  continuous gradient and (9). Then (8) admits a unique strong global solution
  x_μ and estimate (10) holds with m=max(m_μ,m_μ′),
  m_μ=(1+2γ²+2/β_μ²)^{1/2}.

  Deviations: convexity, `HasGradientAt` and `β_μ > 0` are explicit hypotheses
  (section 4.1 context in the paper; convexity and the gradient structure are
  what Baillon–Haddad `ext_thm_4` consumes), and uniqueness is asserted on the
  forward half axis only, as in `thm_1`. -/
theorem cor_1 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup M] (V : Set M) (φ : M → H → ℝ) (gradφ : M → H → H)
    (γ : ℝ) (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H)
    (β : M → ℝ) (k₁ γ₁ : ℝ)
    (hconv : ∀ μ ∈ V, IsConvex (φ μ))
    (hdiff : ∀ μ ∈ V, Differentiable ℝ (φ μ))
    (hgrad_id : ∀ μ ∈ V, ∀ q : H, HasGradientAt (φ μ) (gradφ μ q) q)
    (hgrad : ∀ μ ∈ V, LipschitzWith (Real.toNNReal (1 / (β μ))) (gradφ μ))
    (hsol : ∀ μ ∈ V, ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (h9 : ∀ x_ : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hβ : ∀ μ ∈ V, 0 < β μ) (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1) :
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((β μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((β μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (k₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ γ₁) := by
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ0, hμ0⟩
    have hγpos : 0 < γ := (hsol μ0 hμ0).1
    have hC1 : ∀ μ ∈ V, 0 < β μ ∧ ∀ u v : H,
        β μ * ‖gradφ μ u - gradφ μ v‖ ^ 2 ≤
          inner ℝ (gradφ μ u - gradφ μ v) (u - v) := by
      intro μ hμ
      have hc : CocoerciveOn (β μ) Set.univ (fun x : Set.univ => gradφ μ x) := by
        simpa [one_div] using
          (ext_thm_4 (φ μ) (gradφ μ) (1 / β μ) (one_div_pos.mpr (hβ μ hμ))
            (hconv μ hμ) (hdiff μ hμ) (hgrad_id μ hμ) (hgrad μ hμ))
      exact ⟨hβ μ hμ, fun u v => by
        simpa [real_inner_comm] using
          (hc.2 ⟨u, Set.mem_univ u⟩ ⟨v, Set.mem_univ v⟩)⟩
    have hC2 : 0 < k₁ ∧ 0 < γ₁ ∧ γ₁ ≤ 1 ∧
        ∀ u μ μ', μ ∈ V → μ' ∈ V →
          ‖gradφ μ u - gradφ μ' u‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁ :=
      ⟨hk₁, hγ₁_pos, hγ₁_le, by
        intro u μ μ' hμ hμ'
        exact h9 u μ hμ μ' hμ'⟩
    obtain ⟨hunique, hstable⟩ :=
      thm_1 V gradφ γ u₀ v₀ β k₁ γ₁ hγpos hC1 hC2
    refine ⟨hunique, ?_⟩
    intro μ hμ μ' hμ'
    rcases hstable μ hμ μ' hμ' with
      ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hbound⟩
    obtain ⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ
    have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
      (hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
        (hzuniq y dy ddy hy ht)
    obtain ⟨z', dz', ddz', hz', hz'uniq⟩ := hunique μ' hμ'
    have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
      (hz'uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
        (hz'uniq y' dy' ddy' hy' ht)
    filter_upwards [hbound] with t ht
    intro ht_nonneg
    rw [hxy ht_nonneg, hxy' ht_nonneg]
    exact ht ht_nonneg
  · rw [Set.not_nonempty_iff_eq_empty.mp hV]
    simp

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
