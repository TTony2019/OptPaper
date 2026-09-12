import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Remark 3.2(i): If α₀:=sup_{μ∈V(μ̄)}α_μ<+∞ and α is constant on V,
  the conclusion of Theorem 3.1 holds with
  m₀=(1+2γ²+2/α₀²)^{1/2}.

  Deviation: the paper mixes the boundedness assumption `sup α_μ < +∞` with
  the constancy of `α`; the strong reading `α_μ ≡ α₀` is formalized here (with
  the `BddAbove` and `α₀ = sSup` witnesses kept as unused hypotheses of the
  statement). -/
theorem rem_1 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (θ₁ θ₂ : ℝ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (_hα_bdd : BddAbove (α '' V))
    (α₀ : ℝ) (_hα₀ : α₀ = sSup (α '' V))
    (hα_const : ∀ μ ∈ V, α μ = α₀) :
    let m₀ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α₀ ^ 2))
    ∀ μ ∈ V, ∀ μ' ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      ‖x μ t - x μ' t‖ ≤ Real.exp (m₀ * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        (θ₁ / m₀) * (Real.exp (m₀ * t) - 1) * ‖μ - μ'‖ ^ θ₂ := by
  dsimp only
  intro μ hμ μ' hμ'
  rcases thm_1 V A γ u₀ v₀ α θ₁ θ₂ (hsol μ hμ).1 hC₁ hC₂ with ⟨hunique, hpairs⟩
  specialize hpairs μ hμ μ' hμ'
  dsimp only at hpairs
  rcases hpairs with ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hyy⟩
  obtain ⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ
  have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
    (hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
      (hzuniq y dy ddy hy ht)
  obtain ⟨z', dz', ddz', hz', hz'uniq⟩ := hunique μ' hμ'
  have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
    (hz'uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
      (hz'uniq y' dy' ddy' hy' ht)
  filter_upwards [hyy] with t ht
  intro ht_nonneg
  have ht_bound := ht ht_nonneg
  rw [← hxy ht_nonneg, ← hxy' ht_nonneg] at ht_bound
  simpa [hα_const μ hμ, hα_const μ' hμ'] using ht_bound

/-- Remark 3.2(ii): common initial data case. If (u₀^μ,v₀^μ)=(u₀,v₀) for
  all μ, then only the perturbation term survives. -/
theorem rem_1_common_init {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (θ₁ θ₂ : ℝ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hu₀ : ∀ μ ∈ V, ∀ μ' ∈ V, u₀ μ = u₀ μ') (hv₀ : ∀ μ ∈ V, ∀ μ' ∈ V, v₀ μ = v₀ μ') :
    ∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂ := by
  intro μ hμ μ' hμ'
  dsimp only
  rcases thm_1 V A γ u₀ v₀ α θ₁ θ₂ (hsol μ hμ).1 hC₁ hC₂ with ⟨hunique, hpairs⟩
  specialize hpairs μ hμ μ' hμ'
  dsimp only at hpairs
  rcases hpairs with ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hyy⟩
  obtain ⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ
  have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
    (hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
      (hzuniq y dy ddy hy ht)
  obtain ⟨z', dz', ddz', hz', hz'uniq⟩ := hunique μ' hμ'
  have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
    (hz'uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
      (hz'uniq y' dy' ddy' hy' ht)
  filter_upwards [hyy] with t ht
  intro ht_nonneg
  have ht_bound := ht ht_nonneg
  rw [← hxy ht_nonneg, ← hxy' ht_nonneg] at ht_bound
  simpa [hu₀ μ hμ μ' hμ', hv₀ μ hμ μ' hμ'] using ht_bound

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
