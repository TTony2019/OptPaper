import Foundation.SetValued.Resolvent
import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_5
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open scoped Pointwise

/-- Corollary 4.3: Assume for all λ>0,
  ‖J_λ^A(u,μ)−J_λ^A(u,μ′)‖≤λθ₁‖μ−μ′‖^{θ₂}.
  Then for given λ>0, (14) admits a unique strong global solution and the
  estimate holds with m=(1+2γ²+2/λ²)^{1/2}.

  Deviations: maximal monotonicity of the `A_μ` is an explicit hypothesis; the
  perturbation condition (15) is stated for every `λ′ > 0` and every choice of
  resolvent representative `J′` (the paper writes `J_λ^A` as if single-valued,
  which is only formally stronger); and existence/uniqueness of the solution of
  (14) is supplied by `hsol`. -/
theorem cor_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (A : M → SetValuedOperator H H) (hA : ∀ μ ∈ V, (A μ).IsMaximalMonotone)
    (J : M → H → H) (γ lam θ₁ θ₂ : ℝ) (x dx ddx : M → ℝ → H)
    (u₀ v₀ : M → H)
    (hlam : 0 < lam) (hθ₁ : 0 < θ₁) (hθ₂_pos : 0 < θ₂) (hθ₂_le : θ₂ ≤ 1)
    (hJ : ∀ μ ∈ V, ∀ x_ : H,
      J μ x_ ∈ SetValuedOperator.resolvent (lam • A μ) x_)
    (h15 : ∀ (lam' : ℝ) (_ : 0 < lam'),
      ∀ (J' : M → H → H), (∀ μ ∈ V, ∀ x_ : H,
        J' μ x_ ∈ SetValuedOperator.resolvent (lam' • A μ) x_) →
      ∀ u : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖J' μ u - J' μ' u‖ ≤ lam' * θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hsol : ∀ μ ∈ V, ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
      (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ)) :
    let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 / (lam ^ 2))
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
          (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (fun u : H => lam⁻¹ • (u - J μ u)) γ
              (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂) := by
  dsimp
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ₀, hμ₀⟩
    have hγ : 0 < γ := (hsol μ₀ hμ₀).1
    let B : M → H → H := fun μ u => lam⁻¹ • (u - J μ u)
    have hC1 : ∀ μ ∈ V, 0 < lam ∧ ∀ u v : H,
        lam * ‖B μ u - B μ v‖ ^ 2 ≤ inner ℝ (B μ u - B μ v) (u - v) := by
      intro μ hμ
      refine ⟨hlam, ?_⟩
      intro u v
      have hu := (SetValuedOperator.mem_resolvent_smul_iff (A μ) lam u (J μ u)).mp
        (hJ μ hμ u)
      have hv := (SetValuedOperator.mem_resolvent_smul_iff (A μ) lam v (J μ v)).mp
        (hJ μ hμ v)
      rcases hu with ⟨a, ha, hua⟩
      rcases hv with ⟨b, hb, hvb⟩
      have hmono : 0 ≤ inner ℝ (a - b) (J μ u - J μ v) :=
        (hA μ hμ).1 a ha b hb
      have hua' : u - J μ u = lam • a := by
        calc
          u - J μ u = (J μ u + lam • a) - J μ u :=
            (congrArg (fun z => z - J μ u) hua).symm
          _ = lam • a := by module
      have hvb' : v - J μ v = lam • b := by
        calc
          v - J μ v = (J μ v + lam • b) - J μ v :=
            (congrArg (fun z => z - J μ v) hvb).symm
          _ = lam • b := by module
      have hBdiff : B μ u - B μ v = a - b := by
        dsimp [B]
        rw [hua', hvb']
        rw [smul_smul, smul_smul]
        simp [inv_mul_cancel₀ (ne_of_gt hlam)]
      have huv : u - v = (J μ u - J μ v) + lam • (a - b) := by
        calc
          u - v = (J μ u + lam • a) - (J μ v + lam • b) := by rw [hua, hvb]
          _ = (J μ u - J μ v) + lam • (a - b) := by module
      rw [hBdiff, huv, inner_add_right, inner_smul_right]
      have hnorm : ‖a - b‖ ^ 2 = inner ℝ (a - b) (a - b) := by simp
      rw [hnorm]
      nlinarith
    have hC2 : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V →
        ‖B μ u - B μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂ := by
      refine ⟨hθ₁, hθ₂_pos, hθ₂_le, ?_⟩
      intro u μ μ' hμ hμ'
      have h15lam := h15 lam hlam J hJ u μ hμ μ' hμ'
      have hdiff : B μ u - B μ' u = lam⁻¹ • (J μ' u - J μ u) := by
        dsimp [B]
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), norm_sub_rev]
      rw [show lam⁻¹ * ‖J μ u - J μ' u‖ = ‖J μ u - J μ' u‖ / lam by ring]
      exact (div_le_iff₀ hlam).mpr (by simpa [mul_assoc, mul_left_comm, mul_comm] using h15lam)
    rcases thm_1 V B γ u₀ v₀ (fun _ : M => lam) θ₁ θ₂ hγ hC1 hC2 with
      ⟨hunique, hcomparison⟩
    constructor
    · simpa [B] using hunique
    · intro μ hμ μ' hμ'
      rcases hcomparison μ hμ μ' hμ' with ⟨y, y', hysol, hy'sol, hybound⟩
      rcases hysol with ⟨dy, ddy, hysol⟩
      rcases hy'sol with ⟨dy', ddy', hy'sol⟩
      obtain ⟨z, dz, ddz, hzsol, hzuniq⟩ := hunique μ hμ
      have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
        (hzuniq (x μ) (dx μ) (ddx μ) (by simpa [B] using hsol μ hμ) ht).symm.trans
          (hzuniq y dy ddy (by simpa [B] using hysol) ht)
      obtain ⟨z', dz', ddz', hz'sol, hz'uniq⟩ := hunique μ' hμ'
      have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
        (hz'uniq (x μ') (dx μ') (ddx μ') (by simpa [B] using hsol μ' hμ') ht).symm.trans
          (hz'uniq y' dy' ddy' (by simpa [B] using hy'sol) ht)
      filter_upwards [hybound] with t ht
      intro ht_nonneg
      have ht_bound := ht ht_nonneg
      rw [← hxy ht_nonneg, ← hxy' ht_nonneg] at ht_bound
      simpa only [max_self] using ht_bound
  · constructor
    · intro μ hμ
      exact (hV ⟨μ, hμ⟩).elim
    · intro μ hμ
      exact (hV ⟨μ, hμ⟩).elim

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
