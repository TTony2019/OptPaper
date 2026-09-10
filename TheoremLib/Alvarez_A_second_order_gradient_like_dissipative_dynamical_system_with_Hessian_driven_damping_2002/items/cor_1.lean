import Mathlib
import Foundation.Convex.Coercive
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_1
namespace Alvarez2002
open Filter
set_option linter.unusedVariables false in
/-- Corollary 2.1: coercivity bounds every `C²` `(DIN)` trajectory on `[0, ∞)`,
hence yields Theorem 2.1(iii). The Hessian is `fderiv ℝ (gradient Φ)`. -/
theorem coercive_potential_bounds_din {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ)
    (x : ℝ → H) (hΦ : AssumptionH H Φ)
    (hΦreg : ContDiff ℝ 2 Φ)
    (hxreg : ContDiff ℝ 2 x)
    (hcoercive : ERealFunction.Coercive (fun z => (Φ z : EReal)))
    (hsol : IsDINTrajectory H Φ α β x) :
    (∃ R : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ R) ∧
      Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧ Tendsto (deriv (deriv x)) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
  have hα : 0 < α := hsol.1
  have hβ : 0 < β := hsol.2.1
  -- The middle Liapounov coefficient `αβ + 1` lies in the admissible range.
  let ell : ℝ := α * β + 1
  have hell_pos : 0 < ell := by
    dsimp [ell]
    nlinarith [mul_pos hα hβ]
  have hs2 : (Real.sqrt (α * β)) ^ 2 = α * β :=
    Real.sq_sqrt (mul_nonneg hα.le hβ.le)
  have hsnn : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
  have hell_low : (1 - Real.sqrt (α * β)) ^ 2 ≤ ell := by
    dsimp [ell]
    nlinarith [hs2, hsnn]
  have hell_high : ell ≤ (1 + Real.sqrt (α * β)) ^ 2 := by
    dsimp [ell]
    nlinarith [hs2, hsnn]
  -- The energy `E_t = (αβ+1)Φ(x t) + ½‖ẋ+β∇Φ‖²` is decreasing on `[0,∞)`.
  obtain ⟨_, hanti, _, _⟩ :=
    (din_global_properties_part_ii Φ hΦ α β hα hβ (x 0) (deriv x 0) x rfl rfl hsol hxreg).1
      ell hell_low hell_high
  -- Hence `Φ(x t) ≤ E(0)/(αβ+1)` for every `t ≥ 0`.
  have hΦbound : ∀ t : ℝ, 0 ≤ t → Φ (x t) ≤ dinForwardEnergy Φ β ell x 0 / ell := by
    intro t ht
    have hEt : dinForwardEnergy Φ β ell x t ≤ dinForwardEnergy Φ β ell x 0 :=
      hanti (by simp) (by simpa using ht) ht
    have hfac : ell * Φ (x t) ≤ dinForwardEnergy Φ β ell x t := by
      have hnonneg : (0 : ℝ) ≤ (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2 := by
        positivity
      simp only [dinForwardEnergy]
      linarith
    exact (le_div_iff₀' hell_pos).mpr (le_trans hfac hEt)
  -- Coercivity turns that upper bound into a bound on `‖x t‖`.
  have hcoer : ∀ c : ℝ, ∃ a : ℝ, ∀ z : H, a ≤ ‖z‖ → c < Φ z := by
    intro c
    have h : ∀ᶠ z in Bornology.cobounded H, (c : EReal) < (Φ z : EReal) :=
      (EReal.tendsto_nhds_top_iff_real.mp hcoercive) c
    rw [Filter.hasBasis_cobounded_norm.eventually_iff] at h
    obtain ⟨a, -, ha⟩ := h
    exact ⟨a, fun z hz => EReal.coe_lt_coe_iff.mp (ha hz)⟩
  obtain ⟨a, ha⟩ := hcoer (dinForwardEnergy Φ β ell x 0 / ell)
  have hle_a : ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ a := by
    intro t ht
    by_contra hcon
    have hlt : a < ‖x t‖ := not_le.mp hcon
    exact (not_lt.mpr (hΦbound t ht)) (ha (x t) hlt.le)
  have hxbound : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max a 0, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact le_trans (hle_a t ht) (le_max_left a 0)
  -- Now Theorem 2.1(iii) supplies all the remaining conclusions.
  obtain ⟨hvB, haccB, hgradB, hhessB, hvT, haccT, hgradT⟩ :=
    din_global_properties_part_iii Φ hΦ α β hα hβ (x 0) (deriv x 0) x rfl rfl hsol hxreg hxbound
  exact ⟨⟨max a 0, fun t ht => le_trans (hle_a t ht) (le_max_left a 0)⟩,
    hvB, haccB, hgradB, hhessB, hvT, haccT, hgradT⟩

end Alvarez2002
