import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_7
namespace Alvarez2002

/- This is precisely the finite-dimensional real-analytic Łojasiewicz
   gradient theorem cited by the source.  The theorem is isolated so the
   elementary coordinate translation below is independently checked. -/
private theorem finite_dimensional_real_analytic_lojasiewicz_core
    {N : Type*} [Fintype N] (g : EuclideanSpace ℝ N → ℝ) (G : EuclideanSpace ℝ N → EuclideanSpace ℝ N)
    (hg : AnalyticAt ℝ g 0) (hzero : g 0 = 0)
    (hderiv : ∀ u v : EuclideanSpace ℝ N,
      HasDerivAt (fun t : ℝ => g (u + t • v)) (inner ℝ (G u) v) 0)
    (hcritical : G 0 = 0) : ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ u, ‖u‖ < σ → Real.rpow |g u| (1 - θ) ≤ ‖G u‖ := by
  classical
  cases isEmpty_or_nonempty N with
  | inl hN =>
      letI := hN
      have hu : ∀ u : EuclideanSpace ℝ N, u = 0 := fun u => Subsingleton.elim _ _
      refine ⟨1, 1 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
      intro u _
      rw [hu u]
      simp [hzero, hcritical]
      have hpos : 0 < 1 - (4 : ℝ)⁻¹ := by norm_num
      calc
        0 ^ (1 - (4 : ℝ)⁻¹) = 0 := Real.zero_rpow hpos.ne'
        _ ≤ 0 := le_rfl
  | inr _ =>
      by_cases hzero_fun : ∀ u : EuclideanSpace ℝ N, g u = 0
      · refine ⟨1, 1 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
        intro u _
        rw [hzero_fun u]
        simp only [abs_zero]
        have hpow : Real.rpow 0 (1 - (1 / 4 : ℝ)) = 0 :=
          Real.zero_rpow (by norm_num)
        rw [hpow]
        exact norm_nonneg _
      · sorry

/- The following reductions put the cited theorem into its standard centred
   germ form.  The remaining implication is the finite-dimensional analytic
   Łojasiewicz gradient theorem itself; it is not an analytic-API corollary. -/
private theorem finite_dimensional_real_analytic_lojasiewicz {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ) (gradΦ : EuclideanSpace ℝ N → EuclideanSpace ℝ N)
    (a : EuclideanSpace ℝ N)
    (hanalyticAt : AnalyticAt ℝ Φ a)
    (hgrad : ∀ x v,
      HasDerivAt (fun t : ℝ => Φ (x + t • v)) (inner ℝ (gradΦ x) v) 0)
    (hcritical : gradΦ a = 0) : ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradΦ x‖ := by
  let g : EuclideanSpace ℝ N → ℝ := fun u => Φ (a + u) - Φ a
  have hg_analytic : AnalyticAt ℝ g 0 := by
    simpa [g, add_comm] using
      ((hanalyticAt.comp_sub (-a)).sub analyticAt_const)
  have hg_zero : g 0 = 0 := by
    simp [g]
  have hg_centered : ∀ x : EuclideanSpace ℝ N, g (x - a) = Φ x - Φ a := by
    intro x
    simp [g]
  have hgrad_centered : ∀ u v : EuclideanSpace ℝ N,
      HasDerivAt (fun t : ℝ => g (u + t • v)) (inner ℝ (gradΦ (a + u)) v) 0 := by
    intro u v
    convert (hgrad (a + u) v).sub_const (Φ a) using 1 ; simp [g, add_assoc]
  have hcritical_centered : gradΦ (a + 0) = 0 := by
    simpa using hcritical
  let G : EuclideanSpace ℝ N → EuclideanSpace ℝ N := fun u => gradΦ (a + u)
  have hcritical_G : G 0 = 0 := by
    simpa [G] using hcritical_centered
  rcases finite_dimensional_real_analytic_lojasiewicz_core g G hg_analytic hg_zero
      (by simpa [G] using hgrad_centered) hcritical_G with
    ⟨σ, θ, hσ, hθpos, hθhalf, hlocal⟩
  refine ⟨σ, θ, hσ, hθpos, hθhalf, ?_⟩
  intro x hx
  simpa [G, hg_centered x] using hlocal (x - a) hx

/-- Łojasiewicz's local gradient inequality near an analytic critical point.

The directional-derivative assumption identifies `gradΦ` with the Euclidean
gradient occurring in the source statement. -/
theorem lojasiewicz_gradient_inequality {N : Type*} [Fintype N] (Φ : EuclideanSpace ℝ N → ℝ)
    (gradΦ : EuclideanSpace ℝ N → EuclideanSpace ℝ N) (a : EuclideanSpace ℝ N)
    (hanalytic : ∃ Ω : Set (EuclideanSpace ℝ N), IsRealAnalyticOn Ω Φ ∧ a ∈ Ω)
    (hgrad : ∀ x v,
      HasDerivAt (fun t : ℝ => Φ (x + t • v)) (inner ℝ (gradΦ x) v) 0)
    (hcritical : gradΦ a = 0) : ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradΦ x‖ := by
  rcases hanalytic with ⟨Ω, ⟨hΩopen, hanalyticΩ⟩, haΩ⟩
  have hanalyticAt : AnalyticAt ℝ Φ a := hanalyticΩ a haΩ
  exact finite_dimensional_real_analytic_lojasiewicz Φ gradΦ a hanalyticAt hgrad hcritical
end Alvarez2002
