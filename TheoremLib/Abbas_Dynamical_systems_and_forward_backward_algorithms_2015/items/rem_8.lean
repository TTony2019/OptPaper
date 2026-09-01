import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.ProximalOperator
import Foundation.Convex.Subdifferential
import Foundation.Hilbert.WeakTopology

namespace AbbasDynamical2015

/-- Remark 5.3: in the restrictive range the governing field is `I - T` for a contraction. -/
theorem restrictive_parameter_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B T : H → H) (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hS : S.Nonempty)
    (_hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (_hB_maximal_monotone : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hT : ∀ q, T q = ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
      (q - mu • B q))
    (hcontraction : LipschitzWith (1 / 2 : NNReal) T)
    (hclassical : ∀ t : ℝ, HasDerivAt x (T (x t) - x t) t)
    (_hdynamics : ∀ t, deriv x t = T (x t) - x t) :
    ∃ z ∈ S, Filter.Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  obtain ⟨z, hzS⟩ := hS
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := (hsolution z).mp hzS
  have hfix : T z = z := by
    rw [hT z]
    let gamma : ERealFunction.PosReal := ⟨mu, hmu.1⟩
    have hg : gamma • Phi ∈ ERealFunction.gammaZero H :=
      ERealFunction.smul_mem_gammaZero Phi hPhi gamma
    have hsub : (z - mu • B z) - z ∈ ERealFunction.subdifferential (gamma • Phi) z := by
      rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
      refine Set.mem_smul_set.2 ⟨-B z, hzsub, ?_⟩
      simp [gamma]
    change ERealFunction.proximityOperator (gamma • Phi) _ (z - mu • B z) = z
    exact (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential hg
      (z - mu • B z) z).mpr hsub |>.symm
  have henergy : ∀ t : ℝ,
      2 * inner ℝ (x t - z) (T (x t) - x t) ≤ -‖x t - z‖ ^ 2 := by
    intro t
    have hLip : ‖T (x t) - T z‖ ≤ (1 / 2 : ℝ) * ‖x t - z‖ := by
      simpa using hcontraction.norm_sub_le (x t) z
    have hinner : inner ℝ (x t - z) (T (x t) - T z) ≤
        (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by
      calc
        inner ℝ (x t - z) (T (x t) - T z) ≤
            ‖x t - z‖ * ‖T (x t) - T z‖ := real_inner_le_norm _ _
        _ ≤ ‖x t - z‖ * ((1 / 2 : ℝ) * ‖x t - z‖) :=
            mul_le_mul_of_nonneg_left hLip (norm_nonneg _)
        _ = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by ring
    rw [show T (x t) - x t = (T (x t) - T z) - (x t - z) by rw [hfix]; abel]
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    nlinarith
  let p : ℝ → ℝ := fun t ↦ Real.exp t * ‖x t - z‖ ^ 2
  have hp : ∀ t : ℝ, HasDerivAt p
      (Real.exp t * ‖x t - z‖ ^ 2 +
        Real.exp t * (2 * inner ℝ (x t - z) (T (x t) - x t))) t := by
    intro t
    simpa [p] using
      (Real.hasDerivAt_exp t).mul ((hclassical t).sub_const z).norm_sq
  have hp_nonpos : ∀ t : ℝ, deriv p t ≤ 0 := by
    intro t
    rw [(hp t).deriv]
    have hscaled := mul_le_mul_of_nonneg_left (henergy t) (Real.exp_pos t).le
    nlinarith
  have hp_diff : Differentiable ℝ p := fun t ↦ (hp t).differentiableAt
  have hp_anti : Antitone p := antitone_of_deriv_nonpos hp_diff hp_nonpos
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖x t - z‖ ^ 2 ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t ht
    have hle := hp_anti ht
    have hscaled := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-t)).le
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      ‖x t - z‖ ^ 2 = Real.exp (-t) * (Real.exp t * ‖x t - z‖ ^ 2) := by
        rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
        simpa [p] using hscaled
  let q : ℝ → ℝ := fun t ↦ if 0 ≤ t then ‖x t - z‖ ^ 2 else 0
  have hq_nonneg : ∀ t : ℝ, 0 ≤ q t := by
    intro t
    by_cases ht : 0 ≤ t <;> simp [q, ht]
  have hq_le : ∀ t : ℝ, q t ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa [q, ht] using hbound t ht
    · rw [show q t = 0 by simp [q, ht]]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hexp_zero : Filter.Tendsto
      (fun t : ℝ ↦ Real.exp (-t) * ‖x 0 - z‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_const_nhds
  have hq_zero : Filter.Tendsto q Filter.atTop (nhds 0) :=
    squeeze_zero hq_nonneg hq_le hexp_zero
  have hsq_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖ ^ 2) Filter.atTop (nhds 0) := by
    apply hq_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [q, ht]
  have hsqrt_zero :
      Filter.Tendsto (fun t : ℝ ↦ √(‖x t - z‖ ^ 2)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq_zero
  have hnorm_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖) Filter.atTop (nhds 0) := by
    convert hsqrt_zero using 1
    funext t
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hstrong : Filter.Tendsto x Filter.atTop (nhds z) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_zero
  exact ⟨z, hzS, by simpa using ((toWeakSpaceCLM ℝ H).continuous.tendsto z).comp hstrong⟩

end AbbasDynamical2015
