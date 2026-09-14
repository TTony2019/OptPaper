import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_thm_1

open Filter Topology

open ERealFunction

private theorem accelerated_denominator_reciprocal_le_local (A S : ℝ) (hA : 0 < A) (hS : 0 < S) :
    1 / (1 + (Real.sqrt A / 2) * S) ^ 2 ≤ 4 / (A * S ^ 2) := by
  have hq : 0 < (Real.sqrt A / 2) * S := by positivity
  have hden : 0 < (1 + (Real.sqrt A / 2) * S) ^ 2 := sq_pos_of_pos (by linarith)
  have hright : 0 < A * S ^ 2 := mul_pos hA (sq_pos_of_pos hS)
  apply (div_le_div_iff₀ hden hright).2
  have hsquare : ((Real.sqrt A / 2) * S) ^ 2 ≤
      (1 + (Real.sqrt A / 2) * S) ^ 2 := by nlinarith
  have hident : ((Real.sqrt A / 2) * S) ^ 2 = A * S ^ 2 / 4 := by
    calc
      ((Real.sqrt A / 2) * S) ^ 2 = (Real.sqrt A) ^ 2 * S ^ 2 / 4 := by ring
      _ = A * S ^ 2 / 4 := by rw [Real.sq_sqrt hA.le]
  nlinarith [hsquare]

private theorem tendsto_accelerated_rate_bound_zero_local (A C : ℝ) (hA : 0 < A)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop) :
    Tendsto (fun k => (4 / (A * S k ^ 2)) * C) atTop (𝓝 0) := by
  have hSq : Tendsto (fun k => S k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hS
  have hlim : Tendsto (fun k => (4 * C / A) / S k ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hSq
  apply hlim.congr'
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with k hk
  field_simp [hA.ne', ne_of_gt hk]

/-- Corollary 2.3: residual conclusions of the convergent proximal iteration. -/
theorem proximal_residuals_vanish {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (f : H → ℝ) (alg : ProximalPointAlgorithm f) (xstar : H)
    (hstar : ∀ z, f xstar ≤ f z)
    (hdiv : Tendsto (fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) atTop atTop) :
    Tendsto (fun k => ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k) atTop (𝓝 0) ∧
      ((∃ M, ∀ k, alg.lam k ≤ M) →
        Tendsto (fun k => ‖alg.x (k + 1) - alg.y k‖) atTop (𝓝 0)) ∧
      Tendsto (fun k => alg.lam k * subdifferentialResidual f (alg.x (k + 1)) ^ 2) atTop (𝓝 0) ∧
      ((∃ m, 0 < m ∧ ∀ k, m ≤ alg.lam k) →
        Tendsto (fun k => subdifferentialResidual f (alg.x k)) atTop (𝓝 0)) := by
  let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)
  let C : ℝ := f (alg.x 0) - f xstar + (alg.A / 2) * ‖xstar - alg.x 0‖ ^ 2
  have hgap_nonneg : ∀ n, 0 ≤ f (alg.x n) - f xstar := fun n =>
    sub_nonneg.mpr (hstar _)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (hgap_nonneg 0)
      (mul_nonneg (div_nonneg alg.A_pos.le (by norm_num)) (sq_nonneg _))
  have hSsucc : Tendsto (fun k => S (k + 1)) atTop atTop := by
    simpa [S] using hdiv.comp (tendsto_add_atTop_nat 1)
  have hrate : Tendsto (fun k => (4 / (alg.A * S (k + 1) ^ 2)) * C) atTop (𝓝 0) :=
    tendsto_accelerated_rate_bound_zero_local alg.A C alg.A_pos _ hSsucc
  have hq : Tendsto (fun k => ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k) atTop (𝓝 0) := by
    have htworate : Tendsto (fun k => 2 * ((4 / (alg.A * S (k + 1) ^ 2)) * C))
        atTop (𝓝 0) := by simpa using (tendsto_const_nhds.mul hrate : _)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htworate
    · exact Eventually.of_forall fun k => div_nonneg (sq_nonneg _) (le_of_lt (alg.lam_pos k))
    · filter_upwards [hSsucc.eventually (eventually_gt_atTop 0)] with k hk
      have hglobal := proximal_point_global_rate f alg xstar (k + 1) (by omega) (by simp [IsFeasible])
        (by simpa [C] using hCnonneg)
      have hdisp : 0 ≤ ‖alg.y k - alg.x (k + 1)‖ ^ 2 / (2 * alg.lam k) :=
        div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) (alg.lam_pos k)))
      have hfirst : f (alg.x (k + 1)) - f xstar +
          ‖alg.y k - alg.x (k + 1)‖ ^ 2 / (2 * alg.lam k) ≤
          C / (1 + (Real.sqrt alg.A / 2) * S (k + 1)) ^ 2 := by
        simpa [S, C] using hglobal
      have hqle : ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k ≤
          2 * (C / (1 + (Real.sqrt alg.A / 2) * S (k + 1)) ^ 2) := by
        have heq : ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k =
            2 * (‖alg.y k - alg.x (k + 1)‖ ^ 2 / (2 * alg.lam k)) := by
          rw [norm_sub_rev]
          field_simp [ne_of_gt (alg.lam_pos k)]
        rw [heq]
        nlinarith [hgap_nonneg (k + 1)]
      have hrecip := accelerated_denominator_reciprocal_le_local alg.A (S (k + 1)) alg.A_pos hk
      have hbound : C / (1 + (Real.sqrt alg.A / 2) * S (k + 1)) ^ 2 ≤
          (4 / (alg.A * S (k + 1) ^ 2)) * C := by
        rw [div_eq_mul_one_div]
        nlinarith [mul_le_mul_of_nonneg_right hrecip hCnonneg]
      exact hqle.trans (by nlinarith)
  have hr : Tendsto (fun k => alg.lam k * subdifferentialResidual f (alg.x (k + 1)) ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq
    · exact Eventually.of_forall fun k => mul_nonneg (le_of_lt (alg.lam_pos k)) (sq_nonneg _)
    · filter_upwards [] with k
      rcases alg.x_step k with ⟨hlam, hmin⟩
      have hw := proximal_optimality_condition f hlam alg.f_convex hmin
      have hres : subdifferentialResidual f (alg.x (k + 1)) ≤
          ‖(1 / alg.lam k) • (alg.y k - alg.x (k + 1))‖ := by
        rw [subdifferentialResidual, residualDistance]
        simpa [dist_zero_right] using Metric.infDist_le_dist_of_mem (x := (0 : H)) hw
      have hresnonneg : 0 ≤ subdifferentialResidual f (alg.x (k + 1)) := by
        change 0 ≤ Metric.infDist (0 : H) (subdifferential (fun y => (f y : EReal)) (alg.x (k + 1)))
        exact Metric.infDist_nonneg
      have hnorm : ‖(1 / alg.lam k) • (alg.y k - alg.x (k + 1))‖ =
          ‖alg.y k - alg.x (k + 1)‖ / alg.lam k := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlam)]
        ring
      rw [hnorm] at hres
      have hsq : subdifferentialResidual f (alg.x (k + 1)) ^ 2 ≤
          (‖alg.y k - alg.x (k + 1)‖ / alg.lam k) ^ 2 := by nlinarith
      calc
        alg.lam k * subdifferentialResidual f (alg.x (k + 1)) ^ 2 ≤
            alg.lam k * (‖alg.y k - alg.x (k + 1)‖ / alg.lam k) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hlam.le
        _ = ‖alg.y k - alg.x (k + 1)‖ ^ 2 / alg.lam k := by
          field_simp [ne_of_gt hlam]
        _ = ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k := by rw [norm_sub_rev]
  refine ⟨hq, ?_, hr, ?_⟩
  · rintro ⟨M, hM⟩
    have hMsq : Tendsto (fun k => ‖alg.x (k + 1) - alg.y k‖ ^ 2) atTop (𝓝 0) := by
      have hMq : Tendsto (fun k => M * (‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k))
          atTop (𝓝 0) := by simpa using (tendsto_const_nhds.mul hq : _)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hMq
      · exact Eventually.of_forall fun _ => sq_nonneg _
      · filter_upwards [] with k
        have hnonneg : 0 ≤ ‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k :=
          div_nonneg (sq_nonneg _) (le_of_lt (alg.lam_pos k))
        have hmul := mul_le_mul_of_nonneg_left (hM k) hnonneg
        calc
          ‖alg.x (k + 1) - alg.y k‖ ^ 2 =
              (‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k) * alg.lam k := by
                field_simp [ne_of_gt (alg.lam_pos k)]
          _ ≤ (‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k) * M := hmul
          _ = M * (‖alg.x (k + 1) - alg.y k‖ ^ 2 / alg.lam k) := by ring
    have hsqrt := hMsq.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
  · rintro ⟨m, hmpos, hm⟩
    have hrsq : Tendsto (fun k => subdifferentialResidual f (alg.x (k + 1)) ^ 2) atTop (𝓝 0) := by
      have hscaled : Tendsto (fun k => (1 / m) *
          (alg.lam k * subdifferentialResidual f (alg.x (k + 1)) ^ 2)) atTop (𝓝 0) :=
        by simpa using (tendsto_const_nhds.mul hr : _)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled
      · exact Eventually.of_forall fun _ => sq_nonneg _
      · filter_upwards [] with k
        have hmul := mul_le_mul_of_nonneg_right (hm k) (sq_nonneg (subdifferentialResidual f (alg.x (k + 1))))
        calc
          subdifferentialResidual f (alg.x (k + 1)) ^ 2 =
              (1 / m) * (m * subdifferentialResidual f (alg.x (k + 1)) ^ 2) := by
                field_simp [ne_of_gt hmpos]
          _ ≤ (1 / m) * (alg.lam k * subdifferentialResidual f (alg.x (k + 1)) ^ 2) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
    have hshift : Tendsto (fun k => subdifferentialResidual f (alg.x (k + 1))) atTop (𝓝 0) := by
      have hsqrt := hrsq.sqrt
      have habs : Tendsto (fun k => |subdifferentialResidual f (alg.x (k + 1))|) atTop (𝓝 0) := by
        simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
      apply habs.congr'
      filter_upwards [] with k
      rw [abs_of_nonneg]
      change 0 ≤ Metric.infDist (0 : H) (subdifferential (fun y => (f y : EReal)) (alg.x (k + 1)))
      exact Metric.infDist_nonneg
    exact (tendsto_add_atTop_iff_nat 1).mp hshift
