import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4

open Filter Topology

private theorem sum_sqrt_pos_of_pos (lam : ℕ → ℝ) (hlam : ∀ j, 0 < lam j)
    {k : ℕ} (hk : 0 < k) : 0 < ∑ j ∈ Finset.range k, Real.sqrt (lam j) := by
  apply Finset.sum_pos'
  · intro i hi
    exact Real.sqrt_nonneg _
  · exact ⟨0, Finset.mem_range.2 hk, Real.sqrt_pos.2 (hlam 0)⟩

private theorem accelerated_denominator_reciprocal_le (A S : ℝ) (hA : 0 < A) (hS : 0 < S) :
    1 / (1 + (Real.sqrt A / 2) * S) ^ 2 ≤ 4 / (A * S ^ 2) := by
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hden : 0 < (1 + (Real.sqrt A / 2) * S) ^ 2 := sq_pos_of_pos (by positivity)
  have hright : 0 < A * S ^ 2 := mul_pos hA (sq_pos_of_pos hS)
  apply (div_le_div_iff₀ hden hright).2
  have hsquare : ((Real.sqrt A / 2) * S) ^ 2 ≤
      (1 + (Real.sqrt A / 2) * S) ^ 2 := by
    nlinarith
  have hident : ((Real.sqrt A / 2) * S) ^ 2 = A * S ^ 2 / 4 := by
    calc
      ((Real.sqrt A / 2) * S) ^ 2 = (Real.sqrt A) ^ 2 * S ^ 2 / 4 := by ring
      _ = A * S ^ 2 / 4 := by rw [Real.sq_sqrt hA.le]
  nlinarith [hsquare]

private theorem tendsto_accelerated_rate_bound_zero (A C : ℝ) (hA : 0 < A)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop) :
    Tendsto (fun k => (4 / (A * S k ^ 2)) * C) atTop (𝓝 0) := by
  have hSq : Tendsto (fun k => S k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hS
  have hlim : Tendsto (fun k => (4 * C / A) / S k ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hSq
  apply hlim.congr'
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with k hk
  field_simp [hA.ne', ne_of_gt hk]

/-- Theorem 2.3: the objective values converge under divergent square-root step sizes.

The proof uses finite-dimensional attainment of the distance to the closed
minimizer set; this is a stronger hypothesis than the paper's abstract Hilbert
space formulation, which can be stated directly with an infimum distance. -/
theorem proximal_point_converges_to_minimum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (f : H → ℝ) (alg : ProximalPointAlgorithm f) (xstar : H)
    (hstar : ∀ z, f xstar ≤ f z)
    (hdiv : Tendsto (fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) atTop atTop) :
    (∀ k, 0 < k → f (alg.x k) - f xstar ≤
      (4 / (alg.A * (∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) ^ 2)) *
        (f (alg.x 0) - f xstar + (alg.A / 2) * residualDistance (alg.x 0) {z | f z = f xstar} ^ 2)) ∧
    Tendsto (fun k => f (alg.x k)) atTop (𝓝 (f xstar)) := by
  let Xstar : Set H := {z | f z = f xstar}
  let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)
  have hgap_nonneg : ∀ k, 0 ≤ f (alg.x k) - f xstar := fun k =>
    sub_nonneg.mpr (hstar _)
  have hXeq : Xstar = f ⁻¹' Set.Iic (f xstar) := by
    ext z
    simp only [Xstar, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hz
      rw [hz]
    · intro hz
      exact le_antisymm hz (hstar z)
  have hXclosed : IsClosed Xstar := by
    rw [hXeq]
    exact alg.f_lowerSemicontinuous.isClosed_preimage _
  obtain ⟨xopt, hxopt, hmetric⟩ :=
    hXclosed.exists_infDist_eq_dist ⟨xstar, rfl⟩ (alg.x 0)
  have hdist : ‖xopt - alg.x 0‖ = residualDistance (alg.x 0) Xstar := by
    rw [residualDistance, hmetric, dist_eq_norm, norm_sub_rev]
  have hrate : ∀ k, 0 < k → f (alg.x k) - f xstar ≤
      (4 / (alg.A * S k ^ 2)) *
        (f (alg.x 0) - f xstar + (alg.A / 2) * residualDistance (alg.x 0) Xstar ^ 2) := by
    intro k hk
    have hSpos : 0 < S k := by
      exact sum_sqrt_pos_of_pos alg.lam alg.lam_pos hk
    have hC : 0 ≤ f (alg.x 0) - f xopt + (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2 := by
      have hxopt_star : f xopt = f xstar := by simpa [Xstar] using hxopt
      have hfx : 0 ≤ f (alg.x 0) - f xopt := by
        rw [hxopt_star]
        exact sub_nonneg.mpr (hstar (alg.x 0))
      have hquad : 0 ≤ (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2 := by
        exact mul_nonneg (div_nonneg (le_of_lt alg.A_pos) (by norm_num)) (sq_nonneg _)
      linarith
    have hglobal := proximal_point_global_rate f alg xopt k (by omega : 1 ≤ k) (by
      simp [IsFeasible]) hC
    rw [hxopt] at hglobal
    have hres : 0 ≤ ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) (alg.lam_pos _)))
    have hfirst : f (alg.x k) - f xstar ≤
        (f (alg.x 0) - f xstar + (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2) /
          (1 + (Real.sqrt alg.A / 2) * S k) ^ 2 := by
      exact (le_add_of_nonneg_right hres).trans (by simpa [S] using hglobal)
    have hNnonneg : 0 ≤ f (alg.x 0) - f xstar + (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2 := by
      apply add_nonneg
      · exact sub_nonneg.mpr (hstar _)
      · exact mul_nonneg (div_nonneg alg.A_pos.le (by norm_num)) (sq_nonneg _)
    have hrecip := accelerated_denominator_reciprocal_le alg.A (S k) alg.A_pos hSpos
    calc
      f (alg.x k) - f xstar ≤
          (f (alg.x 0) - f xstar + (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2) /
            (1 + (Real.sqrt alg.A / 2) * S k) ^ 2 := hfirst
      _ ≤ (4 / (alg.A * S k ^ 2)) *
          (f (alg.x 0) - f xstar + (alg.A / 2) * ‖xopt - alg.x 0‖ ^ 2) := by
            rw [div_eq_mul_one_div]
            nlinarith [mul_le_mul_of_nonneg_right hrecip hNnonneg]
      _ = (4 / (alg.A * S k ^ 2)) *
          (f (alg.x 0) - f xstar + (alg.A / 2) * residualDistance (alg.x 0) Xstar ^ 2) := by
            rw [hdist]
  constructor
  · intro k hk
    simpa [S, Xstar] using hrate k hk
  · have hboundlim : Tendsto (fun k => (4 / (alg.A * S k ^ 2)) *
        (f (alg.x 0) - f xstar + (alg.A / 2) * residualDistance (alg.x 0) Xstar ^ 2))
        atTop (𝓝 0) :=
      tendsto_accelerated_rate_bound_zero alg.A
        (f (alg.x 0) - f xstar + (alg.A / 2) * residualDistance (alg.x 0) Xstar ^ 2)
        alg.A_pos S (by simpa [S] using hdiv)
    have hgaplim : Tendsto (fun k => f (alg.x k) - f xstar) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboundlim
      · exact Eventually.of_forall hgap_nonneg
      · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
        exact hrate k hk
    have hadd : Tendsto (fun k : ℕ => f xstar + (f (alg.x k) - f xstar)) atTop
        (𝓝 (f xstar + 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f xstar) atTop (𝓝 (f xstar))).add hgaplim
    simpa only [add_zero] using hadd.congr' (Eventually.of_forall fun k => by ring)
