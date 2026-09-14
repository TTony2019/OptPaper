import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_3
import Foundation.Analysis.ExtendedRealFunctions

open ERealFunction

/-- Data for the classical (unaccelerated) proximal point algorithm. -/
structure ClassicalProximalPointAlgorithm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : H → ℝ) where
  x : ℕ → H
  lam : ℕ → ℝ
  f_proper : ERealFunction.IsProper (fun z => (f z : EReal))
  f_lowerSemicontinuous : LowerSemicontinuous f
  f_convex : ConvexOn ℝ Set.univ f
  lam_pos : ∀ k, 0 < lam k
  proximal_step : ∀ k, x (k + 1) ∈ proximalPoints f (lam k) (x k)

private theorem classical_proximal_step_gap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) {lam : ℝ} {y p z : H}
    (hconvex : ConvexOn ℝ Set.univ f) (hp : p ∈ proximalPoints f lam y) :
    2 * lam * (f p - f z) ≤ ‖y - z‖ ^ 2 - ‖p - z‖ ^ 2 := by
  rcases hp with ⟨hlam, hpmin⟩
  have hsub := proximal_optimality_condition f hlam hconvex hpmin
  rw [mem_convexSubdifferential_iff] at hsub
  have hsupport : f p + (1 / lam) * inner ℝ (y - p) (z - p) ≤ f z := by
    simpa [inner_smul_left, smul_eq_mul] using hsub z
  have hinner : lam * (f p - f z) ≤ inner ℝ (y - p) (p - z) := by
    have hneg : inner ℝ (y - p) (p - z) = -inner ℝ (y - p) (z - p) := by
      rw [show p - z = -(z - p) by abel, inner_neg_right]
    field_simp [ne_of_gt hlam] at hsupport ⊢
    rw [hneg]
    nlinarith [hsupport]
  have hidentity :
      2 * inner ℝ (y - p) (p - z) =
        ‖y - z‖ ^ 2 - ‖p - z‖ ^ 2 - ‖y - p‖ ^ 2 := by
    rw [show y - z = (y - p) - (z - p) by abel, norm_sub_sq_real]
    simp [inner_sub_left, inner_sub_right, norm_sub_rev]
    ring
  nlinarith [sq_nonneg ‖y - p‖]

/-- Remark 2.4 records the classical comparison rate for the unaccelerated proximal method. -/
theorem classical_proximal_comparison_rate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (f : H → ℝ)
    (alg : ClassicalProximalPointAlgorithm f) (xstar : H) (k : ℕ) (hk : 1 ≤ k)
    (hstar : ∀ z, f xstar ≤ f z) :
    f (alg.x k) - f xstar ≤ residualDistance (alg.x 0) {z | f z = f xstar} ^ 2 /
      (2 * ∑ j ∈ Finset.range k, alg.lam j) := by
  let Xstar : Set H := {z | f z = f xstar}
  have hobj_succ : ∀ i, f (alg.x (i + 1)) ≤ f (alg.x i) := by
    intro i
    rcases alg.proximal_step i with ⟨_, hmin⟩
    have hmin' : f (alg.x (i + 1)) +
        ‖alg.x (i + 1) - alg.x i‖ ^ 2 / (2 * alg.lam i) ≤ f (alg.x i) := by
      simpa using hmin (Set.mem_univ (alg.x i))
    have hnonneg : 0 ≤ ‖alg.x (i + 1) - alg.x i‖ ^ 2 / (2 * alg.lam i) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) (alg.lam_pos i)))
    linarith
  have hgap_anti : Antitone (fun i => f (alg.x i) - f xstar) := by
    apply antitone_nat_of_succ_le
    intro i
    linarith [hobj_succ i]
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
  have hterm : ∀ i ∈ Finset.range k,
      alg.lam i * (f (alg.x k) - f xstar) ≤
        (‖alg.x i - xopt‖ ^ 2 - ‖alg.x (i + 1) - xopt‖ ^ 2) / 2 := by
    intro i hi
    have hik : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hmono : alg.lam i * (f (alg.x k) - f xstar) ≤
        alg.lam i * (f (alg.x (i + 1)) - f xstar) :=
      mul_le_mul_of_nonneg_left (hgap_anti hik) (alg.lam_pos i).le
    have hstep := classical_proximal_step_gap f alg.f_convex (alg.proximal_step i)
      (z := xopt)
    rw [hxopt] at hstep
    nlinarith
  have hsum : ∑ i ∈ Finset.range k, alg.lam i * (f (alg.x k) - f xstar) ≤
      ∑ i ∈ Finset.range k,
        (‖alg.x i - xopt‖ ^ 2 - ‖alg.x (i + 1) - xopt‖ ^ 2) / 2 := by
    exact Finset.sum_le_sum fun i hi => hterm i hi
  have htel : ∑ i ∈ Finset.range k,
      (‖alg.x i - xopt‖ ^ 2 - ‖alg.x (i + 1) - xopt‖ ^ 2) / 2 =
        (‖alg.x 0 - xopt‖ ^ 2 - ‖alg.x k - xopt‖ ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_range_sub']
  have hweighted : (∑ i ∈ Finset.range k, alg.lam i) *
      (f (alg.x k) - f xstar) ≤ ‖alg.x 0 - xopt‖ ^ 2 / 2 := by
    calc
      (∑ i ∈ Finset.range k, alg.lam i) * (f (alg.x k) - f xstar) =
          ∑ i ∈ Finset.range k, alg.lam i * (f (alg.x k) - f xstar) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.range k,
          (‖alg.x i - xopt‖ ^ 2 - ‖alg.x (i + 1) - xopt‖ ^ 2) / 2 := hsum
      _ = (‖alg.x 0 - xopt‖ ^ 2 - ‖alg.x k - xopt‖ ^ 2) / 2 := htel
      _ ≤ ‖alg.x 0 - xopt‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg ‖alg.x k - xopt‖]
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, alg.lam i := by
    apply Finset.sum_pos'
    · intro i hi
      exact (alg.lam_pos i).le
    · refine ⟨0, Finset.mem_range.mpr ?_, alg.lam_pos 0⟩
      omega
  apply (le_div_iff₀ (mul_pos (by norm_num) hsum_pos)).2
  rw [← hdist, ← norm_sub_rev (alg.x 0) xopt]
  nlinarith [hweighted]
