import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.prop_3
import Mathlib
import Foundation.Convex.Subdifferential
import Foundation.Convex.StronglyConvex

namespace AbbasDynamical2015

open Filter MeasureTheory

/-- Corollary 2.17: strong convexity gives a singleton solution set and strong convergence. -/
theorem strong_convex_solution_unique_and_convergent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H)
    (S : Set H) (x v : ℝ → H) (lam : ℝ)
    (mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)))
    (hsolution : ∀ z, z ∈ S → -B z ∈ ERealFunction.subdifferential Phi z)
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hstrong_support : ∃ m : ℝ, 0 < m ∧ ∀ {a u y : H},
      u ∈ ERealFunction.subdifferential Phi a →
      y ∈ ERealFunction.effectiveDomain Phi →
      m / 2 * ‖y - a‖ ^ 2 ≤
        (Phi y : EReal).toReal - (Phi a : EReal).toReal - inner ℝ u (y - a)) :
    ∃ z, S = {z} ∧ Tendsto x atTop (nhds z) := by
  rcases hS with ⟨z, hz⟩
  rcases hstrong_support with ⟨m, hm, hsupp⟩
  have hS_singleton : S = {z} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩
    intro y hy
    have h1 := hsupp (a := z) (u := -B z) (y := y) (hsolution z hz) (hdom.2 y hy)
    have h2 := hsupp (a := y) (u := -B y) (y := z) (hsolution y hy) (hdom.2 z hz)
    have hineq := hB.ineq ⟨y, Set.mem_univ y⟩ ⟨z, Set.mem_univ z⟩
    have hinner : 0 ≤ inner ℝ (y - z) (B y - B z) := by
      exact le_trans (mul_nonneg hbeta.le (sq_nonneg _)) hineq
    have hdist : m * ‖y - z‖ ^ 2 ≤ 0 := by
      have hsum : m * ‖y - z‖ ^ 2 ≤ -inner ℝ (y - z) (B y - B z) := by
        have h1' : m / 2 * ‖y - z‖ ^ 2 ≤
            (Phi y : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (y - z) (B z) := by
          simpa [inner_neg_left, real_inner_comm] using h1
        have h2' : m / 2 * ‖y - z‖ ^ 2 ≤
            (Phi z : EReal).toReal - (Phi y : EReal).toReal -
              inner ℝ (y - z) (B y) := by
          have hi : inner ℝ (B y) (z - y) = -inner ℝ (y - z) (B y) := by
            rw [← neg_sub, inner_neg_right, real_inner_comm (B y) (y - z)]
          rw [inner_neg_left, hi, norm_sub_rev] at h2
          simpa using h2
        have hinner_eq : inner ℝ (y - z) (B y - B z) =
            inner ℝ (y - z) (B y) - inner ℝ (y - z) (B z) := by
          rw [inner_sub_right]
        nlinarith [h1', h2', hinner_eq]
      exact le_trans hsum (neg_nonpos.mpr hinner)
    have hzero : ‖y - z‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖y - z‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  have hp := proposition_2_16 S Phi hPhi B x v z lam mu beta ⟨z, hz⟩ hz hlam hmu
    hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2
    horbit hsolution hdom hweak
  have hF_lim := hp.2.1
  let gamma : ℝ := m / 2
  have hgamma : 0 < gamma := by dsimp [gamma]; linarith
  have hnorm_lim : Tendsto (fun t => ‖x t - z‖) atTop (nhds 0) := by
    have hsquare : Tendsto (fun t => ‖x t - z‖ ^ 2) atTop (nhds 0) := by
      refine squeeze_zero' (g := fun t => gamma⁻¹ *
          ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
            inner ℝ (B z) (x t - z)))
        (Eventually.of_forall (fun t => sq_nonneg _)) ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        have hgap := hsupp (a := z) (u := -B z) (y := x t) (hsolution z hz) (hdom.1 t ht)
        have hgap' : gamma * ‖x t - z‖ ^ 2 ≤
            (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z) := by
          simpa [gamma, inner_neg_left] using hgap
        have hnonneg : 0 ≤
            gamma⁻¹ * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z)) := by
          have : 0 ≤ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z) := by nlinarith [hgap']
          exact mul_nonneg (inv_nonneg.mpr hgamma.le) this
        have hsq : ‖x t - z‖ ^ 2 ≤ gamma⁻¹ *
            ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z)) := by
          calc
            ‖x t - z‖ ^ 2 = gamma⁻¹ * (gamma * ‖x t - z‖ ^ 2) := by
              rw [← mul_assoc, inv_mul_cancel₀ hgamma.ne', one_mul]
            _ ≤ gamma⁻¹ * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
                inner ℝ (B z) (x t - z)) :=
              mul_le_mul_of_nonneg_left hgap' (inv_nonneg.mpr hgamma.le)
        exact hsq
      · simpa using (hF_lim.const_mul gamma⁻¹)
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsquare
  have hsub_lim : Tendsto (fun t => x t - z) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_lim
  exact ⟨z, hS_singleton, tendsto_sub_nhds_zero_iff.mp hsub_lim⟩

end AbbasDynamical2015
