import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_3
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_lem_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_lem_2
import Foundation.Convex.WeakClosed

namespace Alvarez2000

set_option maxHeartbeats 1000000

open Filter
open scoped InnerProductSpace Topology

private theorem alvarez_residual_decomposition {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a : ℝ) (x0 x1 x2 : H) :
    x2 - (1 + a) • x1 + a • x0 =
      a • (x2 - 2 • x1 + x0) + (1 - a) • (x2 - x1) := by
  module

private theorem alvarez_phi_increment_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a b z : H) :
    (1 / 2 : ℝ) * ‖a - z‖ ^ 2 =
      (1 / 2 : ℝ) * ‖b - z‖ ^ 2 + ⟪a - b, a - z⟫_ℝ -
        (1 / 2 : ℝ) * ‖a - b‖ ^ 2 := by
  have h := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
    (a - b) (a - z)
  have hsub : (a - b) - (a - z) = z - b := by abel
  rw [hsub, show z - b = -(b - z) by abel, norm_neg] at h
  nlinarith [h]

/-- The purely Hilbert-space part of Alvarez' distance recurrence.  Keeping the
subgradient-to-inner-product conversion separate makes this useful independently
of the extended-real representation of the objective. -/
private theorem alvarez_phi_recurrence_of_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H) (alpha lam eps : ℕ → ℝ) (z : H)
    (hAlpha : ∀ k, 0 ≤ alpha k)
    (hinner : ∀ k, 1 ≤ k →
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
        u (k + 1) - z⟫_ℝ ≤ lam k * eps k) :
    ∀ k, 1 ≤ k →
      (1 / 2 : ℝ) * ‖u (k + 1) - z‖ ^ 2 -
          (1 + alpha k) * ((1 / 2 : ℝ) * ‖u k - z‖ ^ 2) +
          alpha k * ((1 / 2 : ℝ) * ‖u (k - 1) - z‖ ^ 2) ≤
        alpha k * ‖u k - u (k - 1)‖ ^ 2 +
          (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2 + lam k * eps k := by
  intro k hk
  have hres :
      u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1) =
        (u (k + 1) - u k) - alpha k • (u k - u (k - 1)) := by
    module
  have hcross :
      alpha k * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ ≤
        (alpha k / 2) * ‖u k - u (k - 1)‖ ^ 2 +
          (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2 := by
    have hsquare : 0 ≤ ‖(u k - u (k - 1)) - (u (k + 1) - u k)‖ ^ 2 :=
      sq_nonneg _
    rw [norm_sub_pow_two_real] at hsquare
    have hbase : 2 * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ ≤
        ‖u k - u (k - 1)‖ ^ 2 + ‖u (k + 1) - u k‖ ^ 2 := by
      linarith
    nlinarith [hAlpha k]
  have hstep := hinner k hk
  rw [hres, inner_sub_left, real_inner_smul_left] at hstep
  have hphi1 := alvarez_phi_increment_identity (u (k + 1)) (u k) z
  have hphi0 := alvarez_phi_increment_identity (u k) (u (k - 1)) z
  have hsplit :
      ⟪u k - u (k - 1), u (k + 1) - z⟫_ℝ =
        ⟪u k - u (k - 1), u k - z⟫_ℝ +
          ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ := by
    rw [show u (k + 1) - z = (u k - z) + (u (k + 1) - u k) by abel,
      inner_add_right]
  rw [hsplit] at hstep
  have hphi0_scaled := congrArg (fun t : ℝ => alpha k * t) hphi0
  ring_nf at hphi0_scaled
  have hrec :
      (1 / 2 : ℝ) * ‖u (k + 1) - z‖ ^ 2 -
          (1 + alpha k) * ((1 / 2 : ℝ) * ‖u k - z‖ ^ 2) +
          alpha k * ((1 / 2 : ℝ) * ‖u (k - 1) - z‖ ^ 2) ≤
        alpha k * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ -
          (1 / 2 : ℝ) * ‖u (k + 1) - u k‖ ^ 2 +
          (alpha k / 2) * ‖u k - u (k - 1)‖ ^ 2 + lam k * eps k := by
    nlinarith [hstep, hphi1, hphi0_scaled]
  nlinarith [hrec, hcross, hAlpha k, sq_nonneg (‖u k - u (k - 1)‖),
    sq_nonneg (‖u (k + 1) - u k‖)]

/-- A distance recurrence with summable errors has a limit.  This packages the
scalar Alvarez lemma in the squared-distance form used by the inertial method. -/
theorem alvarez_norm_converges_of_recurrence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H) (z : H) (alpha delta : ℕ → ℝ)
    (alphaBar : ℝ) (hAlpha : ∀ k, 0 ≤ alpha k)
    (hAlphaBar : ∀ k, alpha k ≤ alphaBar) (hAlphaBarLt : alphaBar < 1)
    (hDelta : ∀ k, 0 ≤ delta k) (hDeltaSum : Summable delta)
    (hRec : ∀ k, 1 ≤ k →
      (1 / 2 : ℝ) * ‖u (k + 1) - z‖ ^ 2 -
          (1 + alpha k) * ((1 / 2 : ℝ) * ‖u k - z‖ ^ 2) +
          alpha k * ((1 / 2 : ℝ) * ‖u (k - 1) - z‖ ^ 2) ≤ delta k) :
    ∃ l : ℝ, Tendsto (fun k => ‖u k - z‖) atTop (nhds l) := by
  let psi : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖u k - z‖ ^ 2
  have hnonneg : ∀ n, 0 ≤ psi n ∧ 0 ≤ delta n ∧ 0 ≤ alpha n := by
    intro n
    exact ⟨mul_nonneg (by norm_num) (sq_nonneg _), hDelta n, hAlpha n⟩
  have hrec' : ∀ n ≥ 1, psi (n + 1) ≤ psi n + alpha n * (psi n - psi (n - 1)) + delta n := by
    intro n hn
    have h := hRec n hn
    dsimp [psi] at h ⊢
    linarith
  have hpsi_nonneg : ∀ n, 0 ≤ psi n := fun n => (hnonneg n).1
  have hdelta_nonneg : ∀ n, 0 ≤ delta n := fun n => (hnonneg n).2.1
  have halpha_nonneg : ∀ n, 0 ≤ alpha n := fun n => (hnonneg n).2.2
  rcases Alvarez2000.alvarez_sequence_convergence psi delta alpha
    hpsi_nonneg hdelta_nonneg halpha_nonneg hrec' hDeltaSum alphaBar
    (fun n _ => hAlphaBar n) hAlphaBarLt with ⟨_, ⟨l, hl_nonneg, hl⟩⟩
  refine ⟨Real.sqrt (2 * l), ?_⟩
  have hscaled : Tendsto (fun n => 2 * psi n) atTop (nhds (2 * l)) := by
    simpa using (tendsto_const_nhds.mul hl :
      Tendsto (fun n => 2 * psi n) atTop (nhds (2 * l)))
  have hsqrt := (Real.continuous_sqrt.tendsto (2 * l)).comp hscaled
  have hpsi : ∀ n, 2 * psi n = ‖u n - z‖ ^ 2 := by
    intro n
    dsimp [psi]
    ring
  have hroot : (fun n => √(2 * psi n)) = fun n => ‖u n - z‖ := by
    funext n
    rw [hpsi n, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  change Tendsto (fun n => √(2 * psi n)) atTop (nhds (√(2 * l))) at hsqrt
  rw [hroot] at hsqrt
  simpa using hsqrt

/-- The real-valued discrete energy inequality underlying Theorem 3.1. -/
private theorem alvarez_energy_step {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u : ℕ → H) (f : H → EReal)
    (eps lam alpha : ℕ → ℝ)
    (hAlpha : ∀ k, 0 ≤ alpha k ∧ alpha k ≤ 1)
    (hLamPos : ∀ k, 0 < lam k)
    (hRatio : Antitone (fun k => alpha k / lam k))
    (hDescent : ∀ k, 1 < k →
      (f (u (k + 1))).toReal - (f (u k)).toReal ≤
        -(lam k)⁻¹ * ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - u k⟫_ℝ + eps k) :
    ∀ k, 1 < k →
      alpha k / (2 * lam k) * ‖u (k + 1) - u k‖ ^ 2 + (f (u (k + 1))).toReal ≤
        alpha (k - 1) / (2 * lam (k - 1)) * ‖u k - u (k - 1)‖ ^ 2 +
          (f (u k)).toReal -
            (alpha k / (2 * lam k) * ‖u (k + 1) - 2 • u k + u (k - 1)‖ ^ 2 +
              (1 - alpha k) / lam k * ‖u (k + 1) - u k‖ ^ 2) + eps k := by
  intro k hk
  have hlam : lam k ≠ 0 := ne_of_gt (hLamPos k)
  have hratio : alpha k / lam k ≤ alpha (k - 1) / lam (k - 1) :=
    hRatio (Nat.sub_le k 1)
  have hkin : alpha k / (2 * lam k) * ‖u k - u (k - 1)‖ ^ 2 ≤
      alpha (k - 1) / (2 * lam (k - 1)) * ‖u k - u (k - 1)‖ ^ 2 := by
    have hsq : 0 ≤ ‖u k - u (k - 1)‖ ^ 2 := sq_nonneg _
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc
      alpha k / (2 * lam k) * ‖u k - u (k - 1)‖ ^ 2 =
          (alpha k / lam k) * ((1 / 2 : ℝ) * ‖u k - u (k - 1)‖ ^ 2) := by
            field_simp [hlam]
      _ ≤ (alpha (k - 1) / lam (k - 1)) *
          ((1 / 2 : ℝ) * ‖u k - u (k - 1)‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_right hratio (mul_nonneg hhalf hsq)
      _ = alpha (k - 1) / (2 * lam (k - 1)) * ‖u k - u (k - 1)‖ ^ 2 := by
            have hprev : lam (k - 1) ≠ 0 := ne_of_gt (hLamPos (k - 1))
            field_simp [hprev]
  have hres :
      u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1) =
        (u (k + 1) - u k) - alpha k • (u k - u (k - 1)) := by
    module
  have hinner :
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
        u (k + 1) - u k⟫_ℝ =
        ‖u (k + 1) - u k‖ ^ 2 -
          alpha k * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ := by
    rw [hres, inner_sub_left, real_inner_smul_left]
    simp [real_inner_self_eq_norm_sq]
  have hq :
      ‖u (k + 1) - 2 • u k + u (k - 1)‖ ^ 2 =
        ‖u (k + 1) - u k‖ ^ 2 + ‖u k - u (k - 1)‖ ^ 2 -
          2 * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ := by
    have hrewrite : u (k + 1) - 2 • u k + u (k - 1) =
        (u (k + 1) - u k) - (u k - u (k - 1)) := by module
    rw [hrewrite, norm_sub_pow_two_real]
    rw [real_inner_comm]
    ring
  have hdes := hDescent k hk
  rw [hinner] at hdes
  have halgebra :
      -(lam k)⁻¹ *
          (‖u (k + 1) - u k‖ ^ 2 -
            alpha k * ⟪u k - u (k - 1), u (k + 1) - u k⟫_ℝ) + eps k +
          alpha k / (2 * lam k) *
            (‖u (k + 1) - u k‖ ^ 2 - ‖u k - u (k - 1)‖ ^ 2) =
        -(alpha k / (2 * lam k) * ‖u (k + 1) - 2 • u k + u (k - 1)‖ ^ 2 +
          (1 - alpha k) / lam k * ‖u (k + 1) - u k‖ ^ 2) + eps k := by
    rw [hq]
    field_simp [hlam]
    ring
  linarith

/-- A nonnegative dissipation controlled by a lower-bounded energy and summable
errors is summable.  This is the finite-energy telescope used below. -/
private theorem alvarez_telescope_summable (E W R : ℕ → ℝ) (m : ℝ)
    (hE : ∀ n, m ≤ E n) (hW : ∀ n, 0 ≤ W n) (hR : ∀ n, 0 ≤ R n)
    (hRsum : Summable R)
    (hstep : ∀ n, E (n + 1) + W n ≤ E n + R n) :
    Summable W := by
  have htel : ∀ n : ℕ,
      E n + ∑ i ∈ Finset.range n, W i ≤ E 0 + ∑ i ∈ Finset.range n, R i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hs := hstep n
        linarith
  refine summable_of_sum_range_le (c := E 0 - m + ∑' i, R i) hW ?_
  intro n
  have h := htel n
  have hsum : (∑ i ∈ Finset.range n, R i) ≤ ∑' i, R i :=
    hRsum.sum_le_tsum (Finset.range n) (by
      intro i hi
      exact hR i)
  linarith [hE n]

/-- A convenient square-root squeeze used for the two dissipative terms. -/
private theorem alvarez_tendsto_zero_of_sq_le {H : Type*} [NormedAddCommGroup H]
    (v : ℕ → H) (q : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hq : Tendsto q atTop (nhds 0))
    (hbound : ∀ n, ‖v n‖ ^ 2 ≤ C * q n) :
    Tendsto v atTop (nhds 0) := by
  have hsq : Tendsto (fun n => ‖v n‖ ^ 2) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => C * q n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hq :
        Tendsto (fun n => C * q n) atTop (nhds (C * 0)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => sq_nonneg _) hbound
  have hnorm : Tendsto (fun n => ‖v n‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    change Tendsto (fun n => √(‖v n‖ ^ 2)) atTop (nhds (√0)) at hsqrt
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

private theorem alvarez_tendsto_of_nat_add {X : Type*} [PseudoMetricSpace X]
    (v : ℕ → X) (r : ℕ) (x : X)
    (h : Tendsto (fun n => v (n + r)) atTop (nhds x)) :
    Tendsto v atTop (nhds x) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro e he
  rcases h e he with ⟨N, hN⟩
  refine ⟨N + r, fun n hn => ?_⟩
  simpa [Nat.sub_add_cancel (le_trans (Nat.le_add_left r N) hn)] using
    hN (n - r) (Nat.le_sub_of_add_le hn)

/-- A strongly null vector sequence has vanishing inner products against any
norm-bounded sequence. -/
private theorem alvarez_inner_tendsto_zero_of_bounded {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v x : ℕ → H)
    (hv : Tendsto v atTop (nhds 0))
    (hx : Bornology.IsBounded (Set.range x)) :
    Tendsto (fun n => ⟪v n, x n⟫_ℝ) atTop (nhds 0) := by
  rcases isBounded_iff_forall_norm_le.mp hx with ⟨C, hC⟩
  have hCnonneg : 0 ≤ C := by
    have := hC (x 0) (Set.mem_range_self 0)
    exact le_trans (norm_nonneg _) this
  have hvnorm : Tendsto (fun n => ‖v n‖) atTop (nhds 0) := by
    simpa using hv.norm
  have hupper : Tendsto (fun n => C * ‖v n‖) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hvnorm :
      Tendsto (fun n => C * ‖v n‖) atTop (nhds (C * 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using hupper.neg) hupper
  · intro n
    have hbound : |⟪v n, x n⟫_ℝ| ≤ C * ‖v n‖ := by
      calc
        |⟪v n, x n⟫_ℝ| ≤ ‖v n‖ * ‖x n‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖v n‖ * C := mul_le_mul_of_nonneg_left
          (hC (x n) (Set.mem_range_self n)) (norm_nonneg _)
        _ = C * ‖v n‖ := by ring
    exact neg_le_of_abs_le hbound
  · intro n
    calc
      ⟪v n, x n⟫_ℝ ≤ |⟪v n, x n⟫_ℝ| := le_abs_self _
      _ ≤ C * ‖v n‖ := by
        calc
          |⟪v n, x n⟫_ℝ| ≤ ‖v n‖ * ‖x n‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖v n‖ * C := mul_le_mul_of_nonneg_left
            (hC (x n) (Set.mem_range_self n)) (norm_nonneg _)
          _ = C * ‖v n‖ := by ring

/- The lower level sets used in the Opial step are weakly closed because they
are norm-closed and convex.  Keeping this elementary fact separate prevents
the cluster-point argument from relying on a (false) unshifted generic helper.
-/
private theorem alvarez_lower_level_convex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {f : H → EReal}
    (hConvex : Convex ℝ (ERealFunction.epigraph f)) (r : ℝ) :
    Convex ℝ (ERealFunction.lowerLevelSet f r) := by
  intro x hx y hy a b ha hb hab
  rw [ERealFunction.mem_lowerLevelSet_iff] at hx hy ⊢
  have hxEpi : (x, r) ∈ ERealFunction.epigraph f := by
    simpa [ERealFunction.mem_epigraph_iff] using hx
  have hyEpi : (y, r) ∈ ERealFunction.epigraph f := by
    simpa [ERealFunction.mem_epigraph_iff] using hy
  have hmem := hConvex hxEpi hyEpi ha hb hab
  rw [ERealFunction.mem_epigraph_iff] at hmem
  have hcoordReal : a * r + b * r = r := by
    calc
      a * r + b * r = (a + b) * r := by ring
      _ = 1 * r := by rw [hab]
      _ = r := one_mul _
  have hcoord : ((a * r + b * r : ℝ) : EReal) = (r : EReal) := by
    exact_mod_cast hcoordReal
  simpa [Prod.smul_mk, smul_eq_mul, hcoordReal, hcoord] using hmem

/-- Theorem 3.1: residuals of the inertial proximal method vanish; under the additional
uniform-inertia assumptions, the iterates converge weakly to a minimizer. -/
theorem inertial_proximal_method_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → EReal}
    (u : ℕ → H) (eps lam alpha : ℕ → ℝ)
    (hProper : ERealFunction.IsProper f)
    (hClosed : IsClosed (ERealFunction.epigraph f))
    (hConvex : Convex ℝ (ERealFunction.epigraph f))
    (hBoundedBelow : ∃ m : ℝ, ∀ x : H, (m : EReal) ≤ f x)
    (hEps : ∀ k, 0 ≤ eps k) (hAlpha : ∀ k, 0 ≤ alpha k ∧ alpha k ≤ 1)
    (hLamLower : ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ lam k)
    (hRatioAntitone : Antitone (fun k => alpha k / lam k))
    (hErrors : Summable (fun k => lam k * eps k))
    (hUpdate : ∀ k : ℕ, 0 < k → 0 ∈ (fun p =>
      (lam k)⁻¹ • (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)) + p) ''
      epsilonSubdifferential f (eps k) (u (k + 1))) :
    Tendsto (fun k => (lam k)⁻¹ •
      (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) ∧
    Tendsto (fun k => Metric.infDist 0
      (epsilonSubdifferential f (eps k) (u (k + 1)))) atTop (nhds 0) ∧
    ((argmin f (by
      rcases hBoundedBelow with ⟨m, hm⟩
      exact ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩)).Nonempty →
      (∃ alphaBar : ℝ, 0 < alphaBar ∧ alphaBar < 1 ∧ ∀ k, alpha k ≤ alphaBar) →
      ((∃ k, 0 < alpha k) → ∃ c : ℝ, ∀ k, lam k ≤ c) →
      ∃ uhat ∈ argmin f (by
        rcases hBoundedBelow with ⟨m, hm⟩
        exact ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩),
        Tendsto (fun k => toWeakSpace ℝ H (u k)) atTop (nhds (toWeakSpace ℝ H uhat))) := by
  rcases hBoundedBelow with ⟨m, hm⟩
  have hBddBelow : BddBelow (Set.range f) :=
    ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩
  rcases hLamLower with ⟨c, hcPos, hcLower⟩
  have hLamPos (k : ℕ) : 0 < lam k := by
    linarith [hcLower k]
  have hLamNe (k : ℕ) : lam k ≠ 0 := ne_of_gt (hLamPos k)
  have hAlphaNonneg (k : ℕ) : 0 ≤ alpha k := (hAlpha k).1
  have hAlphaLeOne (k : ℕ) : alpha k ≤ 1 := (hAlpha k).2
  have hEpsNonneg (k : ℕ) : 0 ≤ eps k := hEps k
  have hEpsSummable : Summable eps := by
    apply Summable.of_nonneg_of_le (fun k => hEpsNonneg k)
    · intro k
      have hmul : c * eps k ≤ lam k * eps k :=
        mul_le_mul_of_nonneg_right (hcLower k) (hEpsNonneg k)
      calc
        eps k = c⁻¹ * (c * eps k) := by field_simp [ne_of_gt hcPos]
        _ ≤ c⁻¹ * (lam k * eps k) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt (inv_pos.mpr hcPos))
    · simpa [mul_assoc] using (hErrors.mul_left c⁻¹)
  have hUpdateWitness (k : ℕ) (hk : 0 < k) :
      ∃ p ∈ epsilonSubdifferential f (eps k) (u (k + 1)),
        p = -((lam k)⁻¹ •
          (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) := by
    rcases hUpdate k hk with ⟨p, hp, hpzero⟩
    refine ⟨p, hp, ?_⟩
    exact eq_neg_of_add_eq_zero_right hpzero
  have hIterateLtTop (k : ℕ) (hk : 0 < k) : f (u (k + 1)) < ⊤ := by
    rcases hUpdateWitness k hk with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) + (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    rcases hProper.2 with ⟨y, hy⟩
    by_contra hnot
    have htop : f (u (k + 1)) = ⊤ := top_unique (not_lt.mp hnot)
    have hbound := hp y
    rw [htop] at hbound
    have hyTop : f y = ⊤ := top_unique (by simpa using hbound)
    exact hy.ne hyTop
  have hDescent (k : ℕ) (hk : 1 < k) :
      (f (u (k + 1))).toReal - (f (u k)).toReal ≤
        -(lam k)⁻¹ * ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - u k⟫_ℝ + eps k := by
    rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) + (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    have hstep : f (u k) ≥ f (u (k + 1)) +
        (⟪p, u k - u (k + 1)⟫_ℝ : EReal) - eps k := hp (u k)
    have hnextTop := hIterateLtTop k (by omega)
    have hcurrTop : f (u k) < ⊤ := by
      have hprev := hIterateLtTop (k - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hprev
      exact hprev
    have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
    have hcurrBot : f (u k) ≠ ⊥ := hProper.1 _
    have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
      (EReal.coe_toReal hnextTop.ne hnextBot).symm
    have hcurr : f (u k) = ((f (u k)).toReal : EReal) :=
      (EReal.coe_toReal hcurrTop.ne hcurrBot).symm
    rw [hnext, hcurr, hpEq] at hstep
    norm_cast at hstep
    have hdiff : u k - u (k + 1) = -(u (k + 1) - u k) := by abel
    rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
    simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
    linarith
  have hEnergyStep := alvarez_energy_step u f eps lam alpha hAlpha hLamPos
    hRatioAntitone hDescent
  let E : ℕ → ℝ := fun n =>
    alpha (n + 1) / (2 * lam (n + 1)) * ‖u (n + 2) - u (n + 1)‖ ^ 2 +
      (f (u (n + 2))).toReal
  let W : ℕ → ℝ := fun n =>
    alpha (n + 2) / (2 * lam (n + 2)) *
        ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 +
      (1 - alpha (n + 2)) / lam (n + 2) * ‖u (n + 3) - u (n + 2)‖ ^ 2
  let R : ℕ → ℝ := fun n => eps (n + 2)
  have hWnonneg (n : ℕ) : 0 ≤ W n := by
    dsimp [W]
    have hfirst : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) := by
      apply div_nonneg (hAlphaNonneg _)
      exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
    have hsecond : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) := by
      exact div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    positivity
  have hElower (n : ℕ) : m ≤ E n := by
    dsimp [E]
    have htop := hIterateLtTop (n + 1) (by omega)
    have hbot : f (u (n + 2)) ≠ ⊥ := hProper.1 _
    have hval : f (u (n + 2)) = ((f (u (n + 2))).toReal : EReal) :=
      (EReal.coe_toReal htop.ne hbot).symm
    have hm' := hm (u (n + 2))
    rw [hval] at hm'
    norm_cast at hm'
    have hkin : 0 ≤ alpha (n + 1) / (2 * lam (n + 1)) *
        ‖u (n + 2) - u (n + 1)‖ ^ 2 := by
      have hcoeff : 0 ≤ alpha (n + 1) / (2 * lam (n + 1)) := by
        apply div_nonneg (hAlphaNonneg _)
        exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
      positivity
    linarith
  have hRnonneg (n : ℕ) : 0 ≤ R n := hEpsNonneg _
  have hRsum : Summable R := by
    simpa [R, Nat.add_comm] using (summable_nat_add_iff 2).mpr hEpsSummable
  have hEstep (n : ℕ) : E (n + 1) + W n ≤ E n + R n := by
    have hs : E (n + 1) ≤ E n - W n + R n := by
      dsimp [E, W, R]
      convert hEnergyStep (n + 2) (by omega) using 1 <;> omega
    linarith
  have hWsum : Summable W :=
    alvarez_telescope_summable E W R m hElower hWnonneg hRnonneg hRsum hEstep
  -- Keep the two dissipations separate.  Besides being the form used in the
  -- paper, these facts are the useful input for both the residual estimate and
  -- the inertial-distance recurrence below.
  let A : ℕ → ℝ := fun n =>
    alpha (n + 2) / (2 * lam (n + 2)) *
      ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2
  let B : ℕ → ℝ := fun n =>
    (1 - alpha (n + 2)) / lam (n + 2) * ‖u (n + 3) - u (n + 2)‖ ^ 2
  have hAnonneg (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    have hcoeff : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) := by
      apply div_nonneg (hAlphaNonneg _)
      exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
    positivity
  have hBnonneg (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    have hcoeff : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) := by
      exact div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    positivity
  have hA_le (n : ℕ) : A n ≤ W n := by
    dsimp [A, B, W]
    have hsecond : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) *
        ‖u (n + 3) - u (n + 2)‖ ^ 2 := by
      exact hBnonneg n
    linarith
  have hB_le (n : ℕ) : B n ≤ W n := by
    dsimp [A, B, W]
    have hfirst : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) *
        ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 := by
      exact hAnonneg n
    linarith
  have hAsum : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hA_le hWsum
  have hBsum : Summable B :=
    Summable.of_nonneg_of_le hBnonneg hB_le hWsum
  have hA0 : Tendsto A atTop (nhds 0) := hAsum.tendsto_atTop_zero
  have hB0 : Tendsto B atTop (nhds 0) := hBsum.tendsto_atTop_zero
  have hSecondDiffShift : Tendsto (fun n =>
      (alpha (n + 2) / lam (n + 2)) •
        (u (n + 3) - 2 • u (n + 2) + u (n + 1))) atTop (nhds 0) := by
    apply alvarez_tendsto_zero_of_sq_le _ A (2 / c) (by positivity) hA0
    intro n
    have hratio0 : 0 ≤ alpha (n + 2) / lam (n + 2) :=
      div_nonneg (hAlphaNonneg _) (le_of_lt (hLamPos _))
    have hratio : alpha (n + 2) / lam (n + 2) ≤ 1 / c := by
      apply (div_le_div_iff₀ (hLamPos _) hcPos).mpr
      have : alpha (n + 2) * c ≤ c := by
        rw [mul_comm]
        exact mul_le_of_le_one_right hcPos.le (hAlphaLeOne _)
      linarith [hcLower (n + 2)]
    have hcoeff : (alpha (n + 2) / lam (n + 2)) ^ 2 ≤
        2 / c * (alpha (n + 2) / (2 * lam (n + 2))) := by
      calc
        (alpha (n + 2) / lam (n + 2)) ^ 2 =
            (alpha (n + 2) / lam (n + 2)) * (alpha (n + 2) / lam (n + 2)) := by ring
        _ ≤ (alpha (n + 2) / lam (n + 2)) * (1 / c) :=
          mul_le_mul_of_nonneg_left hratio hratio0
        _ = 2 / c * (alpha (n + 2) / (2 * lam (n + 2))) := by
          field_simp [hLamNe _, ne_of_gt hcPos]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio0]
    calc
      (alpha (n + 2) / lam (n + 2) *
          ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖) ^ 2 =
          (alpha (n + 2) / lam (n + 2)) ^ 2 *
            ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 := by ring
      _ ≤ (2 / c * (alpha (n + 2) / (2 * lam (n + 2)))) *
            ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = (2 / c) * A n := by simp [A, mul_assoc]
  have hSecondDiff : Tendsto (fun k =>
      (alpha k / lam k) •
        (u (k + 1) - 2 • u k + u (k - 1))) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => (alpha k / lam k) •
        (u (k + 1) - 2 • u k + u (k - 1))) 2 0 hSecondDiffShift
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hFirstDiffShift : Tendsto (fun n =>
      ((1 - alpha (n + 2)) / lam (n + 2)) •
        (u (n + 3) - u (n + 2))) atTop (nhds 0) := by
    apply alvarez_tendsto_zero_of_sq_le _ B (1 / c) (by positivity) hB0
    intro n
    have hratio0 : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) :=
      div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    have hratio : (1 - alpha (n + 2)) / lam (n + 2) ≤ 1 / c := by
      apply (div_le_div_iff₀ (hLamPos _) hcPos).mpr
      nlinarith [hcLower (n + 2), hAlphaNonneg (n + 2)]
    have hcoeff : ((1 - alpha (n + 2)) / lam (n + 2)) ^ 2 ≤
        (1 / c) * ((1 - alpha (n + 2)) / lam (n + 2)) := by
      rw [pow_two]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hratio hratio0
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio0]
    calc
      (((1 - alpha (n + 2)) / lam (n + 2)) *
          ‖u (n + 3) - u (n + 2)‖) ^ 2 =
          ((1 - alpha (n + 2)) / lam (n + 2)) ^ 2 *
            ‖u (n + 3) - u (n + 2)‖ ^ 2 := by ring
      _ ≤ ((1 / c) * ((1 - alpha (n + 2)) / lam (n + 2))) *
            ‖u (n + 3) - u (n + 2)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = (1 / c) * B n := by simp [B, mul_assoc]
  have hFirstDiff : Tendsto (fun k =>
      ((1 - alpha k) / lam k) • (u (k + 1) - u k)) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => ((1 - alpha k) / lam k) • (u (k + 1) - u k)) 2 0 hFirstDiffShift
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hResidual : Tendsto (fun k => (lam k)⁻¹ •
      (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) := by
    have h := hSecondDiff.add hFirstDiff
    have h' : Tendsto (fun k =>
        (alpha k / lam k) • (u (k + 1) - 2 • u k + u (k - 1)) +
          ((1 - alpha k) / lam k) • (u (k + 1) - u k)) atTop (nhds 0) := by
      simpa using h
    convert h' using 1
    ext k
    rw [alvarez_residual_decomposition]
    simp only [Pi.add_apply, smul_add, smul_smul, div_eq_mul_inv]
    module
  have hResidualNormShift : Tendsto (fun n => ‖(lam (n + 1))⁻¹ •
      (u (n + 2) - (1 + alpha (n + 1)) • u (n + 1) +
        alpha (n + 1) • u n)‖) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
    simpa [Nat.add_sub_cancel] using hResidual.norm.comp hshift
  have hInfDistShift : Tendsto (fun n => Metric.infDist 0
      (epsilonSubdifferential f (eps (n + 1)) (u (n + 2)))) atTop (nhds 0) := by
    apply squeeze_zero (fun n => Metric.infDist_nonneg)
    · intro n
      rcases hUpdateWitness (n + 1) (by omega) with ⟨p, hp, hpEq⟩
      calc
        Metric.infDist 0 (epsilonSubdifferential f (eps (n + 1)) (u (n + 2))) ≤
            dist 0 p := Metric.infDist_le_dist_of_mem hp
        _ = ‖p‖ := by simp
        _ = ‖(lam (n + 1))⁻¹ •
            (u (n + 2) - (1 + alpha (n + 1)) • u (n + 1) +
              alpha (n + 1) • u n)‖ := by
              rw [hpEq, norm_neg]
              simp [Nat.add_sub_cancel]
    · exact hResidualNormShift
  have hInfDist : Tendsto (fun k => Metric.infDist 0
      (epsilonSubdifferential f (eps k) (u (k + 1)))) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => Metric.infDist 0 (epsilonSubdifferential f (eps k) (u (k + 1)))) 1 0
      hInfDistShift
    simpa [Nat.add_assoc] using h
  refine ⟨hResidual, hInfDist, ?_⟩
  intro hArgmin hAlphaBar hLamUpper
  rcases hAlphaBar with ⟨alphaBar, hAlphaBarPos, hAlphaBarLt, hAlphaBar⟩
  have hLower : LowerSemicontinuous f :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).2 hClosed
  have hLevelClosed (r : ℝ) : IsClosed (ERealFunction.lowerLevelSet f r) :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hLower r
  have hLevelConv (r : ℝ) : Convex ℝ (ERealFunction.lowerLevelSet f r) :=
    alvarez_lower_level_convex hConvex r
  have hinner (z : H) (hz : z ∈ argmin f hBddBelow) (k : ℕ) (hk : 1 ≤ k) :
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
        u (k + 1) - z⟫_ℝ ≤ lam k * eps k := by
    rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) +
      (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    have hmin : f z ≤ f (u (k + 1)) := by
      have hz_eq : f z = sInf (Set.range f) := hz
      rw [hz_eq]
      exact csInf_le hBddBelow ⟨u (k + 1), rfl⟩
    have hnextTop := hIterateLtTop k (by omega)
    have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
    have hzTop : f z < ⊤ := lt_of_le_of_lt hmin hnextTop
    have hzBot : f z ≠ ⊥ := hProper.1 _
    have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
      (EReal.coe_toReal hnextTop.ne hnextBot).symm
    have hzReal : f z = ((f z).toReal : EReal) :=
      (EReal.coe_toReal hzTop.ne hzBot).symm
    have hstep := hp z
    rw [hzReal, hnext] at hstep hmin
    rw [hpEq] at hstep
    norm_cast at hstep hmin
    have hdiff : z - u (k + 1) = -(u (k + 1) - z) := by abel
    rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
    simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
    have hresidual : (lam k)⁻¹ *
        ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - z⟫_ℝ ≤ eps k := by
      linarith [hstep, hmin]
    have hlam_nonneg : (0 : ℝ) ≤ lam k := (hLamPos k).le
    have hscaled : lam k *
        ((lam k)⁻¹ *
          ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
            u (k + 1) - z⟫_ℝ) ≤ lam k * eps k :=
      mul_le_mul_of_nonneg_left hresidual hlam_nonneg
    calc
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - z⟫_ℝ = lam k * ((lam k)⁻¹ *
          ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
            u (k + 1) - z⟫_ℝ) := by field_simp [hLamNe k]
      _ ≤ lam k * eps k := hscaled
  let delta : ℕ → ℝ := fun k =>
    alpha k * ‖u k - u (k - 1)‖ ^ 2 +
      (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2 + lam k * eps k
  have hdeltaNonneg (k : ℕ) : 0 ≤ delta k := by
    dsimp [delta]
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (hAlphaNonneg k) (sq_nonneg _)
      · exact mul_nonneg (div_nonneg (hAlphaNonneg k) (by norm_num)) (sq_nonneg _)
    · exact mul_nonneg (le_of_lt (hLamPos k)) (hEpsNonneg k)
  have hrec (z : H) (hz : z ∈ argmin f hBddBelow) (k : ℕ) (hk : 1 ≤ k) :
      (1 / 2 : ℝ) * ‖u (k + 1) - z‖ ^ 2 -
          (1 + alpha k) * ((1 / 2 : ℝ) * ‖u k - z‖ ^ 2) +
          alpha k * ((1 / 2 : ℝ) * ‖u (k - 1) - z‖ ^ 2) ≤ delta k := by
    simpa [delta] using
      alvarez_phi_recurrence_of_inner u alpha lam eps z hAlphaNonneg (hinner z hz) k hk
  set_option maxHeartbeats 800000 in
  have hdeltaSum : Summable delta := by
    by_cases hSomeAlpha : ∃ k, 0 < alpha k
    · rcases hLamUpper hSomeAlpha with ⟨L₀, hL₀⟩
      let L : ℝ := max L₀ 1
      have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      have hL : ∀ k, lam k ≤ L := fun k => le_trans (hL₀ k) (le_max_left _ _)
      let q : ℝ := (1 - alphaBar) / L
      have hq : 0 < q := div_pos (by linarith) hLpos
      have hqle (k : ℕ) : q ≤ (1 - alpha k) / lam k := by
        dsimp [q]
        apply (div_le_div_iff₀ hLpos (hLamPos k)).mpr
        have h₁ : 0 ≤ 1 - alphaBar := by linarith
        have h₂ : 1 - alphaBar ≤ 1 - alpha k := by linarith [hAlphaBar k]
        calc
          (1 - alphaBar) * lam k ≤ (1 - alphaBar) * L :=
            mul_le_mul_of_nonneg_left (hL k) h₁
          _ ≤ (1 - alpha k) * L :=
            mul_le_mul_of_nonneg_right h₂ (le_of_lt hLpos)
      have hIncShift : Summable (fun n => ‖u (n + 3) - u (n + 2)‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        · intro n
          have hqD := mul_le_mul_of_nonneg_right (hqle (n + 2)) (sq_nonneg (‖u (n + 3) - u (n + 2)‖))
          calc
            ‖u (n + 3) - u (n + 2)‖ ^ 2 =
                q⁻¹ * (q * ‖u (n + 3) - u (n + 2)‖ ^ 2) := by
                  field_simp [ne_of_gt hq]
            _ ≤ q⁻¹ * ((1 - alpha (n + 2)) / lam (n + 2) *
                ‖u (n + 3) - u (n + 2)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hqD (le_of_lt (inv_pos.mpr hq))
            _ = q⁻¹ * B n := by simp [B, mul_assoc]
        · exact hBsum.mul_left q⁻¹
      have hIncSum : Summable (fun k => ‖u (k + 1) - u k‖ ^ 2) := by
        have h := (summable_nat_add_iff (f := fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) 2).mp hIncShift
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hPrev : Summable (fun k => alpha k * ‖u k - u (k - 1)‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun k => mul_nonneg (hAlphaNonneg k) (sq_nonneg _))
        · intro k
          exact mul_le_of_le_one_left (sq_nonneg _) (hAlphaLeOne k)
        · have hprevBase : Summable (fun k : ℕ => ‖u k - u (k - 1)‖ ^ 2) := by
            apply (summable_nat_add_iff (f := fun k : ℕ => ‖u k - u (k - 1)‖ ^ 2) 1).mp
            simpa [Nat.add_sub_cancel] using hIncSum
          exact hprevBase
      have hNext : Summable (fun k => (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun k =>
          mul_nonneg (div_nonneg (hAlphaNonneg k) (by norm_num)) (sq_nonneg _))
        · intro k
          have halpha : alpha k / 2 ≤ (1 : ℝ) / 2 := by
            nlinarith [hAlphaLeOne k]
          exact mul_le_mul_of_nonneg_right halpha (sq_nonneg _)
        · exact hIncSum.mul_left (1 / 2 : ℝ)
      exact (hPrev.add hNext).add hErrors
    · have hAlphaZero : ∀ k, alpha k = 0 := by
        intro k
        apply le_antisymm
        · by_contra hnot
          exact hSomeAlpha ⟨k, lt_of_not_ge hnot⟩
        · exact hAlphaNonneg k
      convert hErrors using 1
      funext k
      dsimp [delta]
      rw [hAlphaZero k]
      ring
  have hdist (z : H) (hz : z ∈ argmin f hBddBelow) :
      ∃ l : ℝ, Tendsto (fun k => ‖u k - z‖) atTop (nhds l) :=
    alvarez_norm_converges_of_recurrence u z alpha delta alphaBar hAlphaNonneg hAlphaBar
      hAlphaBarLt hdeltaNonneg hdeltaSum (hrec z hz)
  have hcluster (z : H) :
      IsSequentialClusterPt (fun k => toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H z) →
        z ∈ argmin f hBddBelow := by
    intro hz
    rcases hz.exists_subseq_tendsto with ⟨phi, hphiStrict, hphiWeak⟩
    have hphiTop : Tendsto phi atTop atTop := hphiStrict.tendsto_atTop
    have hSubseqWeak : Tendsto (fun n => toWeakSpace ℝ H (u (phi n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiWeak
    rcases hArgmin with ⟨z0, hz0⟩
    have hz0_eq : f z0 = sInf (Set.range f) := hz0
    have hdist0 := hdist z0 hz0
    rcases hdist0 with ⟨l0, hdist0⟩
    have huBound : Bornology.IsBounded (Set.range u) :=
      bounded_range_of_convergent_distance_to_point ⟨l0, hdist0⟩
    have hresBound : Tendsto (fun k => (lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) :=
      hResidual
    have hinnerZero : Tendsto (fun k => ⟪(lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
        u k - z0⟫_ℝ) atTop (nhds 0) := by
      apply alvarez_inner_tendsto_zero_of_bounded _ _ hresBound
      have huBound' := huBound
      rw [isBounded_iff_forall_norm_le] at huBound' ⊢
      rcases huBound' with ⟨C, hC⟩
      refine ⟨C + ‖z0‖, ?_⟩
      rintro y ⟨k, rfl⟩
      calc
        ‖u k - z0‖ ≤ ‖u k‖ + ‖z0‖ := norm_sub_le _ _
        _ ≤ C + ‖z0‖ := by
          simpa [add_comm] using add_le_add_left (hC _ (Set.mem_range_self k)) ‖z0‖
    have hinnerNext : Tendsto (fun k => ⟪(lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
        u (k + 1) - z0⟫_ℝ) atTop (nhds 0) := by
      apply alvarez_inner_tendsto_zero_of_bounded _ _ hresBound
      have huBound' := huBound
      rw [isBounded_iff_forall_norm_le] at huBound' ⊢
      rcases huBound' with ⟨C, hC⟩
      refine ⟨C + ‖z0‖, ?_⟩
      rintro y ⟨k, rfl⟩
      calc
        ‖u (k + 1) - z0‖ ≤ ‖u (k + 1)‖ + ‖z0‖ := norm_sub_le _ _
        _ ≤ C + ‖z0‖ := by
          simpa [add_comm] using add_le_add_left (hC _ (Set.mem_range_self (k + 1))) ‖z0‖
    have hEpsZero : Tendsto eps atTop (nhds 0) := hEpsSummable.tendsto_atTop_zero
    have hz0Top : f z0 < ⊤ := by
      have hmin : f z0 ≤ f (u 2) := by
        rw [hz0_eq]
        exact csInf_le hBddBelow ⟨u 2, rfl⟩
      exact lt_of_le_of_lt hmin (hIterateLtTop 1 (by omega))
    have hz0Bot : f z0 ≠ ⊥ := hProper.1 _
    have hz0Real : f z0 = ((f z0).toReal : EReal) :=
      (EReal.coe_toReal hz0Top.ne hz0Bot).symm
    have hgapLower (k : ℕ) (hk : 1 < k) :
        0 ≤ (f (u k)).toReal - (f z0).toReal := by
      have hmin : f z0 ≤ f (u k) := by
        rw [hz0_eq]
        exact csInf_le hBddBelow ⟨u k, rfl⟩
      have htop : f (u k) < ⊤ := by
        have heq : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
        rw [← heq]
        exact hIterateLtTop (k - 1) (by omega)
      have hbot : f (u k) ≠ ⊥ := hProper.1 _
      have hreal : f (u k) = ((f (u k)).toReal : EReal) :=
        (EReal.coe_toReal htop.ne hbot).symm
      rw [hz0Real, hreal] at hmin
      norm_cast at hmin
      linarith
    have hgapUpper (k : ℕ) (hk : 1 < k) :
        (f (u (k + 1))).toReal - (f z0).toReal ≤
          -⟪(lam k)⁻¹ •
            (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
            u (k + 1) - z0⟫_ℝ + eps k := by
      rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
      change ∀ y : H, f y ≥ f (u (k + 1)) +
        (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
      have hstep := hp z0
      have hnextTop := hIterateLtTop k (by omega)
      have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
      have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
        (EReal.coe_toReal hnextTop.ne hnextBot).symm
      rw [hz0Real, hnext, hpEq] at hstep
      norm_cast at hstep
      have hdiff : z0 - u (k + 1) = -(u (k + 1) - z0) := by abel
      rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
      simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
      rw [real_inner_smul_left]
      linarith
    have hgap : Tendsto (fun k => (f (u k)).toReal - (f z0).toReal) atTop (nhds 0) := by
      have hupper : Tendsto (fun k => -⟪(lam k)⁻¹ •
          (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
          u (k + 1) - z0⟫_ℝ + eps k) atTop (nhds 0) := by
        simpa using hinnerNext.neg.add hEpsZero
      have hshift : Tendsto (fun k : ℕ => k + 2) atTop atTop :=
        tendsto_atTop_mono (fun k => by
          simpa only [id_eq] using Nat.le_add_right k 2) tendsto_id
      have hupperShift : Tendsto (fun k => -⟪(lam (k + 2))⁻¹ •
          (u (k + 3) - (1 + alpha (k + 2)) • u (k + 2) + alpha (k + 2) • u (k + 1)),
          u (k + 3) - z0⟫_ℝ + eps (k + 2)) atTop (nhds 0) := by
        simpa using hupper.comp hshift
      have hgapShift : Tendsto (fun k => (f (u (k + 3))).toReal - (f z0).toReal)
          atTop (nhds 0) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperShift
        · filter_upwards [Filter.eventually_atTop.2 ⟨2, by intro k hk; exact hgapLower (k + 3) (by omega)⟩]
          intro k hk
          exact hk
        · filter_upwards [] with k
          simpa using hgapUpper (k + 2) (by omega)
      have h := alvarez_tendsto_of_nat_add
        (fun k => (f (u k)).toReal - (f z0).toReal) 3 0 hgapShift
      simpa [Nat.add_assoc] using h
    have hgapPhi : Tendsto (fun n => (f (u (phi n))).toReal - (f z0).toReal)
        atTop (nhds 0) := hgap.comp hphiTop
    have hz_le_add (d : ℝ) (hd : 0 < d) :
        f z ≤ ((f z0).toReal + d : EReal) := by
      have hev : ∀ᶠ n in atTop,
          (f (u (phi n))).toReal - (f z0).toReal < d :=
        (tendsto_order.1 hgapPhi).2 d hd
      rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
      let M : ℕ := max N 2
      have hshiftM : Tendsto (fun n : ℕ => n + M) atTop atTop :=
        tendsto_atTop_mono (fun n => by
          simpa only [id_eq] using Nat.le_add_right n M) tendsto_id
      have hgapPhiM : Tendsto (fun n =>
          (f (u (phi (n + M)))).toReal - (f z0).toReal) atTop (nhds 0) := by
        simpa [Function.comp_def] using hgapPhi.comp hshiftM
      have hSubseqWeakM : Tendsto (fun n =>
          toWeakSpace ℝ H (u (phi (n + M)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [Function.comp_def] using hSubseqWeak.comp hshiftM
      have hphi2 : 2 ≤ phi 2 := by
        have h01 := hphiStrict (by omega : 0 < 1)
        have h12 := hphiStrict (by omega : 1 < 2)
        omega
      have hmem : ∀ n, u (phi (n + M)) ∈
          ERealFunction.lowerLevelSet f ((f z0).toReal + d) := by
        intro n
        have hn : (f (u (phi (n + M)))).toReal - (f z0).toReal < d := by
          apply hN
          dsimp [M]
          omega
        rw [ERealFunction.mem_lowerLevelSet_iff]
        have hphiM : 2 ≤ phi (n + M) := by
          apply le_trans hphi2
          exact hphiStrict.monotone (by dsimp [M]; omega)
        have htop : f (u (phi (n + M))) < ⊤ := by
          have heq : phi (n + M) - 1 + 1 = phi (n + M) :=
            Nat.sub_add_cancel (by omega)
          rw [← heq]
          exact hIterateLtTop (phi (n + M) - 1) (by omega)
        have hbot : f (u (phi (n + M))) ≠ ⊥ := hProper.1 _
        rw [(EReal.coe_toReal htop.ne hbot).symm]
        exact_mod_cast (le_of_lt (by linarith))
      have hzlevel := mem_of_tendsto_weakly_of_isClosed_convex
        (hLevelClosed ((f z0).toReal + d)) (hLevelConv ((f z0).toReal + d)) hmem hSubseqWeakM
      rw [ERealFunction.mem_lowerLevelSet_iff] at hzlevel
      exact hzlevel
    have hztop : f z < ⊤ := by
      apply lt_of_le_of_lt (hz_le_add 1 (by norm_num))
      rw [← EReal.coe_add]
      exact EReal.coe_lt_top _
    have hzbot : f z ≠ ⊥ := hProper.1 _
    have hzreal : f z = ((f z).toReal : EReal) :=
      (EReal.coe_toReal hztop.ne hzbot).symm
    have hzLe : f z ≤ f z0 := by
      rw [hzreal, hz0Real]
      apply (EReal.coe_le_coe_iff).mpr
      apply le_of_forall_pos_le_add
      intro d hd
      have h := hz_le_add d hd
      rw [hzreal, ← EReal.coe_add] at h
      exact EReal.coe_le_coe_iff.mp h
    rw [argmin]
    apply le_antisymm
    · simpa [hz0_eq] using hzLe
    · exact csInf_le hBddBelow ⟨z, rfl⟩
  exact opial_lemma hArgmin u hdist hcluster

end Alvarez2000
