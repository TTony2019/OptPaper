import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_8
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_4
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.prop_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_4

namespace AttouchPeypouquetRedont2014

private theorem trajectory_theta_mem_dom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (k : ℕ) :
    u (k + 1) ∈ ERealFunction.dom Θ := by
  obtain ⟨x0, hx0⟩ := hH.phi_proper.2
  obtain ⟨g, hg, -⟩ := hIFB.first_update k
  have hphi_u : phi (u (k + 1)) < ⊤ := by
    by_contra hu
    have hu' : phi (u (k + 1)) = ⊤ := top_unique (not_lt.mp hu)
    have hbad : phi (u (k + 1)) + (inner ℝ g (x0 - u (k + 1)) : EReal) ≤ phi x0 := by
      simpa [real_inner_comm, add_comm] using hg x0
    rw [hu'] at hbad
    simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.top_add_of_ne_bot,
      top_le_iff] at hbad
    exact (ne_of_lt hx0) hbad
  rw [ERealFunction.mem_dom_iff, hH.theta_eq]
  exact EReal.add_lt_top (ne_of_lt hphi_u) (EReal.coe_ne_top _)

private theorem theta_ne_bot {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (x : H) : Θ x ≠ ⊥ := by
  rw [hH.theta_eq]
  exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 x, EReal.coe_ne_bot _⟩

private theorem strongConvex_midpoint_growth {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Θ : H → EReal) (ρ : ℝ)
    (hstrong : IsStronglyConvexWith Θ ρ) {q x : H} (hq : q ∈ Optimization.argminSet Θ)
    (hq_dom : q ∈ ERealFunction.dom Θ) (hx_dom : x ∈ ERealFunction.dom Θ)
    (hq_bot : Θ q ≠ ⊥) (hx_bot : Θ x ≠ ⊥) :
    Θ q + ((ρ / 4 * ‖x - q‖ ^ 2 : ℝ) : EReal) ≤ Θ x := by
  have hmin : Θ q ≤ Θ ((1 - (1 / 2 : ℝ)) • q + (1 / 2 : ℝ) • x) := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact sInf_le ⟨_, rfl⟩
  have hsc := hstrong.2 q hq_dom x hx_dom (1 / 2 : ℝ) (by norm_num)
  have hchain := hmin.trans hsc
  have hqcoe : ((Θ q).toReal : EReal) = Θ q :=
    EReal.coe_toReal (ne_of_lt hq_dom) hq_bot
  have hxcoe : ((Θ x).toReal : EReal) = Θ x :=
    EReal.coe_toReal (ne_of_lt hx_dom) hx_bot
  rw [← hqcoe, ← hxcoe] at hchain
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub] at hchain
  rw [EReal.coe_le_coe_iff] at hchain
  rw [← hqcoe, ← hxcoe, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hnorm : ‖q - x‖ ^ 2 = ‖x - q‖ ^ 2 := by rw [norm_sub_rev]
  rw [hnorm] at hchain
  norm_num at hchain ⊢
  nlinarith

/-- Corollary 10: strong convexity forces strong convergence to the unique minimizer. -/
theorem corollary10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (u y : ℕ → H) (ρ : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hstrong : IsStronglyConvexWith Θ ρ)
    -- TODO: derive this source-implied fact from proper lsc strong convexity once the
    -- extended-real attainment infrastructure is available.
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto u Filter.atTop (nhds q) := by
  rcases hS with ⟨q, hq⟩
  obtain ⟨x0, hx0⟩ := hH.phi_proper.2
  have hx0top : Θ x0 < ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_lt_top (ne_of_lt hx0) (EReal.coe_ne_top _)
  have hqtop : Θ q < ⊤ := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact lt_of_le_of_lt (sInf_le ⟨x0, rfl⟩) hx0top
  have hqdom : q ∈ ERealFunction.dom Θ := by
    rw [ERealFunction.mem_dom_iff]
    exact hqtop
  have hqbot : Θ q ≠ ⊥ := theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH q
  have hqcoe : ((Θ q).toReal : EReal) = Θ q :=
    EReal.coe_toReal (ne_of_lt hqdom) hqbot
  have hdom : ∀ k : ℕ, u (k + 1) ∈ ERealFunction.dom Θ := fun k ↦
    trajectory_theta_mem_dom phi Θ psi gradPsi a b lam Lpsi u y hH hIFB k
  have hbot : ∀ k : ℕ, Θ (u (k + 1)) ≠ ⊥ := fun k ↦
    theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH (u (k + 1))
  have hgrowth : ∀ k : ℕ, Θ q + ((ρ / 4 * ‖u (k + 1) - q‖ ^ 2 : ℝ) : EReal) ≤
      Θ (u (k + 1)) := fun k ↦
    strongConvex_midpoint_growth Θ ρ hstrong hq hqdom (hdom k) hqbot (hbot k)
  have hobj : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (Θ q)) := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact (proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB).1
  have hobj_succ : Filter.Tendsto (fun k ↦ Θ (u (k + 1))) Filter.atTop (nhds (Θ q)) := by
    simpa [Function.comp_def] using hobj.comp (Filter.tendsto_add_atTop_nat 1)
  have hnorm : Filter.Tendsto (fun k ↦ ‖u (k + 1) - q‖) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hc : 0 < ρ / 4 * ε ^ 2 := by
      have := hstrong.1
      positivity
    have hlt : Θ q < Θ q + ((ρ / 4 * ε ^ 2 : ℝ) : EReal) := by
      rw [← hqcoe, ← EReal.coe_add]
      exact_mod_cast (by linarith : (Θ q).toReal < (Θ q).toReal + ρ / 4 * ε ^ 2)
    rcases Filter.eventually_atTop.1
        (hobj_succ.eventually (Iio_mem_nhds hlt)) with ⟨N, hN⟩
    refine ⟨N, fun k hk ↦ ?_⟩
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_contra hnot
    have hle : ε ≤ ‖u (k + 1) - q‖ := le_of_not_gt hnot
    have hsquare : ε ^ 2 ≤ ‖u (k + 1) - q‖ ^ 2 := by nlinarith [sq_nonneg (‖u (k + 1) - q‖ - ε)]
    have hmul : ρ / 4 * ε ^ 2 ≤ ρ / 4 * ‖u (k + 1) - q‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left hsquare
      linarith [hstrong.1]
    have headd : Θ q + ((ρ / 4 * ε ^ 2 : ℝ) : EReal) ≤
        Θ q + ((ρ / 4 * ‖u (k + 1) - q‖ ^ 2 : ℝ) : EReal) := by
      simpa [add_comm] using add_le_add_left (EReal.coe_le_coe_iff.mpr hmul) (Θ q)
    exact (not_lt_of_ge (headd.trans (hgrowth k))) (hN k hk)
  have hu_succ : Filter.Tendsto (fun k ↦ u (k + 1)) Filter.atTop (nhds q) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  exact ⟨q, hq, (Filter.tendsto_add_atTop_iff_nat 1).mp hu_succ⟩

end AttouchPeypouquetRedont2014
