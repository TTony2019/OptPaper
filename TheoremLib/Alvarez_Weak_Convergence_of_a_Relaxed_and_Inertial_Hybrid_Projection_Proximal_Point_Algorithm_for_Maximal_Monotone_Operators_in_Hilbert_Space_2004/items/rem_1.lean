import Mathlib.Tactic
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.thm_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.ext_thm_1

/-!
# Remark 1
-/

open SetValuedOperator
open Filter
open scoped Topology

set_option maxHeartbeats 800000

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private lemma bounded_range_of_tendsto_norm {a : ℕ → H} {l : ℝ}
    (h : Tendsto (fun k : ℕ ↦ ‖a k‖) atTop (𝓝 l)) :
    Bornology.IsBounded (Set.range a) := by
  have hb_norm : Bornology.IsBounded (Set.range (fun k : ℕ ↦ ‖a k‖)) :=
    Metric.isBounded_range_of_tendsto _ h
  rcases isBounded_iff_forall_norm_le.mp hb_norm with ⟨C, hC⟩
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  intro y hy
  rcases hy with ⟨k, rfl⟩
  have hk := hC ‖a k‖ ⟨k, rfl⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a k))] using hk

private lemma residual_subsequence_of_weighted_summability
    {v : ℕ → H} {lam : ℕ → ℝ}
    (hweighted : Summable (fun k : ℕ ↦ (lam k) ^ 2 * ‖v k‖ ^ 2))
    (hlam_sq_diverges : ¬Summable (fun k : ℕ ↦ (lam k) ^ 2)) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      Tendsto (fun j : ℕ ↦ v (subseq j)) atTop (𝓝 (0 : H)) := by
  have hfrequently : ∀ ε : ℝ, 0 < ε →
      ∃ᶠ k in atTop, ‖v k‖ < ε := by
    intro ε hε
    by_contra hnot
    have hev : ∀ᶠ k in atTop, ε ≤ ‖v k‖ := by
      exact (not_frequently.mp hnot).mono fun k hk => le_of_not_gt hk
    have hsum_scaled :
        Summable (fun k : ℕ ↦ ε⁻¹ ^ 2 * ((lam k) ^ 2 * ‖v k‖ ^ 2)) := by
      convert hweighted.mul_left (ε⁻¹ ^ 2) using 1
    have hsum_lam : Summable (fun k : ℕ ↦ (lam k) ^ 2) := by
      refine Summable.of_norm_bounded_eventually_nat hsum_scaled ?_
      filter_upwards [hev] with k hk
      have hsq : ε ^ 2 ≤ ‖v k‖ ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (le_of_lt hε) hk
      have hmul : (lam k) ^ 2 * ε ^ 2 ≤ (lam k) ^ 2 * ‖v k‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      have hbound : (lam k) ^ 2 ≤
          ε⁻¹ ^ 2 * ((lam k) ^ 2 * ‖v k‖ ^ 2) := by
        calc
          (lam k) ^ 2 = ε⁻¹ ^ 2 * (ε ^ 2 * (lam k) ^ 2) := by
            field_simp [ne_of_gt hε]
          _ ≤ ε⁻¹ ^ 2 * ((lam k) ^ 2 * ‖v k‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hmul)
              (by positivity)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (lam k))] using hbound
    exact hlam_sq_diverges hsum_lam
  have hcluster : MapClusterPt (0 : H) atTop v := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
    exact (hfrequently ε hε).mono fun k hk =>
      hball (by simpa [Metric.mem_ball, dist_zero_right] using hk)
  exact hcluster.tendsto_subseq

/-- Remark 1: replacing (1.3) by `∑ λ_k^2 = ∞` gives a strongly null
subsequence of residuals, which is enough for convergence in finite dimension. -/
theorem remark_1_finite_dimensional_convergence
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (x v y z : ℕ → H) (lam rho : ℕ → ℝ)
    (hS : (SetValuedOperator.zeros A).Nonempty)
    (hlam_sq_diverges : ¬ Summable fun k : ℕ ↦ (lam k) ^ 2)
    (hweighted : Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖v k‖ ^ 2)
    (hfinite : FiniteDimensional ℝ H)
    (hdist :
      ∀ xbar ∈ SetValuedOperator.zeros A,
        ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l))
    (h_conn_25 :
      Tendsto
        (fun k : ℕ ↦
          ‖x (k + 1) - ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k)‖)
        atTop (𝓝 0))
    (h_incl_213 :
      ∀ k : ℕ,
        (rho k)⁻¹ • v k ∈ A ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k))
    (hR1_pos : ∃ R1 > (0 : ℝ), ∀ k : ℕ, R1 ≤ rho k)
    (hR2_lt_two : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2) :
    ∃ xstar ∈ SetValuedOperator.zeros A, Tendsto x atTop (𝓝 xstar) := by
  rcases hS with ⟨xbar0, hxbar0⟩
  rcases hdist xbar0 hxbar0 with ⟨l0, hl0⟩
  have hdiff_bdd : Bornology.IsBounded (Set.range (fun k : ℕ ↦ x k - xbar0)) :=
    bounded_range_of_tendsto_norm hl0
  have hx_bdd : Bornology.IsBounded (Set.range x) := by
    rcases isBounded_iff_forall_norm_le.mp hdiff_bdd with ⟨C, hC⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖xbar0‖, ?_⟩
    intro w hw
    rcases hw with ⟨k, rfl⟩
    calc
      ‖x k‖ = ‖(x k - xbar0) + xbar0‖ := by abel
      _ ≤ ‖x k - xbar0‖ + ‖xbar0‖ := norm_add_le _ _
      _ ≤ C + ‖xbar0‖ := by
        linarith [hC (x k - xbar0) ⟨k, rfl⟩]
  rcases residual_subsequence_of_weighted_summability hweighted hlam_sq_diverges with
    ⟨φ, hφ_strictMono, hφ_tendsto⟩
  letI : FiniteDimensional ℝ H := hfinite
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨R, hR⟩
  have h_sub_mem_ball (j : ℕ) : x (φ j + 1) ∈ Metric.closedBall (0 : H) R := by
    have hj := hR (x (φ j + 1)) ⟨φ j + 1, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hj
  rcases (ProperSpace.isCompact_closedBall (0 : H) R).tendsto_subseq h_sub_mem_ball with
    ⟨xhat, _hxhat_ball, ψ, hψ_strictMono, hψ_tendsto⟩
  have h_x_sub_tendsto :
      Tendsto (fun j : ℕ ↦ x (φ (ψ j) + 1)) atTop (𝓝 xhat) := by
    simpa [Function.comp] using hψ_tendsto
  have h_conn_25_vec :
      Tendsto
        (fun k : ℕ ↦
          x (k + 1) - ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k))
        atTop (𝓝 (0 : H)) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr h_conn_25
  let p (k : ℕ) : H := (rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k
  let k_seq (j : ℕ) : ℕ := φ (ψ j)
  have hk_seq_strictMono : StrictMono k_seq := hφ_strictMono.comp hψ_strictMono
  have hp_tendsto : Tendsto (fun j : ℕ ↦ p (k_seq j)) atTop (𝓝 xhat) := by
    have h1 : Tendsto (fun j : ℕ ↦ x (k_seq j + 1)) atTop (𝓝 xhat) := by
      simpa [k_seq] using h_x_sub_tendsto
    have h2 : Tendsto (fun j : ℕ ↦ x (k_seq j + 1) - p (k_seq j))
        atTop (𝓝 (0 : H)) := by
      simpa [p] using h_conn_25_vec.comp hk_seq_strictMono.tendsto_atTop
    have h := h1.sub h2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  rcases hR1_pos with ⟨R1, hR1_pos, hR1_le⟩
  rcases hR2_lt_two with ⟨R2, _hR2_lt_two, _hR2_ge⟩
  have hv_sub_tendsto : Tendsto (fun j : ℕ ↦ v (k_seq j)) atTop (𝓝 (0 : H)) := by
    simpa [k_seq] using hφ_tendsto.comp hψ_strictMono.tendsto_atTop
  have hv_scaled_tendsto :
      Tendsto (fun j : ℕ ↦ (rho (k_seq j))⁻¹ • v (k_seq j)) atTop (𝓝 (0 : H)) := by
    have hnorm_bound (j : ℕ) :
        ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖ ≤ R1⁻¹ * ‖v (k_seq j)‖ := by
      have hρ_pos : 0 < rho (k_seq j) := lt_of_lt_of_le hR1_pos (hR1_le (k_seq j))
      have h_abs_inv : |(rho (k_seq j))⁻¹| ≤ R1⁻¹ := by
        rw [abs_of_pos (inv_pos.mpr hρ_pos)]
        exact (inv_le_inv₀ hρ_pos hR1_pos).mpr (hR1_le (k_seq j))
      calc
        ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖ =
            |(rho (k_seq j))⁻¹| * ‖v (k_seq j)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ R1⁻¹ * ‖v (k_seq j)‖ :=
          mul_le_mul_of_nonneg_right h_abs_inv (norm_nonneg _)
    have hnorm_tendsto :
        Tendsto (fun j : ℕ ↦ ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖) atTop (𝓝 0) := by
      have hprod :
          Tendsto (fun j : ℕ ↦ R1⁻¹ * ‖v (k_seq j)‖) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hv_sub_tendsto.norm)
      exact squeeze_zero (fun j ↦ norm_nonneg _) hnorm_bound hprod
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm_tendsto
  have hp_weak_tendsto :
      Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (p (k_seq j))) atTop
        (𝓝 (toWeakSpace ℝ H xhat)) := by
    have hcont : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
    exact (hcont.tendsto xhat).comp hp_tendsto
  have hxhat_zeros : xhat ∈ SetValuedOperator.zeros A := by
    rw [SetValuedOperator.mem_zeros_iff]
    exact weak_strong_closedness_maximal_monotone_graph A hA hp_weak_tendsto hv_scaled_tendsto
      (by
        intro j
        simpa [p] using h_incl_213 (k_seq j))
  rcases hdist xhat hxhat_zeros with ⟨lhat, hlhat⟩
  have hindex_tendsto : Tendsto (fun j : ℕ ↦ k_seq j + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun j : ℕ ↦ Nat.le_add_right (k_seq j) 1)
      hk_seq_strictMono.tendsto_atTop
  have hlhat_eq_zero : lhat = 0 := by
    have hsub_lhat :
        Tendsto (fun j : ℕ ↦ ‖x (k_seq j + 1) - xhat‖) atTop (𝓝 lhat) :=
      hlhat.comp hindex_tendsto
    have hsub_zero :
        Tendsto (fun j : ℕ ↦ ‖x (k_seq j + 1) - xhat‖) atTop (𝓝 0) := by
      have hdiff := (by
        simpa [k_seq] using h_x_sub_tendsto :
          Tendsto (fun j : ℕ ↦ x (k_seq j + 1)) atTop (𝓝 xhat))
      simpa using (hdiff.sub (tendsto_const_nhds (x := xhat))).norm
    exact tendsto_nhds_unique hsub_lhat hsub_zero
  have hnorm_zero : Tendsto (fun k : ℕ ↦ ‖x k - xhat‖) atTop (𝓝 0) := by
    simpa [hlhat_eq_zero] using hlhat
  have hx_tendsto : Tendsto x atTop (𝓝 xhat) := by
    have hdiff : Tendsto (fun k : ℕ ↦ x k - xhat) atTop (𝓝 (0 : H)) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm_zero
    simpa [sub_add_cancel] using hdiff.add (tendsto_const_nhds (x := xhat))
  exact ⟨xhat, hxhat_zeros, hx_tendsto⟩

end Alvarez2004
