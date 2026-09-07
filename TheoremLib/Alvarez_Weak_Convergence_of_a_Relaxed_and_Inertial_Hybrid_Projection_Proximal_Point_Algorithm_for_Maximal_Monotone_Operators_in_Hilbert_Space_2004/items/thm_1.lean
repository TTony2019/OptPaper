import Mathlib.Tactic
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.algo_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_1
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.lem_3
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.ext_thm_1

set_option linter.style.setOption false
set_option maxHeartbeats 800000

/-!
# Theorem 2.2
-/

open SetValuedOperator
open Filter
open scoped Topology Pointwise InnerProductSpace

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem inner_norm_sq_diff_eq (a b : H) :
    ‖a‖ ^ 2 - ‖b‖ ^ 2 = 2 * ⟪a, a - b⟫_ℝ - ‖a - b‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have hself : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
  rw [inner_sub_right, hself]
  ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem sum_delta_summable
    (x : ℕ → H) (alpha : ℕ → ℝ)
    (halpha_summable : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1) :
    Summable fun k : ℕ ↦
      ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 := by
  refine halpha_summable.of_nonneg_of_le ?hnonneg ?hle
  · intro k
    have ha0 : 0 ≤ alpha k := (halpha_mem k).1
    have hs : 0 ≤ ‖x k - x (k - 1)‖ ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (alpha k)]
  · intro k
    have ha0 : 0 ≤ alpha k := (halpha_mem k).1
    have ha1 : alpha k ≤ 1 := le_of_lt (halpha_mem k).2
    have hasq_le : alpha k ^ 2 ≤ alpha k := by
      nlinarith [sq_nonneg (alpha k), mul_le_mul_of_nonneg_left ha1 ha0]
    have hs : 0 ≤ ‖x k - x (k - 1)‖ ^ 2 := sq_nonneg _
    have hcoef : (alpha k + alpha k ^ 2) / 2 ≤ alpha k := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoef hs

/-- Theorem 2.2 in the nonterminating case used in the paper proof after the
finite-stop case is discarded. -/
theorem theorem_2_2_nonterminating
    {lam alpha rho : ℕ → ℝ}
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alpha rho sigma)
    (hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0)
    (params : ParameterAssumptionsPartI alg.x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    ((∀ xbar ∈ SetValuedOperator.zeros A,
        ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l)) ∧
      Tendsto
        (fun k : ℕ ↦
          ‖alg.x (k + 1) -
            ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)‖)
        atTop (𝓝 0)) ∧
    (∀ _hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k,
      Tendsto (fun k : ℕ ↦ ‖alg.v k‖) atTop (𝓝 0) ∧
      ∃ xstar ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xstar))) := by
  have hlam_pos (k : ℕ) : 0 < lam k := by
    simpa [hlam_eq] using params.lam_pos k
  have halpha_mem (k : ℕ) : 0 ≤ alpha k ∧ alpha k < 1 := by
    simpa [halpha_eq] using params.alpha_mem k
  have halpha_upper : ∃ alpha0 : ℝ, alpha0 < 1 ∧ ∀ k : ℕ, alpha k ≤ alpha0 := by
    rcases params.alpha_upper with ⟨alpha0, hlt, hub⟩
    refine ⟨alpha0, hlt, ?_⟩
    intro k
    simpa [halpha_eq] using hub k
  obtain ⟨alpha0, halpha0_lt, halpha_le⟩ := halpha_upper
  have halpha_bound : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0 := by
    intro k
    exact ⟨(halpha_mem k).1, halpha_le k⟩
  have halpha_summable :
      Summable fun k : ℕ ↦ alpha k * ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
    simpa [halpha_eq] using params.alpha_summable
  have hdelta_summable :
      Summable fun k : ℕ ↦
        ((alpha k + alpha k ^ 2) / 2) * ‖alg.x k - alg.x (k - 1)‖ ^ 2 :=
    sum_delta_summable alg.x alpha halpha_summable halpha_mem
  have hrho_lower : ∃ R1 : ℝ, 0 < R1 ∧ ∀ k : ℕ, R1 ≤ rho k := by
    rcases params.rho_lower with ⟨R1, hpos, hlow⟩
    refine ⟨R1, hpos, ?_⟩
    intro k
    simpa [hrho_eq] using hlow k
  have hrho_upper : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2 := by
    rcases params.rho_upper with ⟨R2, hlt, hub⟩
    refine ⟨R2, hlt, ?_⟩
    intro k
    simpa [hrho_eq] using hub k
  obtain ⟨R1, hR1_pos, hR1_le⟩ := hrho_lower
  obtain ⟨R2, hR2_lt, hR2_ge⟩ := hrho_upper
  have hrho_pos (k : ℕ) : 0 < rho k := lt_of_lt_of_le hR1_pos (hR1_le k)
  have hrho_ne_zero (k : ℕ) : rho k ≠ 0 := (hrho_pos k).ne'
  have hv_norm_pos (k : ℕ) : 0 < ‖alg.v k‖ := norm_pos_iff.mpr (hv_nonzero k)
  have pos_lk_y (k : ℕ) : 0 < ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
    set u : H := (lam k)⁻¹ • (alg.y k - alg.z k)
    have hv_eq : alg.v k = u + alg.eta k := by
      have heq := alg.equation k
      calc
        alg.v k =
            (lam k)⁻¹ • (alg.y k - alg.z k) +
              ((lam k)⁻¹ • (alg.z k - alg.y k) + alg.v k) := by
          symm
          rw [← add_assoc, ← smul_add]
          simp only [sub_add_sub_cancel, sub_self, smul_zero, zero_add]
        _ = u + alg.eta k := by
          rw [heq]
    have hu_norm :
        ‖u‖ = ‖alg.z k - alg.y k‖ / lam k := by
      dsimp [u]
      rw [show alg.y k - alg.z k = -(alg.z k - alg.y k) by abel, norm_smul, norm_neg]
      have hlam_abs : |(lam k)⁻¹| = (lam k)⁻¹ := abs_of_pos (inv_pos.mpr (hlam_pos k))
      rw [Real.norm_eq_abs, hlam_abs]
      rw [div_eq_inv_mul]
    have heta_bound : ‖alg.eta k‖ ≤ sigma * max ‖u‖ ‖alg.v k‖ := by
      simpa [hu_norm] using alg.residual_bound k
    rcases lemma_2_1 hsigma hv_eq heta_bound with ⟨h_norm_bound, h_inner_bound⟩
    have hu_pos : 0 < ‖u‖ := by
      have hvpos : 0 < ‖alg.v k‖ := hv_norm_pos k
      by_contra hnot
      have hu_zero : ‖u‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg u)
      have : ‖alg.v k‖ ≤ 0 := by
        simpa [hu_zero] using h_norm_bound
      linarith
    have hinner_u_pos : 0 < ⟪alg.v k, u⟫_ℝ := by
      have hprod_pos : 0 < (1 - sigma) * ‖u‖ * ‖alg.v k‖ := by
        have hspos : 0 < 1 - sigma := sub_pos.mpr hsigma.2
        exact mul_pos (mul_pos hspos hu_pos) (hv_norm_pos k)
      exact lt_of_lt_of_le hprod_pos h_inner_bound
    have hinner_u_eq :
        ⟪alg.v k, u⟫_ℝ = (lam k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
      dsimp [u]
      simp [real_inner_smul_right]
    have hinv_pos : 0 < (lam k)⁻¹ := inv_pos.mpr (hlam_pos k)
    have hscaled_pos : 0 < (lam k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
      simpa [hinner_u_eq] using hinner_u_pos
    by_contra hnot
    have hip_nonpos : ⟪alg.v k, alg.y k - alg.z k⟫_ℝ ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos :
        (lam k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hinv_pos) hip_nonpos
    linarith
  set t : ℕ → ℝ := fun k : ℕ => ⟪alg.v k, alg.y k - alg.z k⟫_ℝ / ‖alg.v k‖ ^ 2 with ht_def
  have ht_pos (k : ℕ) : 0 < t k := by
    dsimp [t]
    exact div_pos (pos_lk_y k) (pow_pos (hv_norm_pos k) 2)
  have monotone_halfspace (k : ℕ) (xbar : H)
      (hxbar : xbar ∈ SetValuedOperator.zeros A) :
      ⟪alg.v k,
        xbar - ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)⟫_ℝ ≤ 0 := by
    set w : H := (rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k
    rcases alg.step_inclusion k with ⟨a, ha_mem, ha_eq⟩
    have hmono : 0 ≤ ⟪a - (0 : H), w - xbar⟫_ℝ := by
      exact hA.1 a ha_mem 0 hxbar
    have hmono' : 0 ≤ ⟪a, w - xbar⟫_ℝ := by
      simpa using hmono
    have hv_inner_nonneg : 0 ≤ ⟪alg.v k, w - xbar⟫_ℝ := by
      rw [← ha_eq]
      simpa [real_inner_smul_left] using
        mul_nonneg (le_of_lt (hrho_pos k)) hmono'
    have hneg : ⟪alg.v k, xbar - w⟫_ℝ = -⟪alg.v k, w - xbar⟫_ℝ := by
      rw [← inner_neg_right]
      congr 1
      abel
    rw [hneg]
    exact neg_nonpos.mpr hv_inner_nonneg
  have scaled_step_inclusion (k : ℕ) :
      (rho k)⁻¹ • alg.v k ∈
        A ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k) := by
    rcases alg.step_inclusion k with ⟨a, ha_mem, ha_eq⟩
    have ha_eq' : alg.v k = rho k • a := by
      simpa using ha_eq.symm
    have hscaled : (rho k)⁻¹ • alg.v k = a := by
      rw [ha_eq']
      rw [smul_smul]
      rw [inv_mul_cancel₀ (hrho_ne_zero k)]
      simp
    simpa [hscaled] using ha_mem
  have halfspace_inner_ineq (k : ℕ) (xbar : H)
      (hxbar : xbar ∈ SetValuedOperator.zeros A) :
      (rho k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ ≤
        ⟪alg.v k, alg.y k - xbar⟫_ℝ := by
    have hhalf := monotone_halfspace k xbar hxbar
    have hcenter :
        xbar - ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k) =
          (xbar - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k) := by
      rw [sub_eq_add_neg]
      simp only [neg_add, add_comm, add_left_comm, add_assoc, smul_add, add_smul,
        smul_sub, sub_smul, smul_neg, neg_smul, one_smul]
      abel_nf
    have hinner :
        ⟪alg.v k,
          xbar - ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)⟫_ℝ =
          -⟪alg.v k, alg.y k - xbar⟫_ℝ +
            (rho k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
      rw [hcenter, inner_add_right, real_inner_smul_right]
      have hneg :
          ⟪alg.v k, xbar - alg.y k⟫_ℝ =
            -⟪alg.v k, alg.y k - xbar⟫_ℝ := by
        rw [← inner_neg_right]
        congr 1
        abel
      rw [hneg]
    rw [hinner] at hhalf
    linarith
  have descent_ineq_aux (k : ℕ) (xbar : H)
      (hxbar : xbar ∈ SetValuedOperator.zeros A) :
      ‖alg.x (k + 1) - xbar‖ ^ 2 ≤
        ‖alg.y k - xbar‖ ^ 2 -
          (((rho k)⁻¹ * 2) - 1) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
    have hx_update :
        alg.x (k + 1) = alg.y k - (t k) • alg.v k := by
      rw [alg.update_if_nonzero k (hv_nonzero k)]
    have hinner_lower := halfspace_inner_ineq k xbar hxbar
    have ht_inner :
        ⟪alg.v k, alg.y k - alg.z k⟫_ℝ = t k * ‖alg.v k‖ ^ 2 := by
      have hden : ‖alg.v k‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (hv_norm_pos k))
      calc
        ⟪alg.v k, alg.y k - alg.z k⟫_ℝ =
            (⟪alg.v k, alg.y k - alg.z k⟫_ℝ / ‖alg.v k‖ ^ 2) *
              ‖alg.v k‖ ^ 2 := by
                field_simp [hden, ne_of_gt (hv_norm_pos k)]
        _ = t k * ‖alg.v k‖ ^ 2 := by
                rw [ht_def]
    have hinner_lower' :
        (rho k)⁻¹ * (t k * ‖alg.v k‖ ^ 2) ≤
          ⟪alg.v k, alg.y k - xbar⟫_ℝ := by
      simpa [ht_inner] using hinner_lower
    have ht_nonneg : 0 ≤ t k := le_of_lt (ht_pos k)
    rw [hx_update]
    calc
      ‖alg.y k - (t k) • alg.v k - xbar‖ ^ 2
          = ‖(alg.y k - xbar) - (t k) • alg.v k‖ ^ 2 := by
            congr 1
            abel
      _ = ‖alg.y k - xbar‖ ^ 2 -
            2 * t k * ⟪alg.y k - xbar, alg.v k⟫_ℝ +
            (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
            rw [norm_sub_sq_real]
            simp [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg ht_nonneg, pow_two]
            ring
      _ = ‖alg.y k - xbar‖ ^ 2 -
            2 * t k * ⟪alg.v k, alg.y k - xbar⟫_ℝ +
            (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
            rw [real_inner_comm]
      _ ≤ ‖alg.y k - xbar‖ ^ 2 -
            2 * t k * ((rho k)⁻¹ * (t k * ‖alg.v k‖ ^ 2)) +
            (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
            have hmul :
                2 * t k * ((rho k)⁻¹ * (t k * ‖alg.v k‖ ^ 2)) ≤
                  2 * t k * ⟪alg.v k, alg.y k - xbar⟫_ℝ := by
              exact mul_le_mul_of_nonneg_left hinner_lower' (by positivity)
            linarith
      _ = ‖alg.y k - xbar‖ ^ 2 -
            (((rho k)⁻¹ * 2) - 1) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
            ring
  have inertial_expansion (k : ℕ) (xbar : H) :
      ‖alg.y k - xbar‖ ^ 2 =
        ‖alg.x k - xbar‖ ^ 2 +
          alpha k * (‖alg.x k - xbar‖ ^ 2 -
            ‖alg.x (k - 1) - xbar‖ ^ 2) +
          (alpha k + (alpha k) ^ 2) *
            ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
    have hy := alg.y_def k
    rw [hy]
    set a : H := alg.x k - xbar
    set d : H := alg.x k - alg.x (k - 1)
    have hsub : alg.x (k - 1) - xbar = a - d := by
      dsimp [a, d]
      abel
    have hnorm :
        ‖a + alpha k • d‖ ^ 2 =
          ‖a‖ ^ 2 + 2 * alpha k * ⟪a, d⟫_ℝ +
            (alpha k) ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_add_sq_real]
      simp [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (halpha_mem k).1, pow_two]
      ring
    have hinner :
        2 * ⟪a, d⟫_ℝ =
          ‖a‖ ^ 2 - ‖a - d‖ ^ 2 + ‖d‖ ^ 2 := by
      have h := inner_norm_sq_diff_eq a (a - d)
      have hd : a - (a - d) = d := by abel
      rw [hd] at h
      linarith
    have hy_rewrite :
        alg.x k + alpha k • (alg.x k - alg.x (k - 1)) - xbar =
          a + alpha k • d := by
      dsimp [a, d]
      abel
    rw [hy_rewrite, hnorm, hsub]
    rw [show 2 * alpha k * ⟪a, d⟫_ℝ =
        alpha k * (2 * ⟪a, d⟫_ℝ) by ring, hinner]
    ring
  have h_dist_all : ∀ xbar ∈ SetValuedOperator.zeros A,
      ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l) := by
    intro xbar hxbar
    set phi : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖alg.x k - xbar‖ ^ 2 with hphi_def
    have hphi_nonneg : ∀ k : ℕ, 0 ≤ phi k := by
      intro k
      dsimp [phi]
      positivity
    set delta_seq : ℕ → ℝ :=
      fun k => ((alpha k + alpha k ^ 2) / 2) *
        ‖alg.x k - alg.x (k - 1)‖ ^ 2 with hdelta_seq_def
    have hdelta_nonneg' : ∀ k : ℕ, 0 ≤ delta_seq k := by
      intro k
      dsimp [delta_seq]
      have ha : 0 ≤ alpha k := (halpha_mem k).1
      positivity
    have hdelta_sum' : Summable delta_seq := by
      simpa [delta_seq] using hdelta_summable
    have hrecurrence_full (k : ℕ) :
        phi (k + 1) ≤
          phi k + alpha k * (phi k - phi (k - 1)) + delta_seq k -
            ((rho k)⁻¹ - 1 / 2) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
      have hdescent := descent_ineq_aux k xbar hxbar
      have hinertial := inertial_expansion k xbar
      dsimp [phi, delta_seq]
      nlinarith
    have hcoeff_nonneg (k : ℕ) : 0 ≤ (rho k)⁻¹ - (1 / 2 : ℝ) := by
      have hpos : 0 < rho k := hrho_pos k
      have hlt2 : rho k < 2 := lt_of_le_of_lt (hR2_ge k) hR2_lt
      have hlt_inv : (1 / (2 : ℝ)) < 1 / rho k :=
        one_div_lt_one_div_of_lt hpos hlt2
      have hlt_inv' : (1 / (2 : ℝ)) < (rho k)⁻¹ := by
        simpa [one_div] using hlt_inv
      linarith
    have hrecurrence (k : ℕ) :
        phi (k + 1) ≤
          phi k + alpha k * (phi k - phi (k - 1)) + delta_seq k := by
      have hfull := hrecurrence_full k
      have hnonneg :
          0 ≤ ((rho k)⁻¹ - 1 / 2) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
        exact mul_nonneg (mul_nonneg (hcoeff_nonneg k) (sq_nonneg (t k)))
          (sq_nonneg ‖alg.v k‖)
      nlinarith
    have hlemma23 :=
      lemma_2_3 phi delta_seq alpha alpha0 hphi_nonneg hdelta_nonneg'
        hrecurrence hdelta_sum' halpha_bound halpha0_lt
    rcases hlemma23 with ⟨_hsum_pospart, hconv_phi⟩
    rcases hconv_phi with ⟨phistar, hphistar_nonneg, hphi_tendsto⟩
    have h_norm_sq_tendsto :
        Tendsto (fun k : ℕ => ‖alg.x k - xbar‖ ^ 2) atTop (𝓝 (2 * phistar)) := by
      have h_eq :
          (fun k : ℕ => ‖alg.x k - xbar‖ ^ 2) =
            (fun k : ℕ => 2 * phi k) := by
        funext k
        dsimp [phi]
        ring
      rw [h_eq]
      simpa using hphi_tendsto.const_mul 2
    have h_norm_tendsto :
        Tendsto (fun k : ℕ => ‖alg.x k - xbar‖) atTop
          (𝓝 (Real.sqrt (2 * phistar))) := by
      have h_sqrt_tendsto :
          Tendsto (fun k : ℕ => Real.sqrt (‖alg.x k - xbar‖ ^ 2)) atTop
            (𝓝 (Real.sqrt (2 * phistar))) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h_norm_sq_tendsto
      have h_eq :
          (fun k : ℕ => Real.sqrt (‖alg.x k - xbar‖ ^ 2)) =
            (fun k : ℕ => ‖alg.x k - xbar‖) := by
        funext k
        simp
      simpa [h_eq] using h_sqrt_tendsto
    exact ⟨Real.sqrt (2 * phistar), h_norm_tendsto⟩
  rcases hS with ⟨xbar0, hxbar0⟩
  have hS_nonempty : (SetValuedOperator.zeros A).Nonempty := ⟨xbar0, hxbar0⟩
  have hyz_inner_lower (k : ℕ) :
      (1 - sigma) * ‖alg.y k - alg.z k‖ ≤ t k * ‖alg.v k‖ := by
    set u : H := (lam k)⁻¹ • (alg.y k - alg.z k) with hu_def
    have hv_eq : alg.v k = u + alg.eta k := by
      have heq := alg.equation k
      calc
        alg.v k =
            (lam k)⁻¹ • (alg.y k - alg.z k) +
              ((lam k)⁻¹ • (alg.z k - alg.y k) + alg.v k) := by
          symm
          rw [← add_assoc, ← smul_add]
          simp only [sub_add_sub_cancel, sub_self, smul_zero, zero_add]
        _ = u + alg.eta k := by
          rw [heq]
    have hu_norm : ‖u‖ = ‖alg.y k - alg.z k‖ / lam k := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam_pos k))]
      rw [div_eq_inv_mul]
    have heta_bound : ‖alg.eta k‖ ≤ sigma * max ‖u‖ ‖alg.v k‖ := by
      simpa [hu_norm, norm_sub_rev] using alg.residual_bound k
    rcases lemma_2_1 hsigma hv_eq heta_bound with ⟨_hnorm_bound, hinner_bound⟩
    have hinner_eq :
        ⟪alg.v k, u⟫_ℝ =
          (lam k)⁻¹ * ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
      dsimp [u]
      simp [real_inner_smul_right]
    have htv_eq : t k * ‖alg.v k‖ =
        ⟪alg.v k, alg.y k - alg.z k⟫_ℝ / ‖alg.v k‖ := by
      dsimp [t]
      field_simp [(hv_norm_pos k).ne']
    have hmul :
        (1 - sigma) * ‖alg.y k - alg.z k‖ * ‖alg.v k‖ ≤
          ⟪alg.v k, alg.y k - alg.z k⟫_ℝ := by
      have hlam_pos' : 0 < lam k := hlam_pos k
      have hvpos : 0 < ‖alg.v k‖ := hv_norm_pos k
      rw [hu_norm, hinner_eq] at hinner_bound
      field_simp [hlam_pos'.ne'] at hinner_bound
      nlinarith [mul_pos hlam_pos' hvpos]
    rw [htv_eq]
    exact (le_div_iff₀ (hv_norm_pos k)).mpr (by
      simpa [mul_assoc] using hmul)
  have hlam_v_bound (k : ℕ) :
      lam k * ‖alg.v k‖ ≤ ‖alg.y k - alg.z k‖ / (1 - sigma) := by
    set u : H := (lam k)⁻¹ • (alg.y k - alg.z k) with hu_def
    have hv_eq : alg.v k = u + alg.eta k := by
      have heq := alg.equation k
      calc
        alg.v k =
            (lam k)⁻¹ • (alg.y k - alg.z k) +
              ((lam k)⁻¹ • (alg.z k - alg.y k) + alg.v k) := by
          symm
          rw [← add_assoc, ← smul_add]
          simp only [sub_add_sub_cancel, sub_self, smul_zero, zero_add]
        _ = u + alg.eta k := by
          rw [heq]
    have hu_norm : ‖u‖ = ‖alg.y k - alg.z k‖ / lam k := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam_pos k))]
      rw [div_eq_inv_mul]
    have heta_bound : ‖alg.eta k‖ ≤ sigma * max ‖u‖ ‖alg.v k‖ := by
      simpa [hu_norm, norm_sub_rev] using alg.residual_bound k
    rcases lemma_2_1 hsigma hv_eq heta_bound with ⟨hnorm_bound, _hinner_bound⟩
    have hspos : 0 < 1 - sigma := sub_pos.mpr hsigma.2
    have hlam_pos' : 0 < lam k := hlam_pos k
    rw [hu_norm] at hnorm_bound
    have h1 : (1 - sigma) * ‖alg.v k‖ ≤ ‖alg.y k - alg.z k‖ / lam k :=
      (le_div_iff₀' hspos).mp hnorm_bound
    have h2 : ((1 - sigma) * ‖alg.v k‖) * lam k ≤ ‖alg.y k - alg.z k‖ :=
      (le_div_iff₀ hlam_pos').mp h1
    exact (le_div_iff₀ hspos).mpr (by nlinarith [mul_pos hlam_pos' hspos])
  set phi0 : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖alg.x k - xbar0‖ ^ 2 with hphi0_def
  have hphi0_nonneg : ∀ k : ℕ, 0 ≤ phi0 k := by
    intro k
    dsimp [phi0]
    positivity
  set delta_seq0 : ℕ → ℝ :=
    fun k => ((alpha k + alpha k ^ 2) / 2) *
      ‖alg.x k - alg.x (k - 1)‖ ^ 2 with hdelta_seq0_def
  have hdelta0_nonneg : ∀ k : ℕ, 0 ≤ delta_seq0 k := by
    intro k
    dsimp [delta_seq0]
    have ha : 0 ≤ alpha k := (halpha_mem k).1
    positivity
  have hdelta0_sum : Summable delta_seq0 := by
    simpa [delta_seq0] using hdelta_summable
  have hrecurrence0_full (k : ℕ) :
      phi0 (k + 1) ≤
        phi0 k + alpha k * (phi0 k - phi0 (k - 1)) + delta_seq0 k -
          ((rho k)⁻¹ - 1 / 2) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
    have hdescent := descent_ineq_aux k xbar0 hxbar0
    have hinertial := inertial_expansion k xbar0
    dsimp [phi0, delta_seq0]
    nlinarith
  have hrecurrence0 (k : ℕ) :
      phi0 (k + 1) ≤
        phi0 k + alpha k * (phi0 k - phi0 (k - 1)) + delta_seq0 k := by
    have hfull := hrecurrence0_full k
    have hcoeff_nonneg' : 0 ≤ (rho k)⁻¹ - (1 / 2 : ℝ) := by
      have hpos : 0 < rho k := hrho_pos k
      have hlt2 : rho k < 2 := lt_of_le_of_lt (hR2_ge k) hR2_lt
      have hlt_inv : (1 / (2 : ℝ)) < 1 / rho k :=
        one_div_lt_one_div_of_lt hpos hlt2
      have hlt_inv' : (1 / (2 : ℝ)) < (rho k)⁻¹ := by
        simpa [one_div] using hlt_inv
      linarith
    have hnonneg :
        0 ≤ ((rho k)⁻¹ - 1 / 2) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
      exact mul_nonneg (mul_nonneg hcoeff_nonneg' (sq_nonneg (t k)))
        (sq_nonneg ‖alg.v k‖)
    nlinarith
  have hlemma23_0 :=
    lemma_2_3 phi0 delta_seq0 alpha alpha0 hphi0_nonneg hdelta0_nonneg
      hrecurrence0 hdelta0_sum halpha_bound halpha0_lt
  rcases hlemma23_0 with ⟨hsum_pospart0, _hconv_phi0⟩
  set gamma_seq : ℕ → ℝ :=
    fun k : ℕ => ((rho k)⁻¹ - 1 / 2) * (t k) ^ 2 * ‖alg.v k‖ ^ 2 with hgamma_seq_def
  have hgamma_nonneg : ∀ k : ℕ, 0 ≤ gamma_seq k := by
    intro k
    dsimp [gamma_seq]
    have hcoeff_nonneg' : 0 ≤ (rho k)⁻¹ - (1 / 2 : ℝ) := by
      have hpos : 0 < rho k := hrho_pos k
      have hlt2 : rho k < 2 := lt_of_le_of_lt (hR2_ge k) hR2_lt
      have hlt_inv : (1 / (2 : ℝ)) < 1 / rho k :=
        one_div_lt_one_div_of_lt hpos hlt2
      have hlt_inv' : (1 / (2 : ℝ)) < (rho k)⁻¹ := by
        simpa [one_div] using hlt_inv
      linarith
    positivity
  have hsummable_gamma : Summable gamma_seq := by
    have hrecurrence_rearranged (k : ℕ) :
        gamma_seq k ≤
          phi0 k - phi0 (k + 1) + alpha k * (phi0 k - phi0 (k - 1)) +
            delta_seq0 k := by
      dsimp [gamma_seq]
      linarith [hrecurrence0_full k]
    have halpha_theta_bound (k : ℕ) :
        alpha k * (phi0 k - phi0 (k - 1)) ≤
          alpha0 * posPart (phi0 k - phi0 (k - 1)) := by
      set theta := phi0 k - phi0 (k - 1)
      by_cases htheta_nonneg : 0 ≤ theta
      · have hpospart_eq : posPart theta = theta := by
          dsimp [posPart]
          rw [max_eq_left htheta_nonneg]
        have h_alpha_le : alpha k ≤ alpha0 := (halpha_bound k).2
        nlinarith [(halpha_bound k).1]
      · have htheta_nonpos : theta ≤ 0 := le_of_not_ge htheta_nonneg
        have hnonpos : alpha k * theta ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (halpha_bound k).1 htheta_nonpos
        have hpospart_zero : posPart theta = 0 := by
          dsimp [posPart]
          rw [max_eq_right htheta_nonpos]
        have halpha0_nonneg : 0 ≤ alpha0 :=
          le_trans (halpha_bound 0).1 (halpha_bound 0).2
        nlinarith
    have hgamma_bound_partial (n : ℕ) :
        (Finset.range (n + 1)).sum gamma_seq ≤
          (Finset.range (n + 1)).sum (fun k => phi0 k - phi0 (k + 1)) +
          alpha0 * (Finset.range (n + 1)).sum
            (fun k => posPart (phi0 k - phi0 (k - 1))) +
          (Finset.range (n + 1)).sum delta_seq0 := by
      calc
        (Finset.range (n + 1)).sum gamma_seq ≤
            (Finset.range (n + 1)).sum
              (fun k => phi0 k - phi0 (k + 1) +
                alpha k * (phi0 k - phi0 (k - 1)) + delta_seq0 k) := by
          exact Finset.sum_le_sum (fun i _hi => hrecurrence_rearranged i)
        _ = (Finset.range (n + 1)).sum (fun k => phi0 k - phi0 (k + 1)) +
            (Finset.range (n + 1)).sum (fun k => alpha k * (phi0 k - phi0 (k - 1))) +
            (Finset.range (n + 1)).sum delta_seq0 := by
          simp [Finset.sum_add_distrib]
        _ ≤ (Finset.range (n + 1)).sum (fun k => phi0 k - phi0 (k + 1)) +
            (Finset.range (n + 1)).sum
              (fun k => alpha0 * posPart (phi0 k - phi0 (k - 1))) +
            (Finset.range (n + 1)).sum delta_seq0 := by
          have hsum_le :
              (Finset.range (n + 1)).sum
                  (fun k => alpha k * (phi0 k - phi0 (k - 1))) ≤
                (Finset.range (n + 1)).sum
                  (fun k => alpha0 * posPart (phi0 k - phi0 (k - 1))) :=
            Finset.sum_le_sum (fun i _hi => halpha_theta_bound i)
          nlinarith
        _ = (Finset.range (n + 1)).sum (fun k => phi0 k - phi0 (k + 1)) +
            alpha0 * (Finset.range (n + 1)).sum
              (fun k => posPart (phi0 k - phi0 (k - 1))) +
            (Finset.range (n + 1)).sum delta_seq0 := by
          simp [Finset.mul_sum]
    have htelescope (n : ℕ) :
        (Finset.range (n + 1)).sum (fun k : ℕ => phi0 k - phi0 (k + 1)) =
          phi0 0 - phi0 (n + 1) := by
      induction' n with m ih
      · simp
      · rw [Finset.sum_range_succ, ih]
        ring
    have hgamma_bound_total (n : ℕ) :
        (Finset.range (n + 1)).sum gamma_seq ≤
          phi0 0 + alpha0 * ∑' k, posPart (phi0 k - phi0 (k - 1)) +
            ∑' k, delta_seq0 k := by
      have hpartial := hgamma_bound_partial n
      rw [htelescope n] at hpartial
      have hpospart_le :
          (Finset.range (n + 1)).sum
              (fun k => posPart (phi0 k - phi0 (k - 1))) ≤
            ∑' k, posPart (phi0 k - phi0 (k - 1)) :=
        hsum_pospart0.sum_le_tsum (Finset.range (n + 1))
          (fun i _hi => by dsimp [posPart]; exact le_max_right _ _)
      have hdelta_le :
          (Finset.range (n + 1)).sum delta_seq0 ≤ ∑' k, delta_seq0 k :=
        hdelta0_sum.sum_le_tsum (Finset.range (n + 1))
          (fun i _hi => hdelta0_nonneg i)
      have hphi_nonneg' : 0 ≤ phi0 (n + 1) := hphi0_nonneg (n + 1)
      have halpha0_nonneg : 0 ≤ alpha0 :=
        le_trans (halpha_bound 0).1 (halpha_bound 0).2
      nlinarith
    have hbound_for_sum_range_le (n : ℕ) :
        (Finset.range n).sum gamma_seq ≤
          phi0 0 + alpha0 * ∑' k, posPart (phi0 k - phi0 (k - 1)) +
            ∑' k, delta_seq0 k := by
      cases n with
      | zero =>
          have hC_nonneg :
              0 ≤ phi0 0 + alpha0 * ∑' k, posPart (phi0 k - phi0 (k - 1)) +
                ∑' k, delta_seq0 k := by
            have halpha0_nonneg : 0 ≤ alpha0 :=
              le_trans (halpha_bound 0).1 (halpha_bound 0).2
            have hpos_tsum :
                0 ≤ ∑' k, posPart (phi0 k - phi0 (k - 1)) :=
              tsum_nonneg (fun k => by dsimp [posPart]; exact le_max_right _ _)
            have hdelta_tsum : 0 ≤ ∑' k, delta_seq0 k :=
              tsum_nonneg hdelta0_nonneg
            nlinarith [hphi0_nonneg 0]
          simpa using hC_nonneg
      | succ m => simpa using hgamma_bound_total m
    exact summable_of_sum_range_le hgamma_nonneg hbound_for_sum_range_le
  have hsummable_t_sq_v_sq : Summable (fun k : ℕ => (t k) ^ 2 * ‖alg.v k‖ ^ 2) := by
    have hcoeff_uniform_lower : 0 < 1 / R2 - 1 / 2 := by
      have hR2pos : 0 < R2 := lt_of_lt_of_le hR1_pos (le_trans (hR1_le 0) (hR2_ge 0))
      have hlt : 1 / (2 : ℝ) < 1 / R2 := one_div_lt_one_div_of_lt hR2pos hR2_lt
      linarith
    have hcoeff_ge (k : ℕ) : 1 / R2 - 1 / 2 ≤ (rho k)⁻¹ - 1 / 2 := by
      have hR2pos : 0 < R2 := lt_of_lt_of_le hR1_pos (le_trans (hR1_le k) (hR2_ge k))
      have hle : 1 / R2 ≤ 1 / rho k := one_div_le_one_div_of_le (hrho_pos k) (hR2_ge k)
      simpa [one_div] using sub_le_sub_right hle (1 / 2 : ℝ)
    exact Summable.of_nonneg_of_le (fun k => by positivity) (fun k => by
      dsimp [gamma_seq]
      have hnonneg : 0 ≤ (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by positivity
      have hcg := hcoeff_ge k
      have hpos := hcoeff_uniform_lower
      calc
        (t k) ^ 2 * ‖alg.v k‖ ^ 2
            ≤ gamma_seq k / (1 / R2 - 1 / 2) := by
          rw [hgamma_seq_def]
          have hmul :
              (1 / R2 - 1 / 2) * ((t k) ^ 2 * ‖alg.v k‖ ^ 2) ≤
                ((rho k)⁻¹ - 1 / 2) * ((t k) ^ 2 * ‖alg.v k‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hcg hnonneg
          exact (le_div_iff₀ hpos).mpr (by nlinarith [hmul])
      ) (hsummable_gamma.div_const (1 / R2 - 1 / 2))
  have h_tv_tendsto :
      Tendsto (fun k : ℕ => t k * ‖alg.v k‖) atTop (𝓝 0) := by
    have h_sq :
        Tendsto (fun k : ℕ => (t k * ‖alg.v k‖) ^ 2) atTop (𝓝 0) := by
      convert hsummable_t_sq_v_sq.tendsto_atTop_zero using 1
      ext k
      ring
    have h_sqrt :
        Tendsto (fun k : ℕ => Real.sqrt ((t k * ‖alg.v k‖) ^ 2)) atTop
          (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp h_sq
    have h_eq :
        (fun k : ℕ => Real.sqrt ((t k * ‖alg.v k‖) ^ 2)) =
          (fun k : ℕ => t k * ‖alg.v k‖) := by
      funext k
      rw [Real.sqrt_sq]
      exact mul_nonneg (le_of_lt (ht_pos k)) (norm_nonneg _)
    rw [h_eq] at h_sqrt
    simpa [Real.sqrt_zero] using h_sqrt
  have hsummable_yz_sq : Summable (fun k : ℕ => ‖alg.y k - alg.z k‖ ^ 2) := by
    exact Summable.of_nonneg_of_le
      (fun k : ℕ => sq_nonneg ‖alg.y k - alg.z k‖)
      (fun k : ℕ => by
        have hpos : 0 < (1 - sigma) ^ 2 := pow_pos (sub_pos.mpr hsigma.2) 2
        have hineq := hyz_inner_lower k
        have hleft_nonneg : 0 ≤ (1 - sigma) * ‖alg.y k - alg.z k‖ :=
          mul_nonneg (le_of_lt (sub_pos.mpr hsigma.2)) (norm_nonneg _)
        have hsq :
            ((1 - sigma) * ‖alg.y k - alg.z k‖) ^ 2 ≤
              (t k * ‖alg.v k‖) ^ 2 :=
          by simpa [pow_two] using mul_self_le_mul_self hleft_nonneg hineq
        exact (le_div_iff₀ hpos).mpr (by nlinarith [hsq]))
      (hsummable_t_sq_v_sq.div_const ((1 - sigma) ^ 2))
  have hyz_norm_tendsto :
      Tendsto (fun k : ℕ => ‖alg.y k - alg.z k‖) atTop (𝓝 0) := by
    have h_sq :
        Tendsto (fun k : ℕ => ‖alg.y k - alg.z k‖ ^ 2) atTop (𝓝 0) :=
      hsummable_yz_sq.tendsto_atTop_zero
    have h_sqrt :
        Tendsto (fun k : ℕ => Real.sqrt (‖alg.y k - alg.z k‖ ^ 2)) atTop
          (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp h_sq
    have h_eq :
        (fun k : ℕ => Real.sqrt (‖alg.y k - alg.z k‖ ^ 2)) =
          (fun k : ℕ => ‖alg.y k - alg.z k‖) := by
      funext k
      simp
    rw [h_eq] at h_sqrt
    simpa [Real.sqrt_zero] using h_sqrt
  have h_lam_v_sq_summable :
      Summable (fun k : ℕ => (lam k) ^ 2 * ‖alg.v k‖ ^ 2) := by
    exact Summable.of_nonneg_of_le
      (fun k : ℕ => mul_nonneg (sq_nonneg (lam k)) (sq_nonneg ‖alg.v k‖))
      (fun k : ℕ => by
        have hpos : 0 < (1 - sigma) ^ 2 := pow_pos (sub_pos.mpr hsigma.2) 2
        have hineq := hlam_v_bound k
        have hleft_nonneg : 0 ≤ lam k * ‖alg.v k‖ :=
          mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
        have hsq :
            (lam k * ‖alg.v k‖) ^ 2 ≤
              (‖alg.y k - alg.z k‖ / (1 - sigma)) ^ 2 :=
          by simpa [pow_two] using mul_self_le_mul_self hleft_nonneg hineq
        simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq)
      (hsummable_yz_sq.div_const ((1 - sigma) ^ 2))
  have h_lam_v_tendsto :
      Tendsto (fun k : ℕ => lam k * ‖alg.v k‖) atTop (𝓝 0) := by
    have h_sq :
        Tendsto (fun k : ℕ => (lam k) ^ 2 * ‖alg.v k‖ ^ 2) atTop (𝓝 0) :=
      h_lam_v_sq_summable.tendsto_atTop_zero
    have h_sq' :
        Tendsto (fun k : ℕ => (lam k * ‖alg.v k‖) ^ 2) atTop (𝓝 0) := by
      convert h_sq using 1
      ext k
      ring
    have h_sqrt :
        Tendsto (fun k : ℕ => Real.sqrt ((lam k * ‖alg.v k‖) ^ 2)) atTop
          (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp h_sq'
    have h_eq :
        (fun k : ℕ => Real.sqrt ((lam k * ‖alg.v k‖) ^ 2)) =
          (fun k : ℕ => lam k * ‖alg.v k‖) := by
      funext k
      rw [Real.sqrt_sq]
      exact mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
    rw [h_eq] at h_sqrt
    simpa [Real.sqrt_zero] using h_sqrt
  have h_v_norm_tendsto_of_lower :
      ∀ hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k,
        Tendsto (fun k : ℕ => ‖alg.v k‖) atTop (𝓝 0) := by
    intro hlam_lower
    rcases hlam_lower with ⟨lam0, hlam0_pos, hlam_lower'⟩
    have h_bound (k : ℕ) :
        ‖alg.v k‖ ≤ (lam0)⁻¹ * (lam k * ‖alg.v k‖) := by
      have hmul : lam0 * ‖alg.v k‖ ≤ lam k * ‖alg.v k‖ :=
        mul_le_mul_of_nonneg_right (hlam_lower' k) (norm_nonneg _)
      have hdiv := (le_inv_mul_iff₀ hlam0_pos).mpr hmul
      simpa [mul_assoc] using hdiv
    have h_bound_tendsto :
        Tendsto (fun k : ℕ => (lam0)⁻¹ * (lam k * ‖alg.v k‖)) atTop (𝓝 0) := by
      simpa using h_lam_v_tendsto.const_mul (lam0)⁻¹
    exact squeeze_zero (fun _ => norm_nonneg _) h_bound h_bound_tendsto
  set w : ℕ → H :=
    fun k => (rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k with hw_def
  have h_limit_2_5 : Tendsto (fun k : ℕ => ‖alg.x (k + 1) - w k‖) atTop (𝓝 0) := by
    have h_decomp (k : ℕ) :
        alg.x (k + 1) - w k =
          (alg.x (k + 1) - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k) := by
      dsimp [w]
      calc
        alg.x (k + 1) - ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)
            = alg.x (k + 1) +
                ((-(rho k)⁻¹) • alg.z k + (-(1 - (rho k)⁻¹)) • alg.y k) := by
              rw [sub_eq_add_neg, neg_add, ← neg_smul, ← neg_smul]
        _ = (alg.x (k + 1) - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k) := by
              have hcoef : -(1 - (rho k)⁻¹) = (rho k)⁻¹ - 1 := by ring
              rw [hcoef, sub_smul, one_smul]
              simp only [sub_eq_add_neg, smul_add, smul_neg, neg_smul]
              abel
    have h_term1 :
        Tendsto (fun k : ℕ => alg.x (k + 1) - alg.y k) atTop (𝓝 (0 : H)) := by
      have hx_update_all (k : ℕ) :
          alg.x (k + 1) - alg.y k = -(t k) • alg.v k := by
        rw [alg.update_if_nonzero k (hv_nonzero k)]
        rw [ht_def]
        simp only [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_neg,
          neg_smul, add_sub_cancel_left]
        abel_nf
      simp_rw [hx_update_all]
      have h_norm : Tendsto (fun k : ℕ => ‖-(t k) • alg.v k‖) atTop (𝓝 0) := by
        have h_eq :
            (fun k : ℕ => ‖-(t k) • alg.v k‖) =
            (fun k : ℕ => t k * ‖alg.v k‖) := by
          funext k
          calc
            ‖-(t k) • alg.v k‖ = |-(t k)| * ‖alg.v k‖ := by
              rw [norm_smul, Real.norm_eq_abs]
            _ = t k * ‖alg.v k‖ := by
              rw [abs_neg, abs_of_nonneg (le_of_lt (ht_pos k))]
        rw [h_eq]
        exact h_tv_tendsto
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
    have h_term2 :
        Tendsto (fun k : ℕ => (rho k)⁻¹ • (alg.y k - alg.z k)) atTop (𝓝 (0 : H)) := by
      have h_norm_bound (k : ℕ) :
          ‖(rho k)⁻¹ • (alg.y k - alg.z k)‖ ≤
            (R1)⁻¹ * ‖alg.y k - alg.z k‖ := by
        have h_inv_le : (rho k)⁻¹ ≤ (R1)⁻¹ :=
          by simpa [one_div] using
            (one_div_le_one_div (hrho_pos k) hR1_pos).mpr (hR1_le k)
        calc
          ‖(rho k)⁻¹ • (alg.y k - alg.z k)‖ =
              (rho k)⁻¹ * ‖alg.y k - alg.z k‖ := by
                rw [norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hrho_pos k)))]
          _ ≤ (R1)⁻¹ * ‖alg.y k - alg.z k‖ :=
              mul_le_mul_of_nonneg_right h_inv_le (norm_nonneg _)
      have h_norm_squeeze :
          Tendsto (fun k : ℕ => ‖(rho k)⁻¹ • (alg.y k - alg.z k)‖) atTop (𝓝 0) :=
        squeeze_zero (fun _ => norm_nonneg _) h_norm_bound
          (by simpa using hyz_norm_tendsto.const_mul (R1)⁻¹)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_squeeze
    have h_sum :
        Tendsto
          (fun k : ℕ => (alg.x (k + 1) - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k))
          atTop (𝓝 (0 : H)) :=
      by simpa using h_term1.add h_term2
    have h_norm_sum :
        Tendsto
          (fun k : ℕ =>
            ‖(alg.x (k + 1) - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k)‖)
          atTop (𝓝 0) := by
      simpa using h_sum.norm
    simpa [h_decomp] using h_norm_sum
  constructor
  · exact ⟨h_dist_all, by simpa [w] using h_limit_2_5⟩
  · intro hlam_lower
    have h_v_norm_tendsto := h_v_norm_tendsto_of_lower hlam_lower
    have h_weak_cluster_condition :
        ∀ (xhat : H) (subseq : ℕ → ℕ), StrictMono subseq →
          Tendsto (fun j : ℕ => toWeakSpace ℝ H (alg.x (subseq j))) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) →
          xhat ∈ SetValuedOperator.zeros A := by
      have hcont_toWeak : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
        simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
      have hx_diff_tendsto :
          Tendsto (fun k : ℕ => alg.x (k + 1) - alg.x k) atTop (𝓝 (0 : H)) := by
        have h_alpha_sq_tendsto :
            Tendsto (fun k : ℕ => alpha k * ‖alg.x k - alg.x (k - 1)‖ ^ 2)
              atTop (𝓝 0) :=
          halpha_summable.tendsto_atTop_zero
        have h_alpha_norm_tendsto :
            Tendsto (fun k : ℕ => alpha k * ‖alg.x k - alg.x (k - 1)‖) atTop
              (𝓝 0) := by
          have h_sq_tendsto :
              Tendsto (fun k : ℕ => (alpha k * ‖alg.x k - alg.x (k - 1)‖) ^ 2)
                atTop (𝓝 0) := by
            refine squeeze_zero (fun k => sq_nonneg _) ?_ h_alpha_sq_tendsto
            intro k
            have ha0 : 0 ≤ alpha k := (halpha_mem k).1
            have ha1 : alpha k ≤ 1 := le_of_lt (halpha_mem k).2
            have hn : 0 ≤ ‖alg.x k - alg.x (k - 1)‖ := norm_nonneg _
            nlinarith [mul_le_mul_of_nonneg_left ha1 ha0]
          have h_sqrt :
              Tendsto
                (fun k : ℕ => Real.sqrt ((alpha k * ‖alg.x k - alg.x (k - 1)‖) ^ 2))
                atTop (𝓝 (Real.sqrt 0)) :=
            Real.continuous_sqrt.continuousAt.tendsto.comp h_sq_tendsto
          have h_eq :
              (fun k : ℕ =>
                  Real.sqrt ((alpha k * ‖alg.x k - alg.x (k - 1)‖) ^ 2)) =
                (fun k : ℕ => alpha k * ‖alg.x k - alg.x (k - 1)‖) := by
            funext k
            rw [Real.sqrt_sq]
            exact mul_nonneg (halpha_mem k).1 (norm_nonneg _)
          rw [h_eq] at h_sqrt
          simpa [Real.sqrt_zero] using h_sqrt
        have hx_next_minus_y :
            Tendsto (fun k : ℕ => alg.x (k + 1) - alg.y k) atTop (𝓝 (0 : H)) := by
          have hx_update (k : ℕ) : alg.x (k + 1) - alg.y k = -(t k) • alg.v k := by
            rw [alg.update_if_nonzero k (hv_nonzero k)]
            rw [ht_def]
            simp only [add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_neg,
              neg_smul, add_sub_cancel_left]
            abel_nf
          simp_rw [hx_update]
          have h_norm : Tendsto (fun k : ℕ => ‖-(t k) • alg.v k‖) atTop (𝓝 0) := by
            have h_eq :
                (fun k : ℕ => ‖-(t k) • alg.v k‖) =
                  (fun k : ℕ => t k * ‖alg.v k‖) := by
              funext k
              calc
                ‖-(t k) • alg.v k‖ = |-(t k)| * ‖alg.v k‖ := by
                  rw [norm_smul, Real.norm_eq_abs]
                _ = t k * ‖alg.v k‖ := by
                  rw [abs_neg, abs_of_nonneg (le_of_lt (ht_pos k))]
            rw [h_eq]
            exact h_tv_tendsto
          exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
        have h_inertial :
            Tendsto (fun k : ℕ => alpha k • (alg.x k - alg.x (k - 1))) atTop
              (𝓝 (0 : H)) := by
          have h_norm :
              Tendsto (fun k : ℕ => ‖alpha k • (alg.x k - alg.x (k - 1))‖) atTop
                (𝓝 0) := by
            have h_eq :
                (fun k : ℕ => ‖alpha k • (alg.x k - alg.x (k - 1))‖) =
                  (fun k : ℕ => alpha k * ‖alg.x k - alg.x (k - 1)‖) := by
              funext k
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (halpha_mem k).1]
            rw [h_eq]
            exact h_alpha_norm_tendsto
          exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
        have hx_decomp (k : ℕ) :
            alg.x (k + 1) - alg.x k =
              (alg.x (k + 1) - alg.y k) + alpha k • (alg.x k - alg.x (k - 1)) := by
          rw [alg.y_def k]
          simp only [smul_sub, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
            add_sub_cancel_left]
          abel_nf
        simp_rw [hx_decomp]
        simpa using hx_next_minus_y.add h_inertial
      intro xhat subseq hstrict hweak_subseq
      have hsubseq_atTop : Tendsto subseq atTop atTop := hstrict.tendsto_atTop
      have hx_next_weak :
          Tendsto (fun j : ℕ => toWeakSpace ℝ H (alg.x (subseq j + 1))) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) := by
        have hdiff :
            Tendsto (fun j : ℕ => alg.x (subseq j + 1) - alg.x (subseq j)) atTop
              (𝓝 (0 : H)) :=
          hx_diff_tendsto.comp hsubseq_atTop
        have hdiff_weak :
            Tendsto
              (fun j : ℕ => toWeakSpace ℝ H (alg.x (subseq j + 1) - alg.x (subseq j)))
              atTop (𝓝 (toWeakSpace ℝ H (0 : H))) :=
          (hcont_toWeak.tendsto (0 : H)).comp hdiff
        have hsum := hweak_subseq.add hdiff_weak
        have h_eq :
            (fun j : ℕ =>
                toWeakSpace ℝ H (alg.x (subseq j)) +
                  toWeakSpace ℝ H (alg.x (subseq j + 1) - alg.x (subseq j))) =
              (fun j : ℕ => toWeakSpace ℝ H (alg.x (subseq j + 1))) := by
          funext j
          simp
        rw [h_eq] at hsum
        simpa using hsum
      have hw_weak :
          Tendsto (fun j : ℕ => toWeakSpace ℝ H (w (subseq j))) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) := by
        have hlimit_vec :
            Tendsto (fun j : ℕ => alg.x (subseq j + 1) - w (subseq j)) atTop
              (𝓝 (0 : H)) := by
          exact (tendsto_zero_iff_norm_tendsto_zero).mpr
            (h_limit_2_5.comp hsubseq_atTop)
        have hlimit_weak :
            Tendsto
              (fun j : ℕ => toWeakSpace ℝ H (alg.x (subseq j + 1) - w (subseq j)))
              atTop (𝓝 (toWeakSpace ℝ H (0 : H))) :=
          (hcont_toWeak.tendsto (0 : H)).comp hlimit_vec
        have hsub := hx_next_weak.sub hlimit_weak
        have h_eq :
            (fun j : ℕ =>
                toWeakSpace ℝ H (alg.x (subseq j + 1)) -
                  toWeakSpace ℝ H (alg.x (subseq j + 1) - w (subseq j))) =
              (fun j : ℕ => toWeakSpace ℝ H (w (subseq j))) := by
          funext j
          simp
        rw [h_eq] at hsub
        simpa using hsub
      have hv_scaled_tendsto :
          Tendsto (fun j : ℕ => (rho (subseq j))⁻¹ • alg.v (subseq j)) atTop
            (𝓝 (0 : H)) := by
        have hnorm_bound (j : ℕ) :
            ‖(rho (subseq j))⁻¹ • alg.v (subseq j)‖ ≤
              R1⁻¹ * ‖alg.v (subseq j)‖ := by
          have hρ_pos : 0 < rho (subseq j) := hrho_pos (subseq j)
          have h_abs_inv : |(rho (subseq j))⁻¹| ≤ R1⁻¹ := by
            rw [abs_of_pos (inv_pos.mpr hρ_pos)]
            exact (inv_le_inv₀ hρ_pos hR1_pos).mpr (hR1_le (subseq j))
          calc
            ‖(rho (subseq j))⁻¹ • alg.v (subseq j)‖ =
                |(rho (subseq j))⁻¹| * ‖alg.v (subseq j)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
            _ ≤ R1⁻¹ * ‖alg.v (subseq j)‖ :=
              mul_le_mul_of_nonneg_right h_abs_inv (norm_nonneg _)
        have hnorm_tendsto :
            Tendsto
              (fun j : ℕ => ‖(rho (subseq j))⁻¹ • alg.v (subseq j)‖) atTop
              (𝓝 0) := by
          have hprod :
              Tendsto (fun j : ℕ => R1⁻¹ * ‖alg.v (subseq j)‖) atTop (𝓝 0) := by
            simpa using (h_v_norm_tendsto.comp hsubseq_atTop).const_mul R1⁻¹
          exact squeeze_zero (fun j => norm_nonneg _) hnorm_bound hprod
        exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
      rw [SetValuedOperator.mem_zeros_iff]
      exact weak_strong_closedness_maximal_monotone_graph A hA hw_weak hv_scaled_tendsto
        (fun j => by simpa [w] using scaled_step_inclusion (subseq j))
    have h_weak_conv : ∃ xstar ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xstar)) :=
      lemma_2_4_opial alg.x (SetValuedOperator.zeros A) hS_nonempty h_dist_all h_weak_cluster_condition
    exact ⟨h_v_norm_tendsto, h_weak_conv⟩
  
private theorem zero_step_solution
    {A : SetValuedOperator H H} {lam alpha rho : ℕ → ℝ}
    (sigma : ℝ) (hsigma_lt : sigma < 1)
    (alg : RelaxedInertialHPPA A lam alpha rho sigma)
    (params : ParameterAssumptionsPartI alg.x)
    (hlam_eq : lam = params.lam) (hrho_eq : rho = params.rho)
    (k : ℕ) (hv : alg.v k = 0) : alg.y k ∈ SetValuedOperator.zeros A := by
  have hlam_pos : 0 < lam k := by
    simpa [hlam_eq] using params.lam_pos k
  have hrho_lower : ∃ R1 : ℝ, 0 < R1 ∧ ∀ n : ℕ, R1 ≤ rho n := by
    rcases params.rho_lower with ⟨R1, hpos, hlow⟩
    refine ⟨R1, hpos, ?_⟩
    intro n
    simpa [hrho_eq] using hlow n
  obtain ⟨R1, hR1_pos, hR1_le⟩ := hrho_lower
  have hrho_pos : 0 < rho k := lt_of_lt_of_le hR1_pos (hR1_le k)
  have hrho_ne : rho k ≠ 0 := ne_of_gt hrho_pos
  rcases alg.step_inclusion k with ⟨a, ha, ha_eq⟩
  have ha_eq' : alg.v k = rho k • a := by simpa using ha_eq.symm
  have ha_zero : a = 0 := by
    have hscaled : (rho k)⁻¹ • alg.v k = a := by
      rw [ha_eq', inv_smul_smul₀ hrho_ne]
    simpa [hv] using hscaled.symm
  have heta_eq : (lam k)⁻¹ • (alg.z k - alg.y k) = alg.eta k := by
    simpa [hv] using alg.equation k
  have heta_norm : ‖alg.eta k‖ = ‖alg.z k - alg.y k‖ / lam k := by
    rw [← heta_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam_pos)]
    simp [div_eq_mul_inv, mul_comm]
  have hres := alg.residual_bound k
  rw [heta_norm] at hres
  have hquot_nonneg : 0 ≤ ‖alg.z k - alg.y k‖ / lam k :=
    div_nonneg (norm_nonneg _) (le_of_lt hlam_pos)
  have hres' : ‖alg.z k - alg.y k‖ / lam k ≤
      sigma * (‖alg.z k - alg.y k‖ / lam k) := by
    simpa [max_eq_left hquot_nonneg, hv] using hres
  have hquot_zero : ‖alg.z k - alg.y k‖ / lam k = 0 := by
    nlinarith
  have hdiff_norm : ‖alg.z k - alg.y k‖ = 0 := by
    rcases (div_eq_zero_iff).mp hquot_zero with hzero | hzero
    · exact hzero
    · exact False.elim (ne_of_gt hlam_pos hzero)
  have hzy : alg.z k = alg.y k := sub_eq_zero.mp (norm_eq_zero.mp hdiff_norm)
  have hw : (rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k = alg.y k := by
    rw [hzy]
    module
  rw [SetValuedOperator.mem_zeros_iff]
  simpa [ha_zero, hw] using ha

/-- Theorem 2.2: convergence properties of the relaxed inertial HPPA. -/
theorem theorem_2_2
    {lam alpha rho : ℕ → ℝ}
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alpha rho sigma)
    (params : ParameterAssumptions alg.x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    (∀ xbar ∈ SetValuedOperator.zeros A,
      ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l)) ∧
    Tendsto
      (fun k : ℕ ↦
        ‖alg.x (k + 1) -
          ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)‖)
      atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ ↦ ‖alg.v k‖) atTop (𝓝 0) ∧
    ∃ xstar ∈ SetValuedOperator.zeros A,
      Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar)) := by
  classical
  by_cases hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0
  · have hlam_lower_alg : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k := by
      rcases params.lam_lower with ⟨lam0, hpos, hlow⟩
      refine ⟨lam0, hpos, ?_⟩
      intro k
      simpa [hlam_eq] using hlow k
    have hcore := theorem_2_2_nonterminating A hA sigma hsigma alg hv_nonzero params.partI
      hlam_eq halpha_eq hrho_eq hS
    rcases hcore with ⟨hpart_i, hpart_ii⟩
    rcases hpart_ii hlam_lower_alg with ⟨hv_tendsto, hweak_conv⟩
    exact ⟨hpart_i.1, hpart_i.2, hv_tendsto, hweak_conv⟩
  · push Not at hv_nonzero
    rcases hv_nonzero with ⟨K, hvK⟩
    have hyK_zero : alg.y K ∈ SetValuedOperator.zeros A :=
      zero_step_solution sigma hsigma.2 alg params.partI hlam_eq hrho_eq K hvK
    have htail := alg.finite_stop_if_zero K hvK
    have h_dist_all : ∀ xbar ∈ SetValuedOperator.zeros A,
        ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l) := by
      intro xbar _hxbar
      refine ⟨‖alg.y K - xbar‖, ?_⟩
      exact (tendsto_congr' (Filter.eventually_atTop.mpr
        ⟨K + 1, fun n hn => by simp [(htail n hn).1]⟩)).2 tendsto_const_nhds
    have h_limit_2_5 :
        Tendsto
          (fun k : ℕ ↦
            ‖alg.x (k + 1) -
              ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)‖)
          atTop (𝓝 0) := by
      exact (tendsto_congr' (Filter.eventually_atTop.mpr ⟨K + 1, by
        intro n hn
        have hn' : K + 1 ≤ n + 1 := le_trans hn (Nat.le_succ n)
        rcases htail n hn with ⟨_hxn, hyn, hzn, _hvn⟩
        have hxn1 := (htail (n + 1) hn').1
        simp [hxn1, hyn, hzn]⟩)).2 tendsto_const_nhds
    have h_v_norm_tendsto : Tendsto (fun k : ℕ ↦ ‖alg.v k‖) atTop (𝓝 0) := by
      exact (tendsto_congr' (Filter.eventually_atTop.mpr
        ⟨K + 1, fun n hn => by simp [(htail n hn).2.2.2]⟩)).2 tendsto_const_nhds
    have h_weak_conv : ∃ xstar ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xstar)) := by
      refine ⟨alg.y K, hyK_zero, ?_⟩
      exact (tendsto_congr' (Filter.eventually_atTop.mpr
        ⟨K + 1, fun n hn => by simp [(htail n hn).1]⟩)).2 tendsto_const_nhds
    exact ⟨h_dist_all, h_limit_2_5, h_v_norm_tendsto, h_weak_conv⟩

/-! The part of Theorem 2.2 that uses only assumptions (1.4)-(1.6). -/
theorem theorem_2_2_part_i
    {lam alpha rho : ℕ → ℝ}
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alpha rho sigma)
    (params : ParameterAssumptionsPartI alg.x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    (∀ xbar ∈ SetValuedOperator.zeros A,
      ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l)) ∧
    Tendsto
      (fun k : ℕ ↦
        ‖alg.x (k + 1) -
          ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)‖)
      atTop (𝓝 0) := by
  classical
  by_cases hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0
  · exact (theorem_2_2_nonterminating A hA sigma hsigma alg hv_nonzero params
      hlam_eq halpha_eq hrho_eq hS).1
  · push Not at hv_nonzero
    rcases hv_nonzero with ⟨K, hvK⟩
    have hyK_zero : alg.y K ∈ SetValuedOperator.zeros A :=
      zero_step_solution sigma hsigma.2 alg params hlam_eq hrho_eq K hvK
    have htail := alg.finite_stop_if_zero K hvK
    have h_dist_all : ∀ xbar ∈ SetValuedOperator.zeros A,
        ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖alg.x k - xbar‖) atTop (𝓝 l) := by
      intro xbar _hxbar
      refine ⟨‖alg.y K - xbar‖, ?_⟩
      exact (tendsto_congr' (Filter.eventually_atTop.mpr
        ⟨K + 1, fun n hn => by simp [(htail n hn).1]⟩)).2 tendsto_const_nhds
    have h_limit_2_5 :
        Tendsto
          (fun k : ℕ ↦
            ‖alg.x (k + 1) -
              ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)‖)
          atTop (𝓝 0) := by
      exact (tendsto_congr' (Filter.eventually_atTop.mpr ⟨K + 1, by
        intro n hn
        have hn' : K + 1 ≤ n + 1 := le_trans hn (Nat.le_succ n)
        rcases htail n hn with ⟨_hxn, hyn, hzn, _hvn⟩
        have hxn1 := (htail (n + 1) hn').1
        simp [hxn1, hyn, hzn]⟩)).2 tendsto_const_nhds
    exact ⟨h_dist_all, h_limit_2_5⟩

/-- The part of Theorem 2.2(ii) that additionally uses the uniform lower bound
on the regularization parameters from (1.3). -/
theorem theorem_2_2_part_ii
    {lam alpha rho : ℕ → ℝ}
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alpha rho sigma)
    (params : ParameterAssumptions alg.x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    Tendsto (fun k : ℕ ↦ ‖alg.v k‖) atTop (𝓝 0) ∧
    ∃ xstar ∈ SetValuedOperator.zeros A,
      Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar)) := by
  rcases theorem_2_2 A hA sigma hsigma alg params hlam_eq halpha_eq hrho_eq hS with
    ⟨_, _, hv_tendsto, hweak_conv⟩
  exact ⟨hv_tendsto, hweak_conv⟩

end Alvarez2004
