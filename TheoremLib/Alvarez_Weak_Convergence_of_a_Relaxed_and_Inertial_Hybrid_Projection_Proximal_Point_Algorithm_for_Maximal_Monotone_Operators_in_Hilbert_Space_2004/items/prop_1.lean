import Mathlib.Tactic
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.thm_1

/-!
# Proposition 2.5
-/

open SetValuedOperator
open Filter
open scoped Topology InnerProductSpace

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The coefficient `p(α)` from (2.15). -/
noncomputable def pCoeff (R1 R2 alpha : ℝ) : ℝ :=
  1 / R2 - 1 / 2 - (2 / R1 - 1 / 2) * alpha - (1 - 1 / R2) * alpha ^ 2

omit [CompleteSpace H] in
private theorem prop_2_5_quadratic_lower_bound
    (a b : H) (α : ℝ) (hα0 : 0 ≤ α) :
    (1 - α) * ‖a‖ ^ 2 - α * (1 - α) * ‖b‖ ^ 2 ≤ ‖a - α • b‖ ^ 2 := by
  have hinner_le : 2 * ⟪a, b⟫_ℝ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have hsq : 0 ≤ ‖a - b‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at hsq
    nlinarith [real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq b]
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0]
  nlinarith [mul_le_mul_of_nonneg_left hinner_le hα0, sq_nonneg α, sq_nonneg ‖b‖]

private theorem prop_2_5_mu_coeff_nonneg (a r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 < r) :
    0 ≤ a * (r⁻¹ + (1 - r⁻¹) * a) := by
  have hinv_nonneg : 0 ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have htail : 0 ≤ (1 - a) * r⁻¹ := mul_nonneg (sub_nonneg.mpr ha1) hinv_nonneg
  have hrewrite : r⁻¹ + (1 - r⁻¹) * a = a + (1 - a) * r⁻¹ := by
    ring
  rw [hrewrite]
  exact mul_nonneg ha0 (add_nonneg ha0 htail)

set_option maxHeartbeats 800000 in
private theorem prop_2_5_coeff_bound (a b A u v s t : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (haA : a ≤ A)
    (hba : b ≤ a) (hAlt : A < 1)
    (hsu : t ≤ u) (hsv : v ≤ s)
    (huv : v ≤ u) (hvhalf : (1 / 2 : ℝ) < v)
    (hp : 0 < v - 1 / 2 - (2 * u - 1 / 2) * A - (1 - v) * A ^ 2) :
    a * (t + (1 - t) * a) + (s - 1 / 2) * (b - 1) ≤
      -(v - 1 / 2 - (2 * u - 1 / 2) * A - (1 - v) * A ^ 2) := by
  have hterm_a_bound : a * (t + (1 - t) * a) ≤ a ^ 2 + a * (1 - a) * u := by
    have h_eq : a * (t + (1 - t) * a) = a ^ 2 + a * (1 - a) * t := by ring
    rw [h_eq]
    have hnon : 0 ≤ a * (1 - a) := by nlinarith
    nlinarith
  have hterm_b_bound : (s - 1 / 2) * (b - 1) ≤ (v - 1 / 2) * (a - 1) := by
    have hs_half_nonneg : 0 ≤ s - 1 / 2 := by nlinarith
    have hdiffsv : 0 ≤ (s - 1 / 2) - (v - 1 / 2) := by nlinarith
    have ha_minus_nonpos : a - 1 ≤ 0 := by nlinarith
    have hdiff : (s - 1 / 2) * (b - 1) - (v - 1 / 2) * (a - 1) ≤ 0 := by
      have h_eq : (s - 1 / 2) * (b - 1) - (v - 1 / 2) * (a - 1) =
          (s - 1 / 2) * ((b - 1) - (a - 1)) +
            ((s - 1 / 2) - (v - 1 / 2)) * (a - 1) := by
        ring
      rw [h_eq]
      have h1 : (s - 1 / 2) * ((b - 1) - (a - 1)) ≤ 0 := by nlinarith
      have h2 : ((s - 1 / 2) - (v - 1 / 2)) * (a - 1) ≤ 0 := by nlinarith
      nlinarith
    linarith
  have hG_endpoint : A ^ 2 + A * (1 - A) * u + (v - 1 / 2) * (A - 1) ≤
      -(v - 1 / 2 - (2 * u - 1 / 2) * A - (1 - v) * A ^ 2) := by
    have hnon : 0 ≤ A * (A + 1) * (u - v) := by nlinarith
    nlinarith
  have hG_mono : a ^ 2 + a * (1 - a) * u + (v - 1 / 2) * (a - 1) ≤
      A ^ 2 + A * (1 - A) * u + (v - 1 / 2) * (A - 1) := by
    have hdiff_eq : A ^ 2 + A * (1 - A) * u + (v - 1 / 2) * (A - 1) -
        (a ^ 2 + a * (1 - a) * u + (v - 1 / 2) * (a - 1)) =
        (A - a) * ((A + a) * (1 - u) + u + v - 1 / 2) := by
      ring
    have hA_minus_nonneg : 0 ≤ A - a := by nlinarith
    have hbracket_nonneg : 0 ≤ (A + a) * (1 - u) + u + v - 1 / 2 := by
      by_cases hu_le_one : u ≤ 1
      · have hcoef : 0 ≤ 1 - u := by linarith
        have hsum : 0 ≤ A + a := by linarith
        have hterm : 0 ≤ (A + a) * (1 - u) := mul_nonneg hsum hcoef
        nlinarith
      · have hu_gt_one : 1 < u := lt_of_not_ge hu_le_one
        have hlower : 2 * A * (1 - u) + u + v - 1 / 2 ≤
            (A + a) * (1 - u) + u + v - 1 / 2 := by
          nlinarith
        have hD_pos : 0 < 2 * A * (1 - u) + u + v - 1 / 2 := by
          have h_eq : 2 * A * (1 - u) + u + v - 1 / 2 =
              (v - 1 / 2 - (2 * u - 1 / 2) * A - (1 - v) * A ^ 2) +
                (3 / 2) * A + u + A ^ 2 * (1 - v) := by
            ring
          rw [h_eq]
          have hextra_nonneg : 0 ≤ (3 / 2) * A + u + A ^ 2 * (1 - v) := by
            by_cases hv_le_one : v ≤ 1
            · have h3 : 0 ≤ A ^ 2 * (1 - v) :=
                mul_nonneg (sq_nonneg A) (by linarith)
              nlinarith
            · have hv_gt_one : 1 < v := lt_of_not_ge hv_le_one
              have hA2_lt_one : A ^ 2 < 1 := by nlinarith [sq_nonneg A]
              have hpos : 0 < u + A ^ 2 * (1 - v) := by nlinarith
              nlinarith
          nlinarith
        linarith
    nlinarith [hdiff_eq]
  nlinarith

set_option maxHeartbeats 1200000 in
/-- Nonterminating branch of Proposition 2.5. -/
private theorem proposition_2_5_nonterminating
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alphaSeq rho sigma)
    (hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0)
    (hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alphaSeq k ∧ alphaSeq k < 1)
    (halpha_mono : ∀ k : ℕ, alphaSeq k ≤ alphaSeq (k + 1))
    (hp_pos_alphaBar_R1_R2 : 0 < pCoeff R1 R2 alphaBar)
    (halphaBar_lt_one : alphaBar < 1)
    (halphaBar_bound : ∀ k : ℕ, alphaSeq k ≤ alphaBar)
    (hR1_pos : 0 < R1) (hR1_le : ∀ k : ℕ, R1 ≤ rho k)
    (hR2_lt_two : R2 < 2) (hR2_ge : ∀ k : ℕ, rho k ≤ R2)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) ∧
      ∃ xhat ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
  suffices hsummable_sq :
      Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) by
    have halpha_summable :
        Summable fun k : ℕ ↦ alphaSeq k * ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
      refine hsummable_sq.of_nonneg_of_le ?hnonneg ?hle
      · intro k
        exact mul_nonneg (halpha_mem k).1 (sq_nonneg _)
      · intro k
        have ha_le_one : alphaSeq k ≤ 1 := le_of_lt (halpha_mem k).2
        exact mul_le_of_le_one_left (sq_nonneg _) ha_le_one
    let params : ParameterAssumptions alg.x :=
      { lam := lam
        alpha := alphaSeq
        rho := rho
        lam_lower := hlam_lower
        alpha_mem := halpha_mem
        alpha_upper := ⟨alphaBar, halphaBar_lt_one, halphaBar_bound⟩
        alpha_summable := halpha_summable
        rho_lower := ⟨R1, hR1_pos, hR1_le⟩
        rho_upper := ⟨R2, hR2_lt_two, hR2_ge⟩ }
    have hweak :
        ∃ xhat ∈ SetValuedOperator.zeros A,
          Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) := by
      rcases theorem_2_2 A hA sigma hsigma alg params rfl rfl rfl hS with
        ⟨_, _, _, hweak⟩
      exact hweak
    exact ⟨hsummable_sq, hweak⟩
  have hrho_pos (k : ℕ) : 0 < rho k := lt_of_lt_of_le hR1_pos (hR1_le k)
  obtain ⟨xbar, hxbar⟩ := hS
  let phi : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖alg.x k - xbar‖ ^ 2
  let mu : ℕ → ℝ := fun k =>
    phi k - alphaSeq k * phi (k - 1) +
      alphaSeq k * ((rho k)⁻¹ + (1 - (rho k)⁻¹) * alphaSeq k) *
        ‖alg.x k - alg.x (k - 1)‖ ^ 2
  have hmu_coeff_nonneg (k : ℕ) :
      0 ≤ alphaSeq k * ((rho k)⁻¹ + (1 - (rho k)⁻¹) * alphaSeq k) := by
    exact prop_2_5_mu_coeff_nonneg (alphaSeq k) (rho k)
      (halpha_mem k).1 (le_of_lt (halpha_mem k).2) (hrho_pos k)
  have hlam_pos (k : ℕ) : 0 < lam k := by
    rcases hlam_lower with ⟨lam0, hpos, hlow⟩
    exact lt_of_lt_of_le hpos (hlow k)
  have hrho_ne_zero (k : ℕ) : rho k ≠ 0 := (hrho_pos k).ne'
  have hv_norm_pos (k : ℕ) : 0 < ‖alg.v k‖ := norm_pos_iff.mpr (hv_nonzero k)
  have hinner_norm_sq_diff_eq (a b : H) :
      ‖a‖ ^ 2 - ‖b‖ ^ 2 = 2 * ⟪a, a - b⟫_ℝ - ‖a - b‖ ^ 2 := by
    rw [norm_sub_sq_real]
    have hself : ⟪a, a⟫_ℝ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    rw [inner_sub_right, hself]
    ring
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
      rw [show alg.y k - alg.z k = -(alg.z k - alg.y k) by abel_nf, norm_smul, norm_neg]
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
      abel_nf
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
      calc
        xbar - ((rho k)⁻¹ • alg.z k + (1 - (rho k)⁻¹) • alg.y k)
            = xbar + ((-(rho k)⁻¹) • alg.z k + (-(1 - (rho k)⁻¹)) • alg.y k) := by
              rw [sub_eq_add_neg, neg_add, ← neg_smul, ← neg_smul]
        _ = (xbar - alg.y k) + (rho k)⁻¹ • (alg.y k - alg.z k) := by
              have hcoef : -(1 - (rho k)⁻¹) = (rho k)⁻¹ - 1 := by ring
              rw [hcoef, sub_smul, one_smul]
              simp only [sub_eq_add_neg, smul_add, smul_neg, neg_smul]
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
        abel_nf
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
            abel_nf
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
          alphaSeq k * (‖alg.x k - xbar‖ ^ 2 -
            ‖alg.x (k - 1) - xbar‖ ^ 2) +
          (alphaSeq k + (alphaSeq k) ^ 2) *
            ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
    have hy := alg.y_def k
    rw [hy]
    set a : H := alg.x k - xbar
    set d : H := alg.x k - alg.x (k - 1)
    have hsub : alg.x (k - 1) - xbar = a - d := by
      dsimp [a, d]
      abel_nf
    have hnorm :
        ‖a + alphaSeq k • d‖ ^ 2 =
          ‖a‖ ^ 2 + 2 * alphaSeq k * ⟪a, d⟫_ℝ +
            (alphaSeq k) ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_add_sq_real]
      simp [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (halpha_mem k).1, pow_two]
      ring
    have hinner :
        2 * ⟪a, d⟫_ℝ =
          ‖a‖ ^ 2 - ‖a - d‖ ^ 2 + ‖d‖ ^ 2 := by
      have h := hinner_norm_sq_diff_eq a (a - d)
      have hd : a - (a - d) = d := by abel_nf
      rw [hd] at h
      linarith
    have hy_rewrite :
        alg.x k + alphaSeq k • (alg.x k - alg.x (k - 1)) - xbar =
          a + alphaSeq k • d := by
      dsimp [a, d]
      abel_nf
    rw [hy_rewrite, hnorm, hsub]
    rw [show 2 * alphaSeq k * ⟪a, d⟫_ℝ =
        alphaSeq k * (2 * ⟪a, d⟫_ℝ) by ring, hinner]
    ring
  have hineq_27 (k : ℕ) :
      phi (k + 1) ≤ (1 / 2 : ℝ) * ‖alg.y k - xbar‖ ^ 2 -
        ((rho k)⁻¹ - 1 / 2) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
    have hdescent := descent_ineq_aux k xbar hxbar
    have hstep_norm_sq :
        ‖alg.x (k + 1) - alg.y k‖ ^ 2 = (t k) ^ 2 * ‖alg.v k‖ ^ 2 := by
      have hupdate : alg.x (k + 1) - alg.y k = -(t k) • alg.v k := by
        rw [alg.update_if_nonzero k (hv_nonzero k)]
        rw [ht_def]
        simp only [add_comm, add_left_comm, sub_eq_add_neg, neg_smul]
        abel_nf
      rw [hupdate]
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (ht_pos k)), sq]
      ring
    calc
      phi (k + 1)
          = (1 / 2 : ℝ) * ‖alg.x (k + 1) - xbar‖ ^ 2 := rfl
      _ ≤ (1 / 2 : ℝ) *
            (‖alg.y k - xbar‖ ^ 2 -
              (((rho k)⁻¹ * 2) - 1) * (t k) ^ 2 * ‖alg.v k‖ ^ 2) := by
            nlinarith
      _ = (1 / 2 : ℝ) * ‖alg.y k - xbar‖ ^ 2 -
            ((rho k)⁻¹ - 1 / 2) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
            rw [hstep_norm_sq]
            ring
  have hexpand_y (k : ℕ) :
      (1 / 2 : ℝ) * ‖alg.y k - xbar‖ ^ 2 =
        phi k + alphaSeq k * (phi k - phi (k - 1)) +
          ((alphaSeq k + (alphaSeq k) ^ 2) / 2) *
            ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
    have h := inertial_expansion k xbar
    dsimp [phi]
    nlinarith
  have hineq_29 (k : ℕ) :
      phi (k + 1) ≤ phi k + alphaSeq k * (phi k - phi (k - 1))
        + ((alphaSeq k + (alphaSeq k) ^ 2) / 2) *
          ‖alg.x k - alg.x (k - 1)‖ ^ 2
        - ((rho k)⁻¹ - 1 / 2) * ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
    have h27 := hineq_27 k
    have h28 := hexpand_y k
    linarith
  have hquad_lower (k : ℕ) :
      (1 - alphaSeq k) * ‖alg.x (k + 1) - alg.x k‖ ^ 2 -
          alphaSeq k * (1 - alphaSeq k) *
            ‖alg.x k - alg.x (k - 1)‖ ^ 2 ≤
        ‖alg.x (k + 1) - alg.y k‖ ^ 2 := by
    have hy_def : alg.y k = alg.x k + alphaSeq k • (alg.x k - alg.x (k - 1)) := by
      rw [alg.y_def k]
    have htarget :
        alg.x (k + 1) - alg.y k =
          (alg.x (k + 1) - alg.x k) -
            alphaSeq k • (alg.x k - alg.x (k - 1)) := by
      rw [hy_def]
      abel_nf
    rw [htarget]
    exact prop_2_5_quadratic_lower_bound
      (alg.x (k + 1) - alg.x k) (alg.x k - alg.x (k - 1))
      (alphaSeq k) (halpha_mem k).1
  have hZ_pos (k : ℕ) : 0 ≤ (rho k)⁻¹ - 1 / 2 := by
    have hlt2 : rho k < 2 := lt_of_le_of_lt (hR2_ge k) hR2_lt_two
    have hposR : 0 < rho k := hrho_pos k
    have hhalf : (1 / 2 : ℝ) < (rho k)⁻¹ := by
      have h := one_div_lt_one_div_of_lt hposR hlt2
      simpa [one_div] using h
    linarith
  have hineq_A (k : ℕ) :
      phi (k + 1) ≤ phi k + alphaSeq k * (phi k - phi (k - 1))
        + (((alphaSeq k + (alphaSeq k) ^ 2) / 2) +
          ((rho k)⁻¹ - 1 / 2) * alphaSeq k * (1 - alphaSeq k)) *
          ‖alg.x k - alg.x (k - 1)‖ ^ 2
        - ((rho k)⁻¹ - 1 / 2) * (1 - alphaSeq k) *
          ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
    have h29 := hineq_29 k
    have hq := hquad_lower k
    have hZ := hZ_pos k
    nlinarith
  have hcoeff_simplify (k : ℕ) :
      ((alphaSeq k + (alphaSeq k) ^ 2) / 2) +
          ((rho k)⁻¹ - 1 / 2) * alphaSeq k * (1 - alphaSeq k) =
        alphaSeq k * ((rho k)⁻¹ + (1 - (rho k)⁻¹) * alphaSeq k) := by
    ring
  have hineq_B (k : ℕ) :
      phi (k + 1) - alphaSeq k * phi k ≤
        phi k - alphaSeq k * phi (k - 1) +
          alphaSeq k * ((rho k)⁻¹ + (1 - (rho k)⁻¹) * alphaSeq k) *
            ‖alg.x k - alg.x (k - 1)‖ ^ 2 -
          ((rho k)⁻¹ - 1 / 2) * (1 - alphaSeq k) *
            ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
    have hA := hineq_A k
    have hc := hcoeff_simplify k
    nlinarith
  have hmu_descent_raw (k : ℕ) :
      mu (k + 1) ≤ mu k +
        (alphaSeq (k + 1) * ((rho (k + 1))⁻¹ +
            (1 - (rho (k + 1))⁻¹) * alphaSeq (k + 1)) +
          ((rho k)⁻¹ - 1 / 2) * (alphaSeq k - 1)) *
          ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
    have hB := hineq_B k
    have hphi_nonneg : 0 ≤ phi k := by
      dsimp [phi]
      positivity
    have hmono_term : -alphaSeq (k + 1) * phi k ≤ -alphaSeq k * phi k := by
      nlinarith [halpha_mono k, hphi_nonneg]
    dsimp [mu]
    nlinarith
  have hR2_pos : 0 < R2 := by
    exact lt_of_lt_of_le (hrho_pos 0) (hR2_ge 0)
  have hcoeff_sum (k : ℕ) :
      alphaSeq (k + 1) * ((rho (k + 1))⁻¹ +
            (1 - (rho (k + 1))⁻¹) * alphaSeq (k + 1)) +
          ((rho k)⁻¹ - 1 / 2) * (alphaSeq k - 1) ≤
        -pCoeff R1 R2 alphaBar := by
    have ha0 : 0 ≤ alphaSeq k := (halpha_mem k).1
    have ha1 : alphaSeq k < 1 := (halpha_mem k).2
    have ha_le : alphaSeq k ≤ alphaBar := halphaBar_bound k
    have ha_next0 : 0 ≤ alphaSeq (k + 1) := (halpha_mem (k + 1)).1
    have ha_next1 : alphaSeq (k + 1) < 1 := (halpha_mem (k + 1)).2
    have ha_next_le : alphaSeq (k + 1) ≤ alphaBar := halphaBar_bound (k + 1)
    have ha_mono : alphaSeq k ≤ alphaSeq (k + 1) := halpha_mono k
    have hr_pos : 0 < rho k := hrho_pos k
    have hr_next_pos : 0 < rho (k + 1) := hrho_pos (k + 1)
    have hr_ge : R1 ≤ rho k := hR1_le k
    have hr_next_ge : R1 ≤ rho (k + 1) := hR1_le (k + 1)
    have hr_le : rho k ≤ R2 := hR2_ge k
    have hr_next_le : rho (k + 1) ≤ R2 := hR2_ge (k + 1)
    have hp_unfold : 0 < 1 / R2 - 1 / 2 -
        (2 / R1 - 1 / 2) * alphaBar - (1 - 1 / R2) * alphaBar ^ 2 := by
      simpa [pCoeff] using hp_pos_alphaBar_R1_R2
    have hp_inv : 0 < R2⁻¹ - 1 / 2 -
        (2 * R1⁻¹ - 1 / 2) * alphaBar - (1 - R2⁻¹) * alphaBar ^ 2 := by
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp_unfold
    have hR1_le_R2 : R1 ≤ R2 := le_trans (hR1_le 0) (hR2_ge 0)
    have h_inv_next_le : (rho (k + 1))⁻¹ ≤ R1⁻¹ :=
      (inv_le_inv₀ hr_next_pos hR1_pos).2 hr_next_ge
    have h_inv_ge : R2⁻¹ ≤ (rho k)⁻¹ :=
      (inv_le_inv₀ hR2_pos hr_pos).2 hr_le
    have h_R2_inv_le_R1_inv : R2⁻¹ ≤ R1⁻¹ :=
      (inv_le_inv₀ hR2_pos hR1_pos).2 hR1_le_R2
    have h_R2_inv_gt_half : (1 / 2 : ℝ) < R2⁻¹ := by
      have h := one_div_lt_one_div_of_lt hR2_pos hR2_lt_two
      simpa [one_div] using h
    simpa [pCoeff, one_div] using
      prop_2_5_coeff_bound
        (alphaSeq (k + 1)) (alphaSeq k) alphaBar R1⁻¹ R2⁻¹
        (rho k)⁻¹ (rho (k + 1))⁻¹
        ha_next0 ha_next1 ha_next_le ha_mono halphaBar_lt_one
        h_inv_next_le h_inv_ge h_R2_inv_le_R1_inv h_R2_inv_gt_half hp_inv
  have hmu_descent (k : ℕ) :
      mu (k + 1) ≤
        mu k - pCoeff R1 R2 alphaBar * ‖alg.x (k + 1) - alg.x k‖ ^ 2 := by
    have hraw := hmu_descent_raw k
    have hcoeff := hcoeff_sum k
    have hnorm_sq_nonneg : 0 ≤ ‖alg.x (k + 1) - alg.x k‖ ^ 2 := sq_nonneg _
    nlinarith
  have hmu_diff (k : ℕ) :
      pCoeff R1 R2 alphaBar * ‖alg.x (k + 1) - alg.x k‖ ^ 2 ≤
        mu k - mu (k + 1) := by
    have h := hmu_descent k
    linarith
  have h_alphaBar_nonneg : 0 ≤ alphaBar :=
    le_trans (halpha_mem 0).1 (halphaBar_bound 0)
  have h_one_minus_alphaBar_pos : 0 < 1 - alphaBar := sub_pos.mpr halphaBar_lt_one
  have hmu_noninc_step (k : ℕ) : mu (k + 1) ≤ mu k := by
    have h := hmu_descent k
    have hnorm_sq_nonneg : 0 ≤ ‖alg.x (k + 1) - alg.x k‖ ^ 2 := sq_nonneg _
    have hp_nonneg : 0 ≤ pCoeff R1 R2 alphaBar := le_of_lt hp_pos_alphaBar_R1_R2
    have hprod_nonneg :
        0 ≤ pCoeff R1 R2 alphaBar * ‖alg.x (k + 1) - alg.x k‖ ^ 2 :=
      mul_nonneg hp_nonneg hnorm_sq_nonneg
    nlinarith
  have hmu_le_mu0 (k : ℕ) : mu k ≤ mu 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
        exact le_trans (hmu_noninc_step k) ih
  have hphi_nonneg (k : ℕ) : 0 ≤ phi k := by
    dsimp [phi]
    positivity
  have hmu0_nonneg : 0 ≤ mu 0 := by
    have hphi0 := hphi_nonneg 0
    have ha0_lt_one : alphaSeq 0 < 1 := (halpha_mem 0).2
    dsimp [mu]
    simp
    nlinarith
  have hphi_recurrence (k : ℕ) :
      phi k ≤ mu 0 + alphaBar * phi (k - 1) := by
    have hmu_le := hmu_le_mu0 k
    have hextra_nonneg :
        0 ≤ alphaSeq k * ((rho k)⁻¹ + (1 - (rho k)⁻¹) * alphaSeq k) *
          ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
      exact mul_nonneg (hmu_coeff_nonneg k) (sq_nonneg _)
    have ha_le : alphaSeq k ≤ alphaBar := halphaBar_bound k
    have hprev_nonneg : 0 ≤ phi (k - 1) := hphi_nonneg (k - 1)
    dsimp [mu] at hmu_le
    nlinarith
  let M : ℝ := phi 0 + mu 0 / (1 - alphaBar)
  have hM_ge_phi0 : phi 0 ≤ M := by
    dsimp [M]
    have hdiv_nonneg : 0 ≤ mu 0 / (1 - alphaBar) :=
      div_nonneg hmu0_nonneg (le_of_lt h_one_minus_alphaBar_pos)
    nlinarith
  have hM_absorb : mu 0 + alphaBar * M ≤ M := by
    dsimp [M]
    have hphi0_nonneg := hphi_nonneg 0
    have hfrac_absorb :
        mu 0 + alphaBar * (mu 0 / (1 - alphaBar)) = mu 0 / (1 - alphaBar) := by
      field_simp [h_one_minus_alphaBar_pos.ne']
      ring
    calc
      mu 0 + alphaBar * (phi 0 + mu 0 / (1 - alphaBar))
          = alphaBar * phi 0 + (mu 0 + alphaBar * (mu 0 / (1 - alphaBar))) := by
            ring
      _ = alphaBar * phi 0 + mu 0 / (1 - alphaBar) := by
            rw [hfrac_absorb]
      _ ≤ phi 0 + mu 0 / (1 - alphaBar) := by
            nlinarith
  have hphi_bound (k : ℕ) : phi k ≤ M := by
    induction k with
    | zero => exact hM_ge_phi0
    | succ k ih =>
        have hrec : phi (k + 1) ≤ mu 0 + alphaBar * phi k := by
          simpa using hphi_recurrence (k + 1)
        have hmul : alphaBar * phi k ≤ alphaBar * M :=
          mul_le_mul_of_nonneg_left ih h_alphaBar_nonneg
        nlinarith
  have hM_nonneg : 0 ≤ M := le_trans (hphi_nonneg 0) hM_ge_phi0
  have h_neg_mu_bound (n : ℕ) : -mu n ≤ alphaBar * M := by
    have hphi_n_nonneg : 0 ≤ phi n := hphi_nonneg n
    have hphi_prev_nonneg : 0 ≤ phi (n - 1) := hphi_nonneg (n - 1)
    have hphi_prev_bound : phi (n - 1) ≤ M := hphi_bound (n - 1)
    have ha_le : alphaSeq n ≤ alphaBar := halphaBar_bound n
    have hextra_nonneg :
        0 ≤ alphaSeq n * ((rho n)⁻¹ + (1 - (rho n)⁻¹) * alphaSeq n) *
          ‖alg.x n - alg.x (n - 1)‖ ^ 2 := by
      exact mul_nonneg (hmu_coeff_nonneg n) (sq_nonneg _)
    have hmu_eq : mu n =
        phi n - alphaSeq n * phi (n - 1) +
          alphaSeq n * ((rho n)⁻¹ + (1 - (rho n)⁻¹) * alphaSeq n) *
            ‖alg.x n - alg.x (n - 1)‖ ^ 2 := rfl
    have hmu_lower : -alphaSeq n * phi (n - 1) ≤ mu n := by
      rw [hmu_eq]
      linarith
    have hneg_le : -mu n ≤ alphaSeq n * phi (n - 1) := by linarith
    have hprod_le_alpha :
        alphaSeq n * phi (n - 1) ≤ alphaBar * phi (n - 1) :=
      mul_le_mul_of_nonneg_right ha_le hphi_prev_nonneg
    have hprod_le_M : alphaBar * phi (n - 1) ≤ alphaBar * M :=
      mul_le_mul_of_nonneg_left hphi_prev_bound h_alphaBar_nonneg
    linarith
  have h_bound_term (k : ℕ) :
      ‖alg.x (k + 1) - alg.x k‖ ^ 2 ≤
        (mu k - mu (k + 1)) / (pCoeff R1 R2 alphaBar) := by
    exact (le_div_iff₀ hp_pos_alphaBar_R1_R2).2 (by simpa [mul_comm] using hmu_diff k)
  have h_telescope (n : ℕ) :
      (Finset.range n).sum (fun k : ℕ => mu k - mu (k + 1)) = mu 0 - mu n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have h_partial_sum_bound (n : ℕ) :
      (Finset.range n).sum (fun k : ℕ => ‖alg.x (k + 1) - alg.x k‖ ^ 2) ≤
        (mu 0 + alphaBar * M) / (pCoeff R1 R2 alphaBar) := by
    calc
      (Finset.range n).sum (fun k : ℕ => ‖alg.x (k + 1) - alg.x k‖ ^ 2)
          ≤ (Finset.range n).sum
              (fun k : ℕ => (mu k - mu (k + 1)) / (pCoeff R1 R2 alphaBar)) := by
            exact Finset.sum_le_sum (fun k _ => h_bound_term k)
      _ = ((Finset.range n).sum (fun k : ℕ => mu k - mu (k + 1))) /
            (pCoeff R1 R2 alphaBar) := by
            rw [Finset.sum_div]
      _ = (mu 0 - mu n) / (pCoeff R1 R2 alphaBar) := by
            rw [h_telescope n]
      _ ≤ (mu 0 + alphaBar * M) / (pCoeff R1 R2 alphaBar) := by
            exact div_le_div_of_nonneg_right (by linarith [h_neg_mu_bound n])
              (le_of_lt hp_pos_alphaBar_R1_R2)
  have hsum_shifted : Summable (fun k : ℕ ↦ ‖alg.x (k + 1) - alg.x k‖ ^ 2) := by
    exact summable_of_sum_range_le (fun k => sq_nonneg _) h_partial_sum_bound
  exact (summable_nat_add_iff (f := fun k : ℕ => ‖alg.x k - alg.x (k - 1)‖ ^ 2) 1).1
    (by simpa using hsum_shifted)

/-- Proposition 2.5: the additional monotonicity and coefficient condition imply
square summability of increments and weak convergence. -/
theorem proposition_2_5
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alphaSeq rho sigma)
    (hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alphaSeq k ∧ alphaSeq k < 1)
    (halpha_mono : ∀ k : ℕ, alphaSeq k ≤ alphaSeq (k + 1))
    (hp_pos_alphaBar_R1_R2 : 0 < pCoeff R1 R2 alphaBar)
    (halphaBar_lt_one : alphaBar < 1)
    (halphaBar_bound : ∀ k : ℕ, alphaSeq k ≤ alphaBar)
    (hR1_pos : 0 < R1) (hR1_le : ∀ k : ℕ, R1 ≤ rho k)
    (hR2_lt_two : R2 < 2) (hR2_ge : ∀ k : ℕ, rho k ≤ R2)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) ∧
      ∃ xhat ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
  by_cases hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0
  · exact proposition_2_5_nonterminating A hA sigma hsigma alg hv_nonzero
      hlam_lower halpha_mem halpha_mono hp_pos_alphaBar_R1_R2 halphaBar_lt_one
      halphaBar_bound hR1_pos hR1_le hR2_lt_two hR2_ge hS
  · push Not at hv_nonzero
    rcases hv_nonzero with ⟨K, hvK⟩
    have htail := alg.finite_stop_if_zero K hvK
    have hsummable_sq :
        Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) := by
      apply summable_of_hasFiniteSupport
      rw [Function.HasFiniteSupport]
      refine (Set.finite_lt_nat (K + 2)).subset ?_
      intro n hn
      by_contra hlt
      have hge : K + 2 ≤ n := le_of_not_gt hlt
      have hn_tail : K + 1 ≤ n := by omega
      have hprev_tail : K + 1 ≤ n - 1 := by omega
      have hxn := (htail n hn_tail).1
      have hxprev := (htail (n - 1) hprev_tail).1
      have hzero : ‖alg.x n - alg.x (n - 1)‖ ^ 2 = 0 := by
        simp [hxn, hxprev]
      exact hn hzero
    have halpha_summable :
        Summable fun k : ℕ ↦ alphaSeq k * ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
      refine hsummable_sq.of_nonneg_of_le ?hnonneg ?hle
      · intro k
        exact mul_nonneg (halpha_mem k).1 (sq_nonneg _)
      · intro k
        have ha_le_one : alphaSeq k ≤ 1 := le_of_lt (halpha_mem k).2
        exact mul_le_of_le_one_left (sq_nonneg _) ha_le_one
    let params : ParameterAssumptions alg.x :=
      { lam := lam
        alpha := alphaSeq
        rho := rho
        lam_lower := hlam_lower
        alpha_mem := halpha_mem
        alpha_upper := ⟨alphaBar, halphaBar_lt_one, halphaBar_bound⟩
        alpha_summable := halpha_summable
        rho_lower := ⟨R1, hR1_pos, hR1_le⟩
        rho_upper := ⟨R2, hR2_lt_two, hR2_ge⟩ }
    have hweak :
        ∃ xhat ∈ SetValuedOperator.zeros A,
          Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) := by
      rcases theorem_2_2 A hA sigma hsigma alg params rfl rfl rfl hS with
        ⟨_, _, _, hweak⟩
      exact hweak
    exact ⟨hsummable_sq, hweak⟩

end Alvarez2004
