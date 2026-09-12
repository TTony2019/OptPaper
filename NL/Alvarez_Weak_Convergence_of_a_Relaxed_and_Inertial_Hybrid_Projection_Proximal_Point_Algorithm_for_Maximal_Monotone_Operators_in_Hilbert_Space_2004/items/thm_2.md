## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/thm_2.lean`

## Lean statement
```lean
theorem theorem_3_1
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (x y v eta : ℕ → H) (lam alpha rho : ℕ → ℝ)
    (rec : InexactProximalRecurrence A x y v eta lam alpha rho)
    (params : ParameterAssumptions x)
    (hlam_eq : lam = params.lam)
    (halpha_eq : alpha = params.alpha)
    (hrho_eq : rho = params.rho)
    (hS : (SetValuedOperator.zeros A).Nonempty)
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖)
    (h33 : Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k‖) :
    Tendsto (fun k : ℕ ↦ v k) atTop (𝓝 (0 : H)) ∧
      ∃ xstar ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (x k)) atTop
          (𝓝 (toWeakSpace ℝ H xstar))
```

## Statement explanation
The declaration is a convergence theorem for an inexact relaxed inertial proximal-point method for a maximal monotone set-valued operator \(A\) on the ambient real Hilbert space \(H\). The operator is \(A:H\to 2^H\), and \(h_A\) says that \(A\) is maximal monotone. The sequences \(x,y,v,\eta:\mathbb N\to H\) and the scalar sequences \(\lambda,\alpha,\rho:\mathbb N\to\mathbb R\) encode the iterates, an auxiliary sequence \(y\), the inexactness/residual sequence \(v\), the error sequence \(\eta\), and the step, inertia, and relaxation parameters. The hypothesis `rec : InexactProximalRecurrence A x y v eta lam alpha rho` packages the recurrence. The proof uses its fields in the following visible ways: \(y_k=x_k+\alpha_k(x_k-x_{k-1})\); \(\eta_k=\lambda_k^{-1}(x_{k+1}-y_k)+v_k\); and, after unfolding the scalar multiple of a set-valued operator, \(v_k=\rho_k a_k\) for some \(a_k\in A(z_k)\), where \(z_k=\rho_k^{-1}x_{k+1}+(1-\rho_k^{-1})y_k\). The hypothesis `params : ParameterAssumptions x` supplies the parameter bounds and summability properties for \(x\). The equalities `hlam_eq`, `halpha_eq`, and `hrho_eq` identify the recurrence parameters with those parameter assumptions.

The parameter assumptions used in the proof are: there is \(\lambda_0>0\) with \(\lambda_0\le \lambda_k\) for all \(k\); for all \(k\), \(0\le \alpha_k<1\); there is \(\alpha_0<1\) with \(\alpha_k\le \alpha_0\) for all \(k\); the series \(\sum_k \alpha_k\|x_k-x_{k-1}\|^2\) converges; there is \(R_1>0\) with \(R_1\le \rho_k\) for all \(k\); and there is \(R_2<2\) with \(\rho_k\le R_2\) for all \(k\). The extra hypotheses are that the zero set of \(A\), \(A^{-1}(0)=\{x:0\in A x\}\), is nonempty; that \(\sum_k \lambda_k\|\eta_k\|<\infty\); and that \(\sum_k \lambda_k\|\eta_k\|\|y_k\|<\infty\). The conclusion is the conjunction of two statements: first, \(v_k\to 0\) strongly in \(H\); second, there exists \(x_\star\in A^{-1}(0)\) such that \(x_k\) converges weakly to \(x_\star\), expressed by convergence of \(\operatorname{toWeakSpace}_{\mathbb R,H}(x_k)\) to \(\operatorname{toWeakSpace}_{\mathbb R,H}(x_\star)\).

## Lean proof
```lean
by
  classical
  have hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k := by
    rcases params.lam_lower with ⟨lam0, hpos, hlow⟩
    refine ⟨lam0, hpos, ?_⟩
    intro k
    simpa [hlam_eq] using hlow k
  have hlam_pos (k : ℕ) : 0 < lam k := by
    rcases hlam_lower with ⟨lam0, hpos, hlow⟩
    exact lt_of_lt_of_le hpos (hlow k)
  have hlam_ne_zero (k : ℕ) : lam k ≠ 0 := (hlam_pos k).ne'
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
      Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2 := by
    simpa [halpha_eq] using params.alpha_summable
  have hdelta_inertial_summable :
      Summable fun k : ℕ ↦
        ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 :=
    inertial_delta_summable_thm2 x alpha halpha_summable halpha_mem
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
  obtain ⟨R2, hR2_lt, hR2_le⟩ := hrho_upper
  have hrho_pos (k : ℕ) : 0 < rho k := lt_of_lt_of_le hR1_pos (hR1_le k)
  have hrho_ne_zero (k : ℕ) : rho k ≠ 0 := (hrho_pos k).ne'
  have hR2_pos : 0 < R2 := lt_of_lt_of_le (hrho_pos 0) (hR2_le 0)
  have hR2_ne_zero : R2 ≠ 0 := hR2_pos.ne'
  let J_seq (k : ℕ) (z : H) : H :=
    Classical.choose (resolvent_nonempty hA (hlam_pos k) z)
  have hJ_seq (k : ℕ) (z : H) :
      J_seq k z ∈ J[(lam k • A)] z :=
    Classical.choose_spec (resolvent_nonempty hA (hlam_pos k) z)
  let A_lam_sv (k : ℕ) (z : H) : H := (lam k)⁻¹ • (z - J_seq k z)
  let w (k : ℕ) : H := (1 - rho k) • y k + rho k • J_seq k (y k)
  let xi (k : ℕ) : H := y k - J_seq k (y k)
  have h_eta_tendsto_zero : Tendsto (fun k : ℕ ↦ ‖eta k‖) atTop (𝓝 0) :=
    eta_norm_tendsto_zero (eta := eta) (lam := lam) hlam_lower h31
  have h_rho_factor_pos : 0 < R1 * (1 - R2 / 2) := by
    have hhalf : R2 / 2 < 1 := by linarith
    have hpos : 0 < 1 - R2 / 2 := by linarith
    exact mul_pos hR1_pos hpos
  have h_rho_factor_nonneg (k : ℕ) : 0 ≤ rho k * (1 - rho k / 2) := by
    have hhalf : rho k / 2 ≤ 1 := by linarith [hR2_le k, hR2_lt]
    have hnonneg : 0 ≤ 1 - rho k / 2 := by linarith
    exact mul_nonneg (le_of_lt (hrho_pos k)) hnonneg
  have h_rho_lower_bound (k : ℕ) :
      R1 * (1 - R2 / 2) ≤ rho k * (1 - rho k / 2) := by
    have hleft : 0 ≤ 1 - R2 / 2 := by linarith [hR2_lt]
    have hright : 0 ≤ rho k := le_of_lt (hrho_pos k)
    have hfactor : 1 - R2 / 2 ≤ 1 - rho k / 2 := by linarith [hR2_le k]
    have hmul₁ : R1 * (1 - R2 / 2) ≤ rho k * (1 - R2 / 2) :=
      mul_le_mul_of_nonneg_right (hR1_le k) hleft
    have hmul₂ : rho k * (1 - R2 / 2) ≤ rho k * (1 - rho k / 2) :=
      mul_le_mul_of_nonneg_left hfactor hright
    exact le_trans hmul₁ hmul₂
  rcases hS with ⟨xbar, hxbar⟩
  have h_y_error_summable :
      Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k - xbar‖ := by
    have hconst : Summable fun k : ℕ ↦ ‖xbar‖ * (lam k * ‖eta k‖) :=
      h31.mul_left ‖xbar‖
    have hsum :
        Summable fun k : ℕ ↦
          lam k * ‖eta k‖ * ‖y k‖ + ‖xbar‖ * (lam k * ‖eta k‖) :=
      h33.add hconst
    refine hsum.of_nonneg_of_le ?hnonneg ?hle
    · intro k
      exact mul_nonneg (mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)) (norm_nonneg _)
    · intro k
      have hfac : 0 ≤ lam k * ‖eta k‖ :=
        mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
      have htri : ‖y k - xbar‖ ≤ ‖y k‖ + ‖xbar‖ := by
        simpa using norm_sub_le (y k) xbar
      calc
        lam k * ‖eta k‖ * ‖y k - xbar‖
            ≤ lam k * ‖eta k‖ * (‖y k‖ + ‖xbar‖) :=
              mul_le_mul_of_nonneg_left htri hfac
        _ = lam k * ‖eta k‖ * ‖y k‖ + ‖xbar‖ * (lam k * ‖eta k‖) := by
              ring
  have hJ_xbar_fixed (k : ℕ) : J_seq k xbar = xbar := by
    have hxbar_res : xbar ∈ J[(lam k • A)] xbar :=
      (Alvarez2004.resolvent_fixed_iff_zero A hA (hlam_pos k) xbar).mpr hxbar
    have hsingle := resolvent_is_at_most_single_valued A hA (hlam_pos k)
    exact hsingle xbar (hJ_seq k xbar) hxbar_res
  have hA_lam_xbar_zero (k : ℕ) : A_lam_sv k xbar = 0 := by
    dsimp [A_lam_sv]
    simp [hJ_xbar_fixed k]
  have hxi_graph (k : ℕ) : (lam k)⁻¹ • xi k ∈ A (y k - xi k) := by
    dsimp [xi]
    exact yosida_resolvent_equiv A (hlam_ne_zero k) (hJ_seq k (y k)) rfl
  have h_alpha_diff_norm_tendsto_zero :
      Tendsto (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖) atTop (𝓝 0) :=
    alpha_diff_norm_tendsto_zero_thm2 x alpha halpha_summable halpha_mem
  have h_lam_sq_eta_sq_summable :
      Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖eta k‖ ^ 2 :=
    lam_sq_eta_sq_summable_thm2 hlam_pos h31
  have h_eta_tendsto_zero_vec : Tendsto (fun k : ℕ ↦ eta k) atTop (𝓝 (0 : H)) := by
    simpa [Metric.tendsto_atTop] using h_eta_tendsto_zero
  have h_xi_eq_lam_A_lam (k : ℕ) : xi k = lam k • A_lam_sv k (y k) := by
    dsimp [xi, A_lam_sv]
    simp [smul_smul, hlam_ne_zero k]
  have h_A_lam_eq_inv_smul_xi (k : ℕ) : A_lam_sv k (y k) = (lam k)⁻¹ • xi k := by
    dsimp [xi, A_lam_sv]
  have h_w_eq_y_sub_rho_xi (k : ℕ) : w k = y k - rho k • xi k := by
    dsimp [w, xi]
    module
  have hJ_firm (k : ℕ) : FirmlyNonexpansive (J_seq k) :=
    firmly_nonexpansive_resolvent_selection_thm2 hA.1 (lam k) (hlam_pos k)
      (J_seq k) (hJ_seq k)
  have hJ_cocoercive (k : ℕ) :
      CocoerciveOn (1 : ℝ) Set.univ (fun z : Set.univ ↦ J_seq k z) :=
    firmly_nonexpansive_cocoerciveOn_one_thm2 (hJ_firm k)
  have h_residual_firm (k : ℕ) :
      FirmlyNonexpansiveOn Set.univ
        (residualMap Set.univ (fun z : Set.univ ↦ J_seq k z)) := by
    rw [firmlyNonexpansiveOn_residualMap_iff]
    simpa [FirmlyNonexpansive] using hJ_firm k
  have h_residual_cocoercive (k : ℕ) :
      CocoerciveOn (1 : ℝ) Set.univ
        (residualMap Set.univ (fun z : Set.univ ↦ J_seq k z)) := by
    exact firmly_nonexpansiveOn_cocoerciveOn_one_thm2 (h_residual_firm k)
  have h_cocoercive (k : ℕ) (z₁ z₂ : H) :
      lam k * ‖A_lam_sv k z₁ - A_lam_sv k z₂‖ ^ 2 ≤
        inner ℝ (A_lam_sv k z₁ - A_lam_sv k z₂) (z₁ - z₂) := by
    simpa [A_lam_sv] using
      scaled_residual_cocoercive_thm2 (lam k) (hlam_pos k) (J_seq k)
        (h_residual_cocoercive k) z₁ z₂
  have h_inertial_expansion (k : ℕ) (xbar' : H) :
      (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 =
        (1 / 2) * ‖x k - xbar'‖ ^ 2 +
          alpha k * ((1 / 2) * ‖x k - xbar'‖ ^ 2 -
            (1 / 2) * ‖x (k - 1) - xbar'‖ ^ 2) +
          ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 :=
    inertial_expansion_y_thm2 x y alpha rec.y_def k xbar'
  let φ (xbar' : H) (k : ℕ) : ℝ := (1 / 2 : ℝ) * ‖x k - xbar'‖ ^ 2
  let δ (xbar' : H) (k : ℕ) : ℝ :=
    ((alpha k + alpha k ^ 2) / 2) * ‖x k - x (k - 1)‖ ^ 2 +
      lam k * ‖eta k‖ * ‖y k - xbar'‖ +
      ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2
  have h35 : ∀ k : ℕ, ‖x (k + 1) - w k‖ ≤ lam k * ‖eta k‖ := by
    intro k
    have h_resolvent_rewrite :
        J_seq k (y k + ((lam k) / (rho k)) • eta k) =
          (rho k)⁻¹ • x (k + 1) + (1 - (rho k)⁻¹) • y k := by
      let z : H := (rho k)⁻¹ • x (k + 1) + (1 - (rho k)⁻¹) • y k
      have hv_mem := rec.inclusion k
      rw [Set.mem_smul_set] at hv_mem
      rcases hv_mem with ⟨a, ha, hv_eq⟩
      have heq := rec.equation k
      have h_eta :
          eta k = (lam k)⁻¹ • (x (k + 1) - y k) + rho k • a := by
        rw [← heq, hv_eq]
      have hdiff :
          y k + ((lam k) / (rho k)) • eta k - z = lam k • a := by
        dsimp [z]
        rw [h_eta]
        have hrho_nz : rho k ≠ 0 := hrho_ne_zero k
        have hlam_nz : lam k ≠ 0 := hlam_ne_zero k
        have hcoeff1 : (lam k / rho k) * (lam k)⁻¹ = (rho k)⁻¹ := by
          field_simp [hrho_nz, hlam_nz]
        have hcoeff2 : (lam k / rho k) * rho k = lam k := by
          field_simp [hrho_nz]
        rw [smul_add, smul_smul, smul_smul, hcoeff1, hcoeff2]
        module
      have hz_mem :
          z ∈ J[(lam k • A)] (y k + ((lam k) / (rho k)) • eta k) := by
        rw [SetValuedOperator.mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        refine ⟨a, ha, ?_⟩
        dsimp [z] at hdiff ⊢
        exact (eq_add_of_sub_eq' hdiff).symm
      exact resolvent_is_at_most_single_valued A hA (hlam_pos k)
        (y k + ((lam k) / (rho k)) • eta k)
        (hJ_seq k (y k + ((lam k) / (rho k)) • eta k)) hz_mem
    have hx_next_eq :
        x (k + 1) =
          (1 - rho k) • y k +
            rho k • J_seq k (y k + ((lam k) / (rho k)) • eta k) := by
      rw [h_resolvent_rewrite]
      have hrho_nz : rho k ≠ 0 := hrho_ne_zero k
      have hcoeff1 : rho k * (rho k)⁻¹ = 1 := by field_simp [hrho_nz]
      have hcoeff2 : rho k * (1 - (rho k)⁻¹) = rho k - 1 := by field_simp [hrho_nz]
      rw [smul_add, smul_smul, smul_smul, hcoeff1, hcoeff2, one_smul]
      module
    calc
      ‖x (k + 1) - w k‖
          = ‖((1 - rho k) • y k +
                rho k • J_seq k (y k + ((lam k) / (rho k)) • eta k)) -
              ((1 - rho k) • y k + rho k • J_seq k (y k))‖ := by
            rw [hx_next_eq]
      _ = ‖rho k •
              (J_seq k (y k + ((lam k) / (rho k)) • eta k) - J_seq k (y k))‖ := by
            congr 1
            rw [smul_sub]
            abel
      _ = rho k *
            ‖J_seq k (y k + ((lam k) / (rho k)) • eta k) - J_seq k (y k)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hrho_pos k)]
      _ ≤ rho k * ‖((lam k) / (rho k)) • eta k‖ := by
            have hlip :=
              resolvent_selection_lipschitz A hA (hlam_pos k) (J_seq k) (hJ_seq k)
            have hdist := hlip.dist_le_mul
              (y k + ((lam k) / (rho k)) • eta k) (y k)
            simp [dist_eq_norm] at hdist
            exact mul_le_mul_of_nonneg_left hdist (le_of_lt (hrho_pos k))
      _ = rho k * ((lam k) / (rho k) * ‖eta k‖) := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg (le_of_lt (hlam_pos k)) (le_of_lt (hrho_pos k)))]
      _ = lam k * ‖eta k‖ := by
            field_simp [hrho_ne_zero k]
  have h_norm_sub_smul_sq (a b : H) (c : ℝ) :
      ‖a - c • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * c * inner ℝ a b + c ^ 2 * ‖b‖ ^ 2 := by
    calc
      ‖a - c • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner ℝ a (c • b) + ‖c • b‖ ^ 2 := by
        rw [norm_sub_sq_real]
      _ = ‖a‖ ^ 2 - 2 * c * inner ℝ a b + c ^ 2 * ‖b‖ ^ 2 := by
        rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
        nlinarith [sq_abs c]
  have h38 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      (1 / 2 : ℝ) * ‖w k - xbar'‖ ^ 2 ≤
        (1 / 2) * ‖y k - xbar'‖ ^ 2 -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
    intro k xbar' hxbar'
    have hA_lam_xbar'_zero : A_lam_sv k xbar' = 0 := by
      exact (yosida_selection_eq_zero_iff_thm2 A hA (hlam_pos k) (J_seq k) (hJ_seq k) xbar').mp hxbar'
    have h_w_expand :
        w k - xbar' =
          (y k - xbar') - (lam k * rho k) • A_lam_sv k (y k) := by
      calc
        w k - xbar' = (y k - rho k • xi k) - xbar' := by rw [h_w_eq_y_sub_rho_xi k]
        _ = (y k - xbar') - rho k • xi k := by module
        _ = (y k - xbar') - rho k • (lam k • A_lam_sv k (y k)) := by
              rw [h_xi_eq_lam_A_lam k]
        _ = (y k - xbar') - (lam k * rho k) • A_lam_sv k (y k) := by
              rw [smul_smul]
              ring_nf
    rw [h_w_expand]
    rw [h_norm_sub_smul_sq (y k - xbar') (A_lam_sv k (y k)) (lam k * rho k)]
    have h_coco :
        lam k * ‖A_lam_sv k (y k)‖ ^ 2 ≤
          inner ℝ (A_lam_sv k (y k)) (y k - xbar') := by
      have h := h_cocoercive k (y k) xbar'
      simpa [hA_lam_xbar'_zero] using h
    have hinner_comm :
        inner ℝ (y k - xbar') (A_lam_sv k (y k)) =
          inner ℝ (A_lam_sv k (y k)) (y k - xbar') := by
      rw [real_inner_comm]
    have hcoef_nonneg : 0 ≤ lam k * rho k :=
      mul_nonneg (le_of_lt (hlam_pos k)) (le_of_lt (hrho_pos k))
    have hmain :
        (1 / 2 : ℝ) *
            (‖y k - xbar'‖ ^ 2 -
              2 * (lam k * rho k) * inner ℝ (y k - xbar') (A_lam_sv k (y k)) +
              (lam k * rho k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤
          (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 -
            (lam k) ^ 2 * rho k * (1 - rho k / 2) *
      ‖A_lam_sv k (y k)‖ ^ 2 := by
      rw [hinner_comm]
      nlinarith [mul_le_mul_of_nonneg_left h_coco hcoef_nonneg]
    exact hmain
  have h_sq_triangle (a b : H) :
      (1 / 2 : ℝ) * ‖a + b‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖a‖ ^ 2 + ‖a‖ * ‖b‖ + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
    calc
      (1 / 2 : ℝ) * ‖a + b‖ ^ 2 =
          (1 / 2 : ℝ) * (‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2) := by
            rw [norm_add_sq_real]
      _ = (1 / 2 : ℝ) * ‖a‖ ^ 2 + inner ℝ a b + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
            ring
      _ ≤ (1 / 2 : ℝ) * ‖a‖ ^ 2 + ‖a‖ * ‖b‖ + (1 / 2 : ℝ) * ‖b‖ ^ 2 := by
            nlinarith [real_inner_le_norm a b]
  have h39 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      (1 / 2 : ℝ) * ‖x (k + 1) - xbar'‖ ^ 2 ≤
        (1 / 2) * ‖y k - xbar'‖ ^ 2 -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 +
          lam k * ‖eta k‖ * ‖y k - xbar'‖ +
          ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2 := by
    intro k xbar' hxbar'
    have h_w_sq_bound :
        (1 / 2 : ℝ) * ‖w k - xbar'‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖y k - xbar'‖ ^ 2 := by
      have hfull := h38 k xbar' hxbar'
      have hnonneg :
          0 ≤ (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
        have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
          mul_nonneg (sq_nonneg _) (h_rho_factor_nonneg k)
        convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
        ring
      nlinarith
    have h_w_norm_bound : ‖w k - xbar'‖ ≤ ‖y k - xbar'‖ := by
      have h_sq : ‖w k - xbar'‖ ^ 2 ≤ ‖y k - xbar'‖ ^ 2 := by nlinarith
      simpa [abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp h_sq
    have h_decomp :
        x (k + 1) - xbar' = (w k - xbar') + (x (k + 1) - w k) := by
      module
    rw [h_decomp]
    have htri := h_sq_triangle (w k - xbar') (x (k + 1) - w k)
    have h35k := h35 k
    have h38k := h38 k xbar' hxbar'
    have h_eta_sq :
        ‖x (k + 1) - w k‖ ^ 2 ≤ (lam k * ‖eta k‖) ^ 2 := by
      have hrhs_nonneg : 0 ≤ lam k * ‖eta k‖ :=
        mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg _)
      nlinarith [h35k, norm_nonneg (x (k + 1) - w k)]
    have h_cross :
        ‖w k - xbar'‖ * ‖x (k + 1) - w k‖ ≤
          ‖y k - xbar'‖ * (lam k * ‖eta k‖) := by
      exact mul_le_mul h_w_norm_bound h35k (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have h310 : ∀ k : ℕ, ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      φ xbar' (k + 1) ≤
        φ xbar' k + alpha k * (φ xbar' k - φ xbar' (k - 1)) +
          δ xbar' k -
          (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
    intro k xbar' hxbar'
    have hdescent := h39 k xbar' hxbar'
    have hinertial := h_inertial_expansion k xbar'
    dsimp [φ, δ] at *
    nlinarith
  have hdelta_summable : ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      Summable (δ xbar') := by
    intro xbar' hxbar'
    have hyerr : Summable fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k - xbar'‖ := by
      have hconst : Summable fun k : ℕ ↦ ‖xbar'‖ * (lam k * ‖eta k‖) :=
        h31.mul_left ‖xbar'‖
      have hsum :
          Summable fun k : ℕ ↦
            lam k * ‖eta k‖ * ‖y k‖ + ‖xbar'‖ * (lam k * ‖eta k‖) :=
        h33.add hconst
      refine hsum.of_nonneg_of_le ?hyerr_nonneg ?hyerr_le
      · intro k
        exact mul_nonneg
          (mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg (eta k)))
          (norm_nonneg (y k - xbar'))
      · intro k
        have hfac : 0 ≤ lam k * ‖eta k‖ :=
          mul_nonneg (le_of_lt (hlam_pos k)) (norm_nonneg (eta k))
        have htri : ‖y k - xbar'‖ ≤ ‖y k‖ + ‖xbar'‖ := by
          simpa using norm_sub_le (y k) xbar'
        calc
          lam k * ‖eta k‖ * ‖y k - xbar'‖
              ≤ lam k * ‖eta k‖ * (‖y k‖ + ‖xbar'‖) :=
                mul_le_mul_of_nonneg_left htri hfac
          _ = lam k * ‖eta k‖ * ‖y k‖ + ‖xbar'‖ * (lam k * ‖eta k‖) := by
                ring
    have hlam_sq_half :
        Summable fun k : ℕ ↦ ((lam k) ^ 2 / 2) * ‖eta k‖ ^ 2 := by
      convert h_lam_sq_eta_sq_summable.mul_left (1 / 2 : ℝ) using 1
      ext k
      ring
    exact (hdelta_inertial_summable.add hyerr).add hlam_sq_half
  have h_lemma23_concl : ∀ xbar' : H, xbar' ∈ SetValuedOperator.zeros A →
      Summable (fun k : ℕ ↦ posPart (φ xbar' k - φ xbar' (k - 1))) ∧
        ∃ φstar : ℝ, 0 ≤ φstar ∧ Tendsto (φ xbar') atTop (𝓝 φstar) := by
    intro xbar' hxbar'
    have hphi_nonneg : ∀ k : ℕ, 0 ≤ φ xbar' k := by
      intro k
      dsimp [φ]
      positivity
    have hdelta_nonneg : ∀ k : ℕ, 0 ≤ δ xbar' k := by
      intro k
      dsimp [δ]
      have ha0 : 0 ≤ alpha k := (halpha_mem k).1
      have hlam0 : 0 ≤ lam k := le_of_lt (hlam_pos k)
      positivity
    have hrec : ∀ k : ℕ,
        φ xbar' (k + 1) ≤
          φ xbar' k + alpha k * (φ xbar' k - φ xbar' (k - 1)) + δ xbar' k := by
      intro k
      have hfull := h310 k xbar' hxbar'
      have hnonneg :
          0 ≤ (lam k) ^ 2 * rho k * (1 - rho k / 2) *
            ‖A_lam_sv k (y k)‖ ^ 2 := by
        have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
          mul_nonneg (sq_nonneg (lam k)) (h_rho_factor_nonneg k)
        convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
        ring
      nlinarith
    exact lemma_2_3 (φ xbar') (δ xbar') alpha alpha0 hphi_nonneg hdelta_nonneg
      hrec (hdelta_summable xbar' hxbar') halpha_bound halpha0_lt
  have h_dist_all : ∀ xbar' ∈ SetValuedOperator.zeros A,
      ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar'‖) atTop (𝓝 l) := by
    intro xbar' hxbar'
    rcases (h_lemma23_concl xbar' hxbar').2 with ⟨φstar, hφstar_nonneg, hφ_tendsto⟩
    have h_norm_sq_tendsto :
        Tendsto (fun k : ℕ => ‖x k - xbar'‖ ^ 2) atTop (𝓝 (2 * φstar)) := by
      have h_eq :
          (fun k : ℕ => ‖x k - xbar'‖ ^ 2) = (fun k : ℕ => 2 * φ xbar' k) := by
        funext k
        dsimp [φ]
        ring
      rw [h_eq]
      simpa using hφ_tendsto.const_mul 2
    have h_norm_tendsto :
        Tendsto (fun k : ℕ => ‖x k - xbar'‖) atTop
          (𝓝 (Real.sqrt (2 * φstar))) := by
      have h_sqrt_tendsto :
          Tendsto (fun k : ℕ => Real.sqrt (‖x k - xbar'‖ ^ 2)) atTop
            (𝓝 (Real.sqrt (2 * φstar))) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h_norm_sq_tendsto
      have h_eq :
          (fun k : ℕ => Real.sqrt (‖x k - xbar'‖ ^ 2)) =
            (fun k : ℕ => ‖x k - xbar'‖) := by
        funext k
        simp
      simpa [h_eq] using h_sqrt_tendsto
    exact ⟨Real.sqrt (2 * φstar), h_norm_tendsto⟩
  have h_yosida_sq_summable :
      Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 := by
    set gamma_seq : ℕ → ℝ := fun k : ℕ =>
      (lam k) ^ 2 * rho k * (1 - rho k / 2) * ‖A_lam_sv k (y k)‖ ^ 2
      with hgamma_seq_def
    have hgamma_nonneg : ∀ k : ℕ, 0 ≤ gamma_seq k := by
      intro k
      rw [hgamma_seq_def]
      have hleft : 0 ≤ (lam k) ^ 2 * (rho k * (1 - rho k / 2)) :=
        mul_nonneg (sq_nonneg _) (h_rho_factor_nonneg k)
      convert mul_nonneg hleft (sq_nonneg ‖A_lam_sv k (y k)‖) using 1
      ring
    have hsummable_gamma : Summable gamma_seq := by
      have hrecurrence_rearranged (k : ℕ) :
          gamma_seq k ≤
            φ xbar k - φ xbar (k + 1) +
              alpha k * (φ xbar k - φ xbar (k - 1)) + δ xbar k := by
        have hfull := h310 k xbar hxbar
        rw [hgamma_seq_def]
        nlinarith
      have halpha_theta_bound (k : ℕ) :
          alpha k * (φ xbar k - φ xbar (k - 1)) ≤
            alpha0 * posPart (φ xbar k - φ xbar (k - 1)) := by
        set theta := φ xbar k - φ xbar (k - 1)
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
            (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
            alpha0 * (Finset.range (n + 1)).sum
              (fun k => posPart (φ xbar k - φ xbar (k - 1))) +
            (Finset.range (n + 1)).sum (δ xbar) := by
        calc
          (Finset.range (n + 1)).sum gamma_seq ≤
              (Finset.range (n + 1)).sum
                (fun k => φ xbar k - φ xbar (k + 1) +
                  alpha k * (φ xbar k - φ xbar (k - 1)) + δ xbar k) := by
            exact Finset.sum_le_sum (fun i _hi => hrecurrence_rearranged i)
          _ = (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              (Finset.range (n + 1)).sum
                (fun k => alpha k * (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            simp [Finset.sum_add_distrib]
          _ ≤ (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              (Finset.range (n + 1)).sum
                (fun k => alpha0 * posPart (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            have hsum_le :
                (Finset.range (n + 1)).sum
                    (fun k => alpha k * (φ xbar k - φ xbar (k - 1))) ≤
                  (Finset.range (n + 1)).sum
                    (fun k => alpha0 * posPart (φ xbar k - φ xbar (k - 1))) :=
              Finset.sum_le_sum (fun i _hi => halpha_theta_bound i)
            nlinarith
          _ = (Finset.range (n + 1)).sum (fun k => φ xbar k - φ xbar (k + 1)) +
              alpha0 * (Finset.range (n + 1)).sum
                (fun k => posPart (φ xbar k - φ xbar (k - 1))) +
              (Finset.range (n + 1)).sum (δ xbar) := by
            simp [Finset.mul_sum]
      have htelescope (n : ℕ) :
          (Finset.range (n + 1)).sum (fun k : ℕ => φ xbar k - φ xbar (k + 1)) =
            φ xbar 0 - φ xbar (n + 1) := by
        induction' n with m ih
        · simp
        · rw [Finset.sum_range_succ, ih]
          ring
      have hphi_nonneg : ∀ k : ℕ, 0 ≤ φ xbar k := by
        intro k
        dsimp [φ]
        positivity
      have hdelta_nonneg : ∀ k : ℕ, 0 ≤ δ xbar k := by
        intro k
        dsimp [δ]
        have ha0 : 0 ≤ alpha k := (halpha_mem k).1
        have hlam0 : 0 ≤ lam k := le_of_lt (hlam_pos k)
        positivity
      have hgamma_bound_total (n : ℕ) :
          (Finset.range (n + 1)).sum gamma_seq ≤
            φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
              ∑' k, δ xbar k := by
        have hpartial := hgamma_bound_partial n
        rw [htelescope n] at hpartial
        have hpospart_le :
            (Finset.range (n + 1)).sum
                (fun k => posPart (φ xbar k - φ xbar (k - 1))) ≤
              ∑' k, posPart (φ xbar k - φ xbar (k - 1)) :=
          (h_lemma23_concl xbar hxbar).1.sum_le_tsum (Finset.range (n + 1))
            (fun i _hi => by dsimp [posPart]; exact le_max_right _ _)
        have hdelta_le :
            (Finset.range (n + 1)).sum (δ xbar) ≤ ∑' k, δ xbar k :=
          (hdelta_summable xbar hxbar).sum_le_tsum (Finset.range (n + 1))
            (fun i _hi => hdelta_nonneg i)
        have halpha0_nonneg : 0 ≤ alpha0 :=
          le_trans (halpha_bound 0).1 (halpha_bound 0).2
        nlinarith [hphi_nonneg (n + 1)]
      have hbound_for_sum_range_le (n : ℕ) :
          (Finset.range n).sum gamma_seq ≤
            φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
              ∑' k, δ xbar k := by
        cases n with
        | zero =>
            have hC_nonneg :
                0 ≤ φ xbar 0 + alpha0 * ∑' k, posPart (φ xbar k - φ xbar (k - 1)) +
                  ∑' k, δ xbar k := by
              have halpha0_nonneg : 0 ≤ alpha0 :=
                le_trans (halpha_bound 0).1 (halpha_bound 0).2
              have hpos_tsum :
                  0 ≤ ∑' k, posPart (φ xbar k - φ xbar (k - 1)) :=
                tsum_nonneg (fun k => by dsimp [posPart]; exact le_max_right _ _)
              have hdelta_tsum : 0 ≤ ∑' k, δ xbar k :=
                tsum_nonneg hdelta_nonneg
              nlinarith [hphi_nonneg 0]
            simpa using hC_nonneg
        | succ m => simpa using hgamma_bound_total m
      exact summable_of_sum_range_le hgamma_nonneg hbound_for_sum_range_le
    have hcoeff_pos : 0 < R1 * (1 - R2 / 2) := h_rho_factor_pos
    let term : ℕ → ℝ := fun k => (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2
    have hterm_nonneg_all : ∀ k : ℕ, 0 ≤ term k := by
      intro k
      dsimp [term]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hterm_le : ∀ k : ℕ, term k ≤ gamma_seq k / (R1 * (1 - R2 / 2)) := by
      intro k
      dsimp [term]
      have hterm_nonneg :
          0 ≤ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hmul :
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤
            (rho k * (1 - rho k / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (h_rho_lower_bound k) hterm_nonneg
      have hgamma_lower :
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) ≤ gamma_seq k := by
        calc
          (R1 * (1 - R2 / 2)) *
              ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2)
              ≤ (rho k * (1 - rho k / 2)) *
                  ((lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2) := hmul
          _ = gamma_seq k := by
                rw [hgamma_seq_def]
                ring
      exact (le_div_iff₀ hcoeff_pos).mpr
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hgamma_lower)
    have hterm_summable : Summable term :=
      Summable.of_nonneg_of_le hterm_nonneg_all hterm_le
        (hsummable_gamma.div_const (R1 * (1 - R2 / 2)))
    simpa [term] using hterm_summable
  have h_xi_tendsto : Tendsto (fun k : ℕ ↦ xi k) atTop (𝓝 (0 : H)) := by
    have hxi_sq_summable : Summable fun k : ℕ ↦ ‖xi k‖ ^ 2 := by
      have h_eq :
          (fun k : ℕ ↦ ‖xi k‖ ^ 2) =
            fun k : ℕ ↦ (lam k) ^ 2 * ‖A_lam_sv k (y k)‖ ^ 2 := by
        funext k
        rw [h_xi_eq_lam_A_lam k, norm_smul, Real.norm_eq_abs,
          abs_of_pos (hlam_pos k)]
        ring
      simpa [h_eq] using h_yosida_sq_summable
    have hsq_tendsto :
        Tendsto (fun k : ℕ ↦ ‖xi k‖ ^ 2) atTop (𝓝 0) :=
      hxi_sq_summable.tendsto_atTop_zero
    have hsqrt :
        Tendsto (fun k : ℕ ↦ Real.sqrt (‖xi k‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto
    have hnorm_tendsto : Tendsto (fun k : ℕ ↦ ‖xi k‖) atTop (𝓝 0) := by
      have h_eq :
          (fun k : ℕ ↦ Real.sqrt (‖xi k‖ ^ 2)) = fun k : ℕ ↦ ‖xi k‖ := by
        funext k
        simp
      simpa [h_eq] using hsqrt
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
  have hv_tendsto : Tendsto (fun k : ℕ ↦ v k) atTop (𝓝 (0 : H)) := by
    rcases hlam_lower with ⟨lam0, hlam0_pos, hlam0_le⟩
    have hstep_scaled_tendsto :
        Tendsto (fun k : ℕ ↦ (lam k)⁻¹ • (x (k + 1) - y k)) atTop
          (𝓝 (0 : H)) := by
      have hnorm_bound (k : ℕ) :
          ‖(lam k)⁻¹ • (x (k + 1) - y k)‖ ≤
            ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖ := by
        have hwy_bound : ‖w k - y k‖ ≤ R2 * ‖xi k‖ := by
          have hwy_eq : ‖w k - y k‖ = rho k * ‖xi k‖ := by
            rw [h_w_eq_y_sub_rho_xi k]
            have hvec : y k - rho k • xi k - y k = -rho k • xi k := by
              module
            rw [hvec, norm_smul, Real.norm_eq_abs]
            simp [abs_of_pos (hrho_pos k)]
          rw [hwy_eq]
          exact mul_le_mul_of_nonneg_right (hR2_le k) (norm_nonneg _)
        have hstep_bound :
            ‖x (k + 1) - y k‖ ≤ lam k * ‖eta k‖ + R2 * ‖xi k‖ := by
          have hdecomp :
              x (k + 1) - y k = (x (k + 1) - w k) + (w k - y k) := by
            module
          calc
            ‖x (k + 1) - y k‖
                = ‖(x (k + 1) - w k) + (w k - y k)‖ := by rw [hdecomp]
            _ ≤ ‖x (k + 1) - w k‖ + ‖w k - y k‖ := norm_add_le _ _
            _ ≤ lam k * ‖eta k‖ + R2 * ‖xi k‖ := add_le_add (h35 k) hwy_bound
        have hinv_nonneg : 0 ≤ (lam k)⁻¹ := le_of_lt (inv_pos.mpr (hlam_pos k))
        have hinv_le : (lam k)⁻¹ ≤ lam0⁻¹ :=
          (inv_le_inv₀ (hlam_pos k) hlam0_pos).mpr (hlam0_le k)
        calc
          ‖(lam k)⁻¹ • (x (k + 1) - y k)‖
              = (lam k)⁻¹ * ‖x (k + 1) - y k‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam_pos k))]
          _ ≤ (lam k)⁻¹ * (lam k * ‖eta k‖ + R2 * ‖xi k‖) :=
                mul_le_mul_of_nonneg_left hstep_bound hinv_nonneg
          _ = ‖eta k‖ + ((lam k)⁻¹ * R2) * ‖xi k‖ := by
                field_simp [hlam_ne_zero k]
          _ ≤ ‖eta k‖ + (lam0⁻¹ * R2) * ‖xi k‖ := by
                have hcoef : (lam k)⁻¹ * R2 ≤ lam0⁻¹ * R2 :=
                  mul_le_mul_of_nonneg_right hinv_le (le_of_lt hR2_pos)
                have hmul :=
                  mul_le_mul_of_nonneg_right hcoef (norm_nonneg (xi k))
                nlinarith
          _ = ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖ := by ring
      have hnorm_tendsto :
          Tendsto (fun k : ℕ ↦ ‖(lam k)⁻¹ • (x (k + 1) - y k)‖) atTop
            (𝓝 0) := by
        have hright :
            Tendsto (fun k : ℕ ↦ ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖) atTop
              (𝓝 (0 + (R2 * lam0⁻¹) * 0)) :=
          h_eta_tendsto_zero.add
            ((tendsto_zero_iff_norm_tendsto_zero.mp h_xi_tendsto).const_mul
              (R2 * lam0⁻¹))
        have hright0 :
            Tendsto (fun k : ℕ ↦ ‖eta k‖ + (R2 * lam0⁻¹) * ‖xi k‖) atTop
              (𝓝 0) := by
          simpa using hright
        exact squeeze_zero (fun k => norm_nonneg _) hnorm_bound hright0
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
    have hv_eq (k : ℕ) : v k = eta k - (lam k)⁻¹ • (x (k + 1) - y k) := by
      rw [← rec.equation k]
      module
    have hdiff := h_eta_tendsto_zero_vec.sub hstep_scaled_tendsto
    have h_eq :
        (fun k : ℕ ↦ eta k - (lam k)⁻¹ • (x (k + 1) - y k)) =
          fun k : ℕ ↦ v k := by
      funext k
      exact (hv_eq k).symm
    simpa [h_eq] using hdiff
  have h_weak_cluster_condition :
      ∀ xhat : H, ∀ subseq : ℕ → ℕ, StrictMono subseq →
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (x (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) →
        xhat ∈ SetValuedOperator.zeros A := by
    intro xhat subseq hstrict hweak_subseq
    have hcont_toWeak : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
    have hsubseq_atTop : Tendsto subseq atTop atTop := hstrict.tendsto_atTop
    have h_inertial_tendsto :
        Tendsto (fun k : ℕ ↦ alpha k • (x k - x (k - 1))) atTop (𝓝 (0 : H)) := by
      have h_norm :
          Tendsto (fun k : ℕ ↦ ‖alpha k • (x k - x (k - 1))‖) atTop (𝓝 0) := by
        have h_eq :
            (fun k : ℕ ↦ ‖alpha k • (x k - x (k - 1))‖) =
              (fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖) := by
          funext k
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (halpha_mem k).1]
        rw [h_eq]
        exact h_alpha_diff_norm_tendsto_zero
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h_norm
    have hy_weak :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (y (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
      have h_inertial_subseq :
          Tendsto (fun j : ℕ ↦ alpha (subseq j) •
            (x (subseq j) - x (subseq j - 1))) atTop (𝓝 (0 : H)) :=
        h_inertial_tendsto.comp hsubseq_atTop
      have h_inertial_weak :
          Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H
              (alpha (subseq j) • (x (subseq j) - x (subseq j - 1)))) atTop
            (𝓝 (toWeakSpace ℝ H (0 : H))) :=
        (hcont_toWeak.tendsto (0 : H)).comp h_inertial_subseq
      have hsum := hweak_subseq.add h_inertial_weak
      have h_eq :
          (fun j : ℕ =>
              toWeakSpace ℝ H (x (subseq j)) +
                toWeakSpace ℝ H
                  (alpha (subseq j) • (x (subseq j) - x (subseq j - 1)))) =
            (fun j : ℕ => toWeakSpace ℝ H (y (subseq j))) := by
        funext j
        rw [rec.y_def (subseq j)]
        simp
      rw [h_eq] at hsum
      simpa using hsum
    have hy_minus_xi_weak :
        Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (y (subseq j) - xi (subseq j))) atTop
          (𝓝 (toWeakSpace ℝ H xhat)) := by
      have h_xi_subseq : Tendsto (fun j : ℕ ↦ xi (subseq j)) atTop (𝓝 (0 : H)) :=
        h_xi_tendsto.comp hsubseq_atTop
      have h_xi_weak :
          Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (xi (subseq j))) atTop
            (𝓝 (toWeakSpace ℝ H (0 : H))) :=
        (hcont_toWeak.tendsto (0 : H)).comp h_xi_subseq
      have hdiff := hy_weak.sub h_xi_weak
      simpa using hdiff
    have h_scaled_xi_tendsto :
        Tendsto (fun j : ℕ ↦ (lam (subseq j))⁻¹ • xi (subseq j)) atTop
          (𝓝 (0 : H)) := by
      rcases hlam_lower with ⟨lam0, hlam0_pos, hlam0_le⟩
      have hnorm_bound (j : ℕ) :
          ‖(lam (subseq j))⁻¹ • xi (subseq j)‖ ≤ lam0⁻¹ * ‖xi (subseq j)‖ := by
        have hlam_subseq_pos : 0 < lam (subseq j) := hlam_pos (subseq j)
        calc
          ‖(lam (subseq j))⁻¹ • xi (subseq j)‖ =
              (lam (subseq j))⁻¹ * ‖xi (subseq j)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam_subseq_pos)]
          _ ≤ lam0⁻¹ * ‖xi (subseq j)‖ :=
            mul_le_mul_of_nonneg_right
              ((inv_le_inv₀ hlam_subseq_pos hlam0_pos).mpr (hlam0_le (subseq j)))
              (norm_nonneg _)
      have h_xi_norm_tendsto :
          Tendsto (fun j : ℕ ↦ ‖xi (subseq j)‖) atTop (𝓝 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp h_xi_tendsto).comp hsubseq_atTop
      have hnorm_tendsto :
          Tendsto (fun j : ℕ ↦ ‖(lam (subseq j))⁻¹ • xi (subseq j)‖) atTop
            (𝓝 0) :=
        squeeze_zero (fun j => norm_nonneg _) hnorm_bound
          (by simpa using h_xi_norm_tendsto.const_mul lam0⁻¹)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
    rw [SetValuedOperator.mem_zeros_iff]
    exact weak_strong_closedness_maximal_monotone_graph A hA
      hy_minus_xi_weak h_scaled_xi_tendsto (fun j => hxi_graph (subseq j))
  have h_weak_conv : ∃ xstar ∈ SetValuedOperator.zeros A,
      Tendsto (fun k : ℕ => toWeakSpace ℝ H (x k)) atTop
        (𝓝 (toWeakSpace ℝ H xstar)) :=
    lemma_2_4_opial x (SetValuedOperator.zeros A) ⟨xbar, hxbar⟩ h_dist_all
      h_weak_cluster_condition
  exact ⟨hv_tendsto, h_weak_conv⟩
```

## Proof explanation
The proof begins with `classical`, which permits classical choice for the nonempty resolvent sets, and then extracts and normalizes the parameter bounds. From `params.lam_lower` and `hlam_eq`, it obtains \(\lambda_0>0\) with \(\lambda_0\le \lambda_k\). Hence every \(\lambda_k\) is positive and nonzero. From `params.alpha_mem` and `halpha_eq`, it obtains \(0\le \alpha_k<1\). From `params.alpha_upper`, it obtains \(\alpha_0<1\) with \(\alpha_k\le \alpha_0\) for all \(k\). From `params.alpha_summable` and `halpha_eq`, it obtains
\[
\sum_k \alpha_k\|x_k-x_{k-1}\|^2<\infty.
\]
Using `inertial_delta_summable_thm2`, this gives
\[
\sum_k \frac{\alpha_k+\alpha_k^2}{2}\|x_k-x_{k-1}\|^2<\infty.
\]
Similarly, from `params.rho_lower` and `params.rho_upper`, together with `hrho_eq`, it obtains \(R_1>0\), \(R_2<2\), and \(R_1\le \rho_k\le R_2\), so all \(\rho_k\) are positive.

Next the proof selects a single-valued resolvent selection. For each \(k\) and each \(z\in H\), the theorem `resolvent_nonempty` says that, because \(A\) is maximal monotone and \(\lambda_k>0\), the resolvent set \(J[(\lambda_k A)]z\) is nonempty. The proof uses `Classical.choose` to define \(J_{\lambda,k}(z)\in J[(\lambda_k A)]z\). It then defines the Yosida-type residual
\[
A_{\lambda,k}(z)=\lambda_k^{-1}\bigl(z-J_{\lambda,k}(z)\bigr),
\]
the relaxed point
\[
w_k=(1-\rho_k)y_k+\rho_k J_{\lambda,k}(y_k),
\]
and
\[
\xi_k=y_k-J_{\lambda,k}(y_k).
\]

The theorem `eta_norm_tendsto_zero` is applied with \(\lambda_k\ge \lambda_0>0\) and \(\sum_k \lambda_k\|\eta_k\|<\infty\); it yields \(\|\eta_k\|\to0\). The proof also shows
\[
R_1\bigl(1-R_2/2\bigr)>0,\qquad
\rho_k(1-\rho_k/2)\ge R_1(1-R_2/2),
\]
which will later turn a \(\rho\)-weighted energy dissipation term into a positive lower bound.

Because \(A^{-1}(0)\) is nonempty, choose \(\bar x\in A^{-1}(0)\). The proof proves summability of \(\sum_k \lambda_k\|\eta_k\|\|y_k-\bar x\|\). It uses the given summability of \(\sum_k \lambda_k\|\eta_k\|\|y_k\|\), the summability of \(\sum_k \|\bar x\|\lambda_k\|\eta_k\|\) obtained from \(\sum_k \lambda_k\|\eta_k\|<\infty\), and the triangle inequality \(\|y_k-\bar x\|\le \|y_k\|+\|\bar x\|\). This controls the error term involving \(\bar x\).

For each \(k\), since \(0\in A\bar x\), the theorem `resolvent_fixed_iff_zero` gives \(\bar x\in J[(\lambda_k A)]\bar x\). The theorem `resolvent_is_at_most_single_valued` says the maximal-monotone resolvent is at most single-valued, so \(J_{\lambda,k}(\bar x)=\bar x\). Hence
\[
A_{\lambda,k}(\bar x)=0.
\]
The theorem `yosida_resolvent_equiv` is applied to the membership \(J_{\lambda,k}(y_k)\in J[(\lambda_k A)]y_k\). It states that if \(y\in J[(\lambda A)]x\) and \(\xi=x-y\), then \(\lambda^{-1}\xi\in A(x-\xi)\). Here this gives
\[
\lambda_k^{-1}\xi_k\in A\bigl(y_k-\xi_k\bigr)=A\bigl(J_{\lambda,k}(y_k)\bigr).
\]
This graph-membership relation is used later in the weak closedness argument.

The proof also applies `alpha_diff_norm_tendsto_zero_thm2` to obtain
\[
\alpha_k\|x_k-x_{k-1}\|\to0,
\]
and `lam_sq_eta_sq_summable_thm2` to obtain
\[
\sum_k \lambda_k^2\|\eta_k\|^2<\infty.
\]
From \(\|\eta_k\|\to0\), it also records the vector limit \(\eta_k\to0\) in \(H\).

The resolvent selection is then shown to be firmly nonexpansive. The theorem `firmly_nonexpansive_resolvent_selection_thm2` uses the monotonicity part \(h_A.1\) of maximal monotonicity, the positivity \(\lambda_k>0\), and the resolvent membership \(J_{\lambda,k}(z)\in J[(\lambda_k A)]z\), and concludes that \(J_{\lambda,k}\) is firmly nonexpansive. By `firmly_nonexpansive_cocoerciveOn_one_thm2`, a firmly nonexpansive map is \(1\)-cocoercive on the whole space. The residual map \(z\mapsto z-J_{\lambda,k}(z)\) is firmly nonexpansive by `firmlyNonexpansiveOn_residualMap_iff`, and hence is \(1\)-cocoercive by `firmly_nonexpansiveOn_cocoerciveOn_one_thm2`. Finally, `scaled_residual_cocoercive_thm2` gives, for all \(z_1,z_2\in H\),
\[
\lambda_k\|A_{\lambda,k}(z_1)-A_{\lambda,k}(z_2)\|^2
\le \langle A_{\lambda,k}(z_1)-A_{\lambda,k}(z_2),\,z_1-z_2\rangle.
\]
This is the cocoercivity inequality for \(A_{\lambda,k}\).

The inertial expansion is supplied by `inertial_expansion_y_thm2`, using \(y_k=x_k+\alpha_k(x_k-x_{k-1})\) from `rec.y_def`. For every \(\bar x'\in H\),
\[
\frac12\|y_k-\bar x'\|^2
=
\frac12\|x_k-\bar x'\|^2
+\alpha_k\left(\frac12\|x_k-\bar x'\|^2-\frac12\|x_{k-1}-\bar x'\|^2\right)
+\frac{\alpha_k+\alpha_k^2}{2}\|x_k-x_{k-1}\|^2.
\]
The proof defines
\[
\phi(\bar x',k)=\frac12\|x_k-\bar x'\|^2
\]
and
\[
\delta(\bar x',k)
=
\frac{\alpha_k+\alpha_k^2}{2}\|x_k-x_{k-1}\|^2
+\lambda_k\|\eta_k\|\|y_k-\bar x'\|
+\frac{\lambda_k^2}{2}\|\eta_k\|^2.
\]

The proof then establishes the estimate
\[
\|x_{k+1}-w_k\|\le \lambda_k\|\eta_k\|.
\]
For this, it uses `rec.inclusion` after rewriting membership in the scalar multiple of a set: there are \(a_k\in A(z_k)\) with
\[
z_k=\rho_k^{-1}x_{k+1}+(1-\rho_k^{-1})y_k
\]
and \(v_k=\rho_k a_k\). Using `rec.equation`, it obtains
\[
\eta_k=\lambda_k^{-1}(x_{k+1}-y_k)+\rho_k a_k.
\]
It then verifies that
\[
y_k+\frac{\lambda_k}{\rho_k}\eta_k-z_k=\lambda_k a_k,
\]
so \(z_k\in J[(\lambda_k A)](y_k+(\lambda_k/\rho_k)\eta_k)\). Since the resolvent is at most single-valued, this identifies
\[
J_{\lambda,k}\left(y_k+\frac{\lambda_k}{\rho_k}\eta_k\right)
=
\rho_k^{-1}x_{k+1}+(1-\rho_k^{-1})y_k.
\]
After rearranging,
\[
x_{k+1}
=
(1-\rho_k)y_k
+\rho_k J_{\lambda,k}\left(y_k+\frac{\lambda_k}{\rho_k}\eta_k\right).
\]
Subtracting
\[
w_k=(1-\rho_k)y_k+\rho_k J_{\lambda,k}(y_k)
\]
gives
\[
x_{k+1}-w_k
=
\rho_k\left(
J_{\lambda,k}\left(y_k+\frac{\lambda_k}{\rho_k}\eta_k\right)
-J_{\lambda,k}(y_k)
\right).
\]
By `resolvent_selection_lipschitz`, the selection \(J_{\lambda,k}\) is \(1\)-Lipschitz, so
\[
\|x_{k+1}-w_k\|
\le
\rho_k\left\|\frac{\lambda_k}{\rho_k}\eta_k\right\|
=
\lambda_k\|\eta_k\|.
\]

The proof uses the quadratic identity
\[
\|a-c b\|^2=\|a\|^2-2c\langle a,b\rangle+c^2\|b\|^2.
\]
With \(A_{\lambda,k}(\bar x')=0\), obtained from `yosida_selection_eq_zero_iff_thm2` and \(\bar x'\in A^{-1}(0)\), it expands
\[
w_k-\bar x'
=
(y_k-\bar x')-(\lambda_k\rho_k)A_{\lambda,k}(y_k).
\]
The cocoercivity inequality for \(A_{\lambda,k}\) gives
\[
\lambda_k\|A_{\lambda,k}(y_k)\|^2
\le
\langle A_{\lambda,k}(y_k),\,y_k-\bar x'\rangle.
\]
This yields the one-step dissipation estimate
\[
\frac12\|w_k-\bar x'\|^2
\le
\frac12\|y_k-\bar x'\|^2
-
\lambda_k^2\rho_k\left(1-\frac{\rho_k}{2}\right)
\|A_{\lambda,k}(y_k)\|^2.
\]

Next the proof decomposes
\[
x_{k+1}-\bar x'=(w_k-\bar x')+(x_{k+1}-w_k)
\]
and uses the elementary squared triangle estimate
\[
\frac12\|a+b\|^2
\le
\frac12\|a\|^2+\|a\|\|b\|+\frac12\|b\|^2.
\]
Combining this with \(\|x_{k+1}-w_k\|\le \lambda_k\|\eta_k\|\) and the previous dissipation estimate gives
\[
\frac12\|x_{k+1}-\bar x'\|^2
\le
\frac12\|y_k-\bar x'\|^2
-
\lambda_k^2\rho_k\left(1-\frac{\rho_k}{2}\right)
\|A_{\lambda,k}(y_k)\|^2
+\lambda_k\|\eta_k\|\|y_k-\bar x'\|
+\frac{\lambda_k^2}{2}\|\eta_k\|^2.
\]
Substituting the inertial expansion for \(\frac12\|y_k-\bar x'\|^2\) gives the recurrence
\[
\phi(\bar x',k+1)
\le
\phi(\bar x',k)
+\alpha_k\bigl(\phi(\bar x',k)-\phi(\bar x',k-1)\bigr)
+\delta(\bar x',k)
-
\lambda_k^2\rho_k\left(1-\frac{\rho_k}{2}\right)
\|A_{\lambda,k}(y_k)\|^2.
\]
This is the main energy inequality.

The proof then shows that \(\delta(\bar x')\) is summable for each \(\bar x'\in A^{-1}(0)\). The inertial part is summable by `inertial_delta_summable_thm2`; the middle term \(\lambda_k\|\eta_k\|\|y_k-\bar x'\|\) is summable by the earlier triangle-inequality argument; and the last term \(\frac{\lambda_k^2}{2}\|\eta_k\|^2\) is summable by `lam_sq_eta_sq_summable_thm2`.

Now `lemma_2_3` is applied to \(\phi(\bar x')\) and \(\delta(\bar x')\) with \(\alpha_k\) and the upper bound \(\alpha_0<1\). Its hypotheses are that \(\phi\) and \(\delta\) are nonnegative, that the recurrence above holds, that \(\delta\) is summable, and that \(0\le \alpha_k\le \alpha_0<1\). Its conclusion is
\[
\sum_k \operatorname{posPart}\bigl(\phi(\bar x',k)-\phi(\bar x',k-1)\bigr)<\infty
\]
and there is \(\phi_\star\ge 0\) with
\[
\phi(\bar x',k)\to \phi_\star.
\]
Here \(\operatorname{posPart}(t)=\max(t,0)\). Since \(\phi(\bar x',k)=\frac12\|x_k-\bar x'\|^2\), this implies
\[
\|x_k-\bar x'\|^2\to 2\phi_\star,
\]
and by continuity of the square root,
\[
\|x_k-\bar x'\|\to \sqrt{2\phi_\star}.
\]
Thus, for every zero \(\bar x'\) of \(A\), the distance from \(x_k\) to \(\bar x'\) converges. This is the distance-convergence hypothesis needed for the Opial lemma.

The proof next establishes summability of the Yosida residual. Let
\[
\gamma_k
=
\lambda_k^2\rho_k\left(1-\frac{\rho_k}{2}\right)
\|A_{\lambda,k}(y_k)\|^2.
\]
From the main energy inequality, rearranged, and from the summability of the positive part of \(\phi(\bar x,k)-\phi(\bar x,k-1)\) and of \(\delta(\bar x)\), the proof shows \(\sum_k \gamma_k<\infty\). Since
\[
\rho_k\left(1-\frac{\rho_k}{2}\right)\ge R_1(1-R_2/2)>0,
\]
it follows that
\[
\sum_k \lambda_k^2\|A_{\lambda,k}(y_k)\|^2<\infty.
\]
Because \(\xi_k=\lambda_k A_{\lambda,k}(y_k)\), this says
\[
\sum_k \|\xi_k\|^2<\infty.
\]
A summable nonnegative square-summand sequence tends to zero, and hence
\[
\xi_k\to 0.
\]

The strong convergence of \(v_k\) is then deduced. The proof bounds
\[
\|\lambda_k^{-1}(x_{k+1}-y_k)\|
\le
\|\eta_k\|+\frac{R_2}{\lambda_0}\|\xi_k\|.
\]
Indeed, \(x_{k+1}-y_k=(x_{k+1}-w_k)+(w_k-y_k)\); the first term is controlled by \(\|x_{k+1}-w_k\|\le \lambda_k\|\eta_k\|\), and \(w_k-y_k=-\rho_k\xi_k\), whose norm is at most \(R_2\|\xi_k\|\). Multiplying by \(\lambda_k^{-1}\le \lambda_0^{-1}\) gives the displayed inequality. Since \(\|\eta_k\|\to0\) and \(\|\xi_k\|\to0\), the norm of \(\lambda_k^{-1}(x_{k+1}-y_k)\) tends to \(0\); a squeeze argument using `squeeze_zero` gives
\[
\lambda_k^{-1}(x_{k+1}-y_k)\to 0.
\]
The recurrence equation gives
\[
v_k=\eta_k-\lambda_k^{-1}(x_{k+1}-y_k),
\]
and both terms tend to \(0\), so
\[
v_k\to 0
\]
strongly.

It remains to prove weak convergence. The proof verifies the weak cluster condition needed by the Opial lemma. Suppose a subsequence \(x_{m_j}\) converges weakly to \(\hat x\). The inertial term satisfies
\[
\alpha_k(x_k-x_{k-1})\to0
\]
strongly, because its norm is \(\alpha_k\|x_k-x_{k-1}\|\to0\) by `alpha_diff_norm_tendsto_zero_thm2`. Since
\[
y_k=x_k+\alpha_k(x_k-x_{k-1}),
\]
the subsequence \(y_{m_j}\) also converges weakly to \(\hat x\). Since \(\xi_k\to0\) strongly, the sequence
\[
y_{m_j}-\xi_{m_j}
\]
converges weakly to \(\hat x\). Also, because \(\lambda_k\ge \lambda_0>0\) and \(\xi_k\to0\), the sequence
\[
\lambda_{m_j}^{-1}\xi_{m_j}
\]
converges strongly to \(0\). The earlier graph inclusion
\[
\lambda_k^{-1}\xi_k\in A(y_k-\xi_k)
\]
was obtained from `yosida_resolvent_equiv`. Now `weak_strong_closedness_maximal_monotone_graph` is applied to the weak limit \(\hat x\) of \(y_{m_j}-\xi_{m_j}\), the strong limit \(0\) of \(\lambda_{m_j}^{-1}\xi_{m_j}\), and the membership \(\lambda_{m_j}^{-1}\xi_{m_j}\in A(y_{m_j}-\xi_{m_j})\). It concludes
\[
0\in A\hat x,
\]
that is, \(\hat x\in A^{-1}(0)\). Thus every weak subsequential limit of \(x_k\) lies in the zero set of \(A\).

Finally, the Opial-type theorem `lemma_2_4_opial` is applied with \(S=A^{-1}(0)\). The set \(S\) is nonempty by `hS`; for every \(\bar x'\in S\), the distances \(\|x_k-\bar x'\|\) converge; and every weak cluster point of \(x_k\) lies in \(S\). The theorem concludes that there exists \(x_\star\in S\) such that
\[
x_k\to x_\star
\]
weakly, i.e.
\[
\operatorname{toWeakSpace}_{\mathbb R,H}(x_k)
\to
\operatorname{toWeakSpace}_{\mathbb R,H}(x_\star).
\]
Combining this weak convergence with the already proved strong convergence \(v_k\to0\) gives the two asserted conclusions.

