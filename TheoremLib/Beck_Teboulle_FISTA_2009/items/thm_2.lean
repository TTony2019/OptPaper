import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Sqrt
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_3
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_4
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_6
import TheoremLib.Beck_Teboulle_FISTA_2009.items.algo_1
import TheoremLib.Beck_Teboulle_FISTA_2009.items.algo_2

open Set
open scoped RealInnerProductSpace

set_option maxHeartbeats 400000

/-- Internal rate lemma for an accepted FISTA stepsize sequence.

The public Theorem 4.1 entry points are the two mode-specific rate lemmas below
and the unified `fista_convergence_rate` at the end.  The algorithm objects
record the global choice of mode, including the backtracking `IsLeast` condition. -/
private theorem fista_convergence_rate_of_steps {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf α : ℝ} (hP : ProblemP f g Lf)
    (xSeq ySeq : ℕ → EuclideanSpace ℝ (Fin n))
    (tSeq LSeq : ℕ → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : xSeq 0 = x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (h_alpha_ge_one : 1 ≤ α)
    (hFISTA : ∀ (k : ℕ) (_hk : 1 ≤ k),
      0 < LSeq k ∧
      IsProxPoint f g (LSeq k) (ySeq k) (xSeq k) ∧
      compositeObjective f g (xSeq k) ≤
        quadraticApprox f g (LSeq k) (xSeq k) (ySeq k) ∧
      tSeq (k + 1) = (1 + Real.sqrt (1 + 4 * (tSeq k) ^ 2)) / 2 ∧
      ySeq (k + 1) = xSeq k +
        ((tSeq k - 1) / tSeq (k + 1)) • (xSeq k - xSeq (k - 1)) ∧
      LSeq k ≤ LSeq (k + 1) ∧
      LSeq k ≤ α * Lf)
    (t1 : tSeq 1 = 1) (y1 : ySeq 1 = xSeq 0) (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (xSeq k) - compositeObjective f g xStar ≤
      (2 * α * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2) := by
  have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
  let v (m : ℕ) := compositeObjective f g (xSeq m) - compositeObjective f g xStar
  let u (m : ℕ) := (tSeq m) • (xSeq m) - ((tSeq m - 1) • (xSeq (m - 1))) - xStar
  -- Construct the lem_4-compatible hFISTA from this theorem's hFISTA.
  -- We need properties at both k' and k'+1 indices.
  have hFISTA_lem4 : ∀ (k' : ℕ) (hk' : 1 ≤ k'),
      0 < LSeq (k' + 1) ∧
      IsProxPoint f g (LSeq (k' + 1)) (ySeq (k' + 1)) (xSeq (k' + 1)) ∧
      compositeObjective f g (xSeq (k' + 1)) ≤
        quadraticApprox f g (LSeq (k' + 1)) (xSeq (k' + 1)) (ySeq (k' + 1)) ∧
      tSeq (k' + 1) = (1 + Real.sqrt (1 + 4 * (tSeq k') ^ 2)) / 2 ∧
      ySeq (k' + 1) = xSeq k' +
        ((tSeq k' - 1) / tSeq (k' + 1)) • (xSeq k' - xSeq (k' - 1)) ∧
      LSeq k' ≤ LSeq (k' + 1) := by
    intro k' hk'
    have hk1 : 1 ≤ k' + 1 := by omega
    rcases hFISTA (k' + 1) hk1 with ⟨hp, hpx, hdesc, _, _, _, _⟩
    rcases hFISTA k' hk' with ⟨_, _, _, ht, hy, hm, _⟩
    exact ⟨hp, hpx, hdesc, ht, hy, hm⟩
  have hLseq1_pos : 0 < LSeq 1 := (hFISTA 1 (by omega)).1
  -- The proof from the paper (Beck-Teboulle 2009, Theorem 4.1):
  -- Define a_k = (2/L_k)·t_k²·v_k, b_k = ‖u_k‖², c = ‖x₀ - x*‖²
  -- Lemma 4.1 → a_k - a_{k+1} ≥ b_{k+1} - b_k for k ≥ 1
  -- Telescoping sum: a_1 - a_k ≥ b_k - b_1  →  a_k ≤ a_1 + b_1  (since b_k ≥ 0)
  -- Base case: a₁ + b₁ ≤ c via Lemma 2.3 at (x*, y₁, x₁)
  -- Lemma 4.3: t_k ≥ (k+1)/2  →  t_k² ≥ (k+1)²/4
  -- From a_k ≤ c: v_k ≤ (L_k·c)/(2·t_k²) ≤ (α·Lf·c)·2/(k+1)²
  set a := fun (m : ℕ) => (2 / LSeq m) * (tSeq m) ^ 2 * v m with ha
  set b := fun (m : ℕ) => ‖u m‖ ^ 2 with hb
  set c := ‖x0 - xStar‖ ^ 2 with hc
  -- Lemma 4.1: recursive relation a_k - a_{k+1} ≥ b_{k+1} - b_k for k ≥ 1
  have h_rec (k' : ℕ) (hk' : 1 ≤ k') : a k' - a (k' + 1) ≥ b (k' + 1) - b k' := by
    have h := fista_recursive_relation hP xSeq ySeq tSeq LSeq xStar hxStar
      hFISTA_lem4 hLseq1_pos t1 y1 k' hk'
    dsimp [a, b, v, u]
    exact h
  -- Telescoping: a_1 - a_k ≥ b_k - b_1 for all k ≥ 1
  have h_telescope (k' : ℕ) (hk' : 1 ≤ k') : a 1 - a k' ≥ b k' - b 1 := by
    refine Nat.le_induction ?base ?step k' hk'
    · dsimp [a, b]; linarith
    · intro m hm ih
      have h_rec_m := h_rec m hm
      linarith
  -- Therefore a_k ≤ a_1 + b_1 - b_k ≤ a_1 + b_1 (since b_k = ‖u_k‖² ≥ 0)
  have h_ak_bound (k' : ℕ) (hk' : 1 ≤ k') : a k' ≤ a 1 + b 1 := by
    have h := h_telescope k' hk'
    have hb_nonneg : 0 ≤ b k' := by dsimp [b]; positivity
    linarith
  -- Base case: a₁ + b₁ ≤ c = ‖x₀ - x*‖² via Lemma 2.3 at (x*, y₁, x₁)
  have h_base : a 1 + b 1 ≤ c := by
    rcases hFISTA 1 (by omega) with ⟨hLpos1, hprox1, h_desc1, _, _, _, _⟩
    have h_cond1 : compositeObjective f g (xSeq 1) ≤
        quadraticApprox f g (LSeq 1) (xSeq 1) (ySeq 1) := by
      exact h_desc1
    have h_key := key_inequality' hP hLpos1 (ySeq 1) xStar (xSeq 1) hprox1 h_cond1
    -- h_key: F(x*) - F(x₁) ≥ L₁/2·‖x₁-y₁‖² + L₁·⟨y₁-x*, x₁-y₁⟩
    -- Identity: ‖z-y‖² + 2⟨y-x, z-y⟩ = ‖x-z‖² - ‖x-y‖²
    have h_norm_eq : (LSeq 1 / 2) * ‖xSeq 1 - ySeq 1‖ ^ 2 +
        LSeq 1 * ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫ =
        (LSeq 1 / 2) * (‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2) := by
      have key : ‖xSeq 1 - ySeq 1‖ ^ 2 + 2 * ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫ =
          ‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2 := by
        calc
          ‖xSeq 1 - ySeq 1‖ ^ 2 + 2 * ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫
              = ‖xSeq 1 - ySeq 1‖ ^ 2 - 2 * ⟪xSeq 1 - ySeq 1, xStar - ySeq 1⟫ := by
            have h_inner : ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫ =
                -⟪xSeq 1 - ySeq 1, xStar - ySeq 1⟫ := by
              calc
                ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫
                    = ⟪-(xStar - ySeq 1), xSeq 1 - ySeq 1⟫ := by
                  have h : ySeq 1 - xStar = -(xStar - ySeq 1) := by abel
                  rw [h]
                _ = -⟪xStar - ySeq 1, xSeq 1 - ySeq 1⟫ := by
                  rw [inner_neg_left]
                _ = -⟪xSeq 1 - ySeq 1, xStar - ySeq 1⟫ := by
                  rw [real_inner_comm (xStar - ySeq 1)]
            rw [h_inner]
            ring
          _ = ‖xSeq 1 - xStar‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2 := by
            have h := norm_sub_sq_real (xSeq 1 - ySeq 1) (xStar - ySeq 1)
            have h_diff : (xSeq 1 - ySeq 1) - (xStar - ySeq 1) = xSeq 1 - xStar := by abel
            rw [h_diff] at h
            linarith
          _ = ‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2 := by
            rw [norm_sub_rev (xSeq 1) (xStar)]
      nlinarith
    have h_rearr : (2 / LSeq 1) * (compositeObjective f g xStar - compositeObjective f g (xSeq 1)) ≥
        ‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2 := by
      calc
        (2 / LSeq 1) * (compositeObjective f g xStar - compositeObjective f g (xSeq 1))
            ≥ (2 / LSeq 1) * ((LSeq 1 / 2) * ‖xSeq 1 - ySeq 1‖ ^ 2 + LSeq 1 * ⟪ySeq 1 - xStar, xSeq 1 - ySeq 1⟫) := by
          refine mul_le_mul_of_nonneg_left h_key ?_
          positivity
        _ = (2 / LSeq 1) * ((LSeq 1 / 2) * (‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2)) := by
          rw [h_norm_eq]
        _ = ‖xStar - xSeq 1‖ ^ 2 - ‖xStar - ySeq 1‖ ^ 2 := by
          field_simp [show LSeq 1 ≠ 0 from by linarith]
    -- Now rewrite: a_1 = (2/LSeq 1)*1²*v_1, b_1 = ‖u_1‖²
    dsimp [a, b, u, v, c]
    rw [t1]
    have h_simp : (1 : ℝ) • xSeq 1 - ((1 : ℝ) - 1) • xSeq 0 - xStar = xSeq 1 - xStar := by
      simp
    rw [h_simp]
    have h_one_sq : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [h_one_sq, mul_one]
    rw [y1, hx0] at h_rearr
    have h_norm_sq_symm1 : ‖xStar - xSeq 1‖ ^ 2 = ‖xSeq 1 - xStar‖ ^ 2 := by
      rw [norm_sub_rev (xSeq 1) (xStar)]
    have h_norm_sq_symm0 : ‖xStar - x0‖ ^ 2 = ‖x0 - xStar‖ ^ 2 := by
      rw [norm_sub_rev x0 xStar]
    rw [h_norm_sq_symm1, h_norm_sq_symm0] at h_rearr
    linarith
  -- Combine: a_k ≤ c for all k ≥ 1
  have hak_le_c (k' : ℕ) (hk' : 1 ≤ k') : a k' ≤ c := by
    have := h_ak_bound k' hk'
    linarith
  -- t_k ≥ (k+1)/2 for k ≥ 1 (same as Lemma 4.3)
  have ht_lower (m : ℕ) (hm : 1 ≤ m) : (tSeq m : ℝ) ≥ ((m : ℝ) + 1) / 2 := by
    let P (n : ℕ) (_h : 1 ≤ n) : Prop := (tSeq n : ℝ) ≥ ((n : ℝ) + 1) / 2
    have hbase : P 1 (by omega) := by
      dsimp [P]; rw [t1]; norm_num
    have hstep : ∀ (n : ℕ) (hn : 1 ≤ n), P n hn → P (n+1) (by omega) := by
      intro n hn ih
      dsimp [P] at ih ⊢
      rcases hFISTA n hn with ⟨_, _, _, htrec, _, _, _⟩
      rw [htrec]
      have h_sq : (tSeq n : ℝ) ≥ ((n : ℝ) + 1) / 2 := ih
      have h_nonneg_t : 0 ≤ tSeq n := by
        have h_nonneg_bound : 0 ≤ ((n : ℝ) + 1) / 2 := by
          have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          positivity
        linarith
      have h_inner : 1 + 4 * ((tSeq n : ℝ) ^ 2) ≥ ((n : ℝ) + 1) ^ 2 := by
        have h_sq_ineq : (tSeq n : ℝ) ^ 2 ≥ (((n : ℝ) + 1) / 2) ^ 2 := by
          have h_nonneg_bound : 0 ≤ ((n : ℝ) + 1) / 2 := by
            have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
            positivity
          gcongr
        nlinarith
      have h_nonneg_n : 0 ≤ (n : ℝ) + 1 := by
        have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        linarith
      have h_sqrt : Real.sqrt (1 + 4 * ((tSeq n : ℝ) ^ 2)) ≥ (n : ℝ) + 1 := by
        calc
          Real.sqrt (1 + 4 * ((tSeq n : ℝ) ^ 2)) ≥ Real.sqrt (((n : ℝ) + 1) ^ 2) :=
            Real.sqrt_le_sqrt h_inner
          _ = |(n : ℝ) + 1| := by rw [Real.sqrt_sq_eq_abs]
          _ = (n : ℝ) + 1 := abs_of_nonneg h_nonneg_n
      push_cast
      nlinarith
    exact Nat.le_induction hbase hstep m hm
  -- Final bound using hak_le_c, ht_lower, and L_k ≤ α·Lf
  have h_final : compositeObjective f g (xSeq k) - compositeObjective f g xStar ≤
      (2 * α * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2) := by
    rcases hFISTA k hk with ⟨hLkpos, _, _, _, _, _, hLbound⟩
    have h_ak := hak_le_c k hk
    dsimp [a, v, c] at h_ak
    set V := compositeObjective f g (xSeq k) - compositeObjective f g xStar
    set C := ‖x0 - xStar‖ ^ 2
    -- h_ak: (2/LSeq k)*(tSeq k)^2*V ≤ C
    -- Step 1: V ≤ (LSeq k * C) / (2 * (tSeq k)^2)
    have h_vk_mid : V ≤ (LSeq k * C) / (2 * (tSeq k) ^ 2) := by
      have h_tk_sq_pos : 0 < (tSeq k) ^ 2 := by
        have h_tk_pos : 0 < tSeq k := by
          have h_tk_lower := ht_lower k hk
          have : 0 < ((k : ℝ) + 1) / 2 := by
            have hkpos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            positivity
          linarith
        positivity
      have h_mul : V * (2 * (tSeq k) ^ 2) ≤ LSeq k * C := by
        calc
          V * (2 * (tSeq k) ^ 2) = (2 * (tSeq k) ^ 2) * V := by ring
          _ = LSeq k * ((2 / LSeq k) * (tSeq k) ^ 2 * V) := by
            field_simp [hLkpos.ne']
          _ ≤ LSeq k * C := by
            have hX : (2 / LSeq k) * (tSeq k) ^ 2 * V ≤ C := by
              simpa [mul_assoc] using h_ak
            nlinarith
      have denom_pos : 0 < 2 * (tSeq k) ^ 2 := by positivity
      rw [le_div_iff₀ denom_pos]
      exact h_mul
    -- Step 2: (LSeq k * C) / (2 * (tSeq k)^2) ≤ (2 * α * Lf * C) / ((k+1)^2)
    have h_final_bound : (LSeq k * C) / (2 * (tSeq k) ^ 2) ≤
        (2 * α * Lf * C) / (((k : ℝ) + 1) ^ 2) := by
      have h_tk_nonneg : 0 ≤ tSeq k := by
        have h_tk_lower := ht_lower k hk
        have h_nonneg : 0 ≤ ((k : ℝ) + 1) / 2 := by
          have hkpos : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
          positivity
        linarith
      have h_tk_sq_pos : 0 < (tSeq k) ^ 2 := by
        have h_tk_pos : 0 < tSeq k := by
          have h_tk_lower := ht_lower k hk
          have h_pos : 0 < ((k : ℝ) + 1) / 2 := by
            have hkpos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            positivity
          linarith
        positivity
      have h_denom_inv : 1 / (2 * (tSeq k) ^ 2) ≤ 2 / (((k : ℝ) + 1) ^ 2) := by
        have h_tk_lower := ht_lower k hk
        have h_sq_lower : (tSeq k) ^ 2 ≥ (((k : ℝ) + 1) / 2) ^ 2 := by
          have h_nonneg_bound : 0 ≤ ((k : ℝ) + 1) / 2 := by
            have hkpos : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
            positivity
          gcongr
        have h_sq_bound : ((k : ℝ) + 1) ^ 2 ≤ 4 * (tSeq k) ^ 2 := by
          have : (tSeq k) ^ 2 ≥ ((k : ℝ) + 1) ^ 2 / 4 := by
            linarith
          linarith
        have h_pos_4tk2 : 0 < 4 * (tSeq k) ^ 2 := by positivity
        have h_pos_k12 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
        have h_inv : 1 / (4 * (tSeq k) ^ 2) ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          (one_div_le_one_div h_pos_4tk2 h_pos_k12).mpr h_sq_bound
        calc
          1 / (2 * (tSeq k) ^ 2) = 2 * (1 / (4 * (tSeq k) ^ 2)) := by ring
          _ ≤ 2 * (1 / (((k : ℝ) + 1) ^ 2)) := by gcongr
          _ = 2 / (((k : ℝ) + 1) ^ 2) := by ring
      have hC_nonneg : 0 ≤ C := by positivity
      have h_nonneg_αLfC : 0 ≤ α * Lf * C := by
        have h_α_nonneg : 0 ≤ α := by linarith
        have h_Lf_nonneg : 0 ≤ Lf := by linarith
        dsimp [C]
        positivity
      have h_div1 : (LSeq k * C) / (2 * (tSeq k) ^ 2) ≤ (α * Lf * C) / (2 * (tSeq k) ^ 2) := by
        have h_num : LSeq k * C ≤ α * Lf * C := by nlinarith
        have h_denom_nonneg : 0 ≤ (2 * (tSeq k) ^ 2)⁻¹ := by positivity
        calc
          (LSeq k * C) / (2 * (tSeq k) ^ 2) = (LSeq k * C) * (2 * (tSeq k) ^ 2)⁻¹ := rfl
          _ ≤ (α * Lf * C) * (2 * (tSeq k) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right h_num h_denom_nonneg
          _ = (α * Lf * C) / (2 * (tSeq k) ^ 2) := rfl
      have h_div2 : (α * Lf * C) / (2 * (tSeq k) ^ 2) ≤ (2 * α * Lf * C) / (((k : ℝ) + 1) ^ 2) := by
        have h_denom_inv' : (2 * (tSeq k) ^ 2)⁻¹ ≤ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
          simpa [one_div] using h_denom_inv
        calc
          (α * Lf * C) / (2 * (tSeq k) ^ 2) = (α * Lf * C) * (2 * (tSeq k) ^ 2)⁻¹ := rfl
          _ ≤ (α * Lf * C) * (2 * (((k : ℝ) + 1) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h_denom_inv' h_nonneg_αLfC
          _ = (2 * α * Lf * C) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
            simp [mul_comm, mul_left_comm, mul_assoc]
          _ = (2 * α * Lf * C) / (((k : ℝ) + 1) ^ 2) := rfl
      exact h_div1.trans h_div2
    have h_target := h_vk_mid.trans h_final_bound
    dsimp [V, C] at h_target ⊢
    exact h_target
  exact h_final

/-- Theorem 4.1 for FISTA with the constant stepsize `L(f)` (equations (4.1)--(4.3)). -/
theorem fista_constant_stepsize_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTAConstantStepsize f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (2 * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2) := by
  have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
  have h := fista_convergence_rate_of_steps (hP := hP) (xSeq := A.x) (ySeq := A.y)
    (tSeq := A.t) (LSeq := fun _ : ℕ => Lf) (x0 := x0) (hx0 := A.x_zero)
    (xStar := xStar) (hxStar := hxStar) (α := 1)
    (h_alpha_ge_one := by norm_num)
    (hFISTA := by
      intro m hm
      have hprox := A.proximal_step m hm
      have hdesc : compositeObjective f g (A.x m) ≤
          quadraticApprox f g Lf (A.x m) (A.y m) := by
        unfold compositeObjective quadraticApprox
        have hu := quadratic_upper_bound_C11 hP.smooth_f (le_refl Lf) (A.x m) (A.y m)
        linarith
      refine ⟨hLfpos, hprox, hdesc, A.t_update m hm, A.y_update m hm, ?_, ?_⟩
      · simp
      · simp)
    (t1 := A.t_one) (y1 := by simpa [A.x_zero] using A.y_one)
    (k := k) hk
  simpa using h

/-- Theorem 4.1 for FISTA with backtracking (the rule following (4.3)).

`A` records the backtracking rule itself.  The analytical estimate (3.4), namely
`β L(f) ≤ L_k ≤ α L(f)` with `β = L₀/L(f)` and `α = η`, is supplied as `h_bounds`. -/
theorem fista_backtracking_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (h_bounds : BacktrackingStepsizeBounds Lf A.L0 A.eta A.L)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (2 * A.eta * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2) := by
  have h := fista_convergence_rate_of_steps (hP := hP) (xSeq := A.x) (ySeq := A.y)
    (tSeq := A.t) (LSeq := A.L) (x0 := x0) (hx0 := A.x_zero)
    (xStar := xStar) (hxStar := hxStar) (α := A.eta)
    (h_alpha_ge_one := le_of_lt A.eta_gt_one)
    (hFISTA := by
      intro m hm
      refine ⟨A.stepsize_pos m, A.proximal_step m hm,
        A.descent_condition m hm, A.t_update m hm, A.y_update m hm, ?_, ?_⟩
      · have hstep := A.stepsize_non_decreasing (m + 1) (by omega)
        simpa only [Nat.add_sub_cancel] using hstep
      · simpa [backtrackingAlpha] using (h_bounds m hm).2)
    (t1 := A.t_one) (y1 := by simpa [A.x_zero] using A.y_one)
    (k := k) hk
  simpa using h

/-- A global choice of one of the two FISTA algorithms in Theorem 4.1.

This sum type rules out changing between constant and backtracking stepsizes from one
iteration to the next. -/
inductive FISTARun {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  | constant (run : FISTAConstantStepsize f g Lf x0)
  | backtracking (run : FISTABacktracking f g x0)
      (bounds : BacktrackingStepsizeBounds Lf run.L0 run.eta run.L)

namespace FISTARun

def x {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} :
    FISTARun f g Lf x0 → ℕ → EuclideanSpace ℝ (Fin n)
  | .constant run => run.x
  | .backtracking run _ => run.x

def alpha {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} : FISTARun f g Lf x0 → ℝ
  | .constant _ => 1
  | .backtracking run _ => run.eta

end FISTARun

/-- Theorem 4.1, with the paper's global choice between the two FISTA algorithms. -/
theorem fista_convergence_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTARun f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (2 * A.alpha * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2) := by
  cases A with
  | constant run =>
      simpa [FISTARun.x, FISTARun.alpha] using
        fista_constant_stepsize_rate hP run xStar hxStar k hk
  | backtracking run bounds =>
      simpa [FISTARun.x, FISTARun.alpha] using
        fista_backtracking_rate hP run bounds xStar hxStar k hk
