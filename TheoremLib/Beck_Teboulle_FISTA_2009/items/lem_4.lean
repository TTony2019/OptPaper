import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_3

open scoped RealInnerProductSpace

/-- Lemma 4.1: Key recursive relation for FISTA.

The sequences `{x_k}`, `{y_k}` generated via FISTA with either a constant or backtracking
stepsize rule satisfy for every `k ≥ 1`:
`(2/L_k) t_k² v_k - (2/L_{k+1}) t_{k+1}² v_{k+1} ≥ ‖u_{k+1}‖² - ‖u_k‖²`,

where
`v_k := F(x_k) - F(x*)` and
`u_k := t_k x_k - (t_k - 1) x_{k-1} - x*`. -/
theorem fista_recursive_relation {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    (xSeq ySeq : ℕ → EuclideanSpace ℝ (Fin n))
    (tSeq LSeq : ℕ → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (hFISTA : ∀ (k : ℕ) (hk : 1 ≤ k),
      0 < LSeq (k + 1) ∧
      IsProxPoint f g (LSeq (k + 1)) (ySeq (k + 1)) (xSeq (k + 1)) ∧
      compositeObjective f g (xSeq (k + 1)) ≤
        quadraticApprox f g (LSeq (k + 1)) (xSeq (k + 1)) (ySeq (k + 1)) ∧
      tSeq (k + 1) = (1 + Real.sqrt (1 + 4 * (tSeq k) ^ 2)) / 2 ∧
      ySeq (k + 1) = xSeq k +
        ((tSeq k - 1) / tSeq (k + 1)) • (xSeq k - xSeq (k - 1)) ∧
      LSeq k ≤ LSeq (k + 1))
    (hLseq1_pos : 0 < LSeq 1)
    (t1 : tSeq 1 = 1) (y1 : ySeq 1 = xSeq 0) (k : ℕ) (hk : 1 ≤ k) :
    let v (m : ℕ) := compositeObjective f g (xSeq m) -
      compositeObjective f g xStar
    let u (m : ℕ) := (tSeq m) • (xSeq m) -
      ((tSeq m - 1) • (xSeq (m - 1))) - xStar
    (2 / LSeq k) * (tSeq k) ^ 2 * v k -
      (2 / LSeq (k + 1)) * (tSeq (k + 1)) ^ 2 * v (k + 1) ≥
      ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by
  intro v u
  rcases hFISTA k hk with ⟨hLpos, h_prox, h_cond_raw, h_tk1, h_yk1, h_Lk1⟩
  let F (x : EuclideanSpace ℝ (Fin n)) := compositeObjective f g x
  -- The backtracking acceptance test is the descent condition in Lemma 2.3.
  have h_cond : F (xSeq (k + 1)) ≤ quadraticApprox f g (LSeq (k + 1)) (xSeq (k + 1)) (ySeq (k + 1)) := by
    simpa [F] using h_cond_raw
  -- Apply Lemma 2.3 (key_inequality') at two points
  have h_ineq1 : F (xSeq k) - F (xSeq (k + 1)) ≥
      (LSeq (k + 1) / 2) * ‖xSeq (k + 1) - ySeq (k + 1)‖ ^ 2 +
      LSeq (k + 1) * ⟪ySeq (k + 1) - xSeq k, xSeq (k + 1) - ySeq (k + 1)⟫ :=
    key_inequality' hP hLpos (ySeq (k + 1)) (xSeq k) (xSeq (k + 1)) h_prox h_cond
  have h_ineq2 : F xStar - F (xSeq (k + 1)) ≥
      (LSeq (k + 1) / 2) * ‖xSeq (k + 1) - ySeq (k + 1)‖ ^ 2 +
      LSeq (k + 1) * ⟪ySeq (k + 1) - xStar, xSeq (k + 1) - ySeq (k + 1)⟫ :=
    key_inequality' hP hLpos (ySeq (k + 1)) xStar (xSeq (k + 1)) h_prox h_cond
  -- Express v_k - v_{k+1} and -v_{k+1} in terms of F
  have hv_diff : v k - v (k + 1) = F (xSeq k) - F (xSeq (k + 1)) := by dsimp [v, F]; ring
  have hv_neg : -v (k + 1) = F xStar - F (xSeq (k + 1)) := by dsimp [v, F]; ring
  -- Let L := L_{k+1}, t := t_{k+1}, d := x_{k+1} - y_{k+1}
  set L := LSeq (k + 1) with hL
  set t := tSeq (k + 1) with ht
  set d := xSeq (k + 1) - ySeq (k + 1) with hd
  -- v_k ≥ 0 since x* is a minimizer
  have hv_nonneg : ∀ m, 0 ≤ v m := by
    intro m
    dsimp [v]
    have hmin : IsMinOn (compositeObjective f g) Set.univ xStar := by
      simpa [solutionSet] using hxStar
    have hx_mem : xSeq m ∈ Set.univ := Set.mem_univ _
    have h_le : compositeObjective f g xStar ≤ compositeObjective f g (xSeq m) := by
      simpa [IsMinOn, IsMinFilter, Filter.eventually_principal] using hmin hx_mem
    linarith
  -- t_{k+1} ≥ 1 (from the recurrence formula)
  have ht_ge_one : 1 ≤ t := by
    have h_inner : (1 : ℝ) ≤ 1 + 4 * (tSeq k) ^ 2 := by nlinarith
    have h_sqrt_ge_one : 1 ≤ Real.sqrt (1 + 4 * (tSeq k) ^ 2) := by
      calc
        1 = Real.sqrt (1 : ℝ) := by norm_num
        _ ≤ Real.sqrt (1 + 4 * (tSeq k) ^ 2) := Real.sqrt_le_sqrt h_inner
    dsimp [t] at h_tk1; linarith
  -- FISTA t-recurrence: t_k² = t_{k+1}² - t_{k+1}  (paper equation (4.2))
  have h_tsq : (tSeq k) ^ 2 = t ^ 2 - t := by
    have h_nonneg : 0 ≤ 1 + 4 * (tSeq k) ^ 2 := by nlinarith
    have h_sq : (2 * t - 1) ^ 2 = 1 + 4 * (tSeq k) ^ 2 := by
      have h_sqrt_eq : 2 * t - 1 = Real.sqrt (1 + 4 * (tSeq k) ^ 2) := by
        dsimp [t] at h_tk1; linarith
      rw [h_sqrt_eq, Real.sq_sqrt h_nonneg]
    nlinarith
  -- Pythagoras identity: ‖b-a‖² + 2⟨b-a, a-c⟩ = ‖b-c‖² - ‖a-c‖²
  have h_pythagoras (a b c : EuclideanSpace ℝ (Fin n)) :
      ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by
    set w := b - a; set v' := a - c
    have hsum : w + v' = b - c := by dsimp [w, v']; abel
    calc
      ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ = ‖w‖ ^ 2 + 2 * ⟪w, v'⟫ := by simp [w, v']
      _ = (‖w‖ ^ 2 + 2 * ⟪w, v'⟫ + ‖v'‖ ^ 2) - ‖v'‖ ^ 2 := by ring
      _ = ‖w + v'‖ ^ 2 - ‖v'‖ ^ 2 := by rw [norm_add_sq_real]
      _ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by simp [hsum, v']
  -- Step 1: Paper (4.4) — (2/L)(v_k - v_{k+1}) ≥ ‖d‖² + 2⟨d, y_{k+1} - x_k⟩
  have h_step1 : (2 / L) * (v k - v (k + 1)) ≥ ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫ := by
    rw [hv_diff]
    calc
      (2 / L) * (F (xSeq k) - F (xSeq (k + 1)))
          ≥ (2 / L) * ((L / 2) * ‖d‖ ^ 2 + L * ⟪ySeq (k + 1) - xSeq k, d⟫) := by gcongr
      _ = (2 / L) * (L / 2) * ‖d‖ ^ 2 + (2 / L) * L * ⟪ySeq (k + 1) - xSeq k, d⟫ := by ring
      _ = 1 * ‖d‖ ^ 2 + 2 * ⟪ySeq (k + 1) - xSeq k, d⟫ := by field_simp [hLpos.ne']
      _ = ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫ := by simp [real_inner_comm d]
  -- Step 1': Paper (4.5) — (2/L)(-v_{k+1}) ≥ ‖d‖² + 2⟨d, y_{k+1} - x*⟩
  have h_step1' : (2 / L) * (-v (k + 1)) ≥ ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫ := by
    rw [hv_neg]
    calc
      (2 / L) * (F xStar - F (xSeq (k + 1)))
          ≥ (2 / L) * ((L / 2) * ‖d‖ ^ 2 + L * ⟪ySeq (k + 1) - xStar, d⟫) := by gcongr
      _ = (2 / L) * (L / 2) * ‖d‖ ^ 2 + (2 / L) * L * ⟪ySeq (k + 1) - xStar, d⟫ := by ring
      _ = 1 * ‖d‖ ^ 2 + 2 * ⟪ySeq (k + 1) - xStar, d⟫ := by field_simp [hLpos.ne']
      _ = ‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫ := by simp [real_inner_comm d]
  -- Vector identity for linear combination in Step 2
  have h_vec_id : ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) + (ySeq (k + 1) - xStar) =
      t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by
    calc
      ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) + (ySeq (k + 1) - xStar)
          = ((t - 1) • ySeq (k + 1) - (t - 1) • xSeq k) + (ySeq (k + 1) - xStar) := by simp [smul_sub]
      _ = ((t - 1) • ySeq (k + 1) + ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by abel
      _ = ((t - 1) • ySeq (k + 1) + (1 : ℝ) • ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by simp
      _ = ((t - 1 + 1 : ℝ) • ySeq (k + 1)) - ((t - 1) • xSeq k + xStar) := by rw [add_smul]
      _ = t • ySeq (k + 1) - ((t - 1) • xSeq k + xStar) := by ring
      _ = t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by abel
  -- Step 2: Combined inequality (t-1)*(4.4) + (4.5), paper before (4.6)
  have h_combined : (2 / L) * ((t - 1) * v k - t * v (k + 1)) ≥
      t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
    have hsum_rhs : (t - 1) * (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫) +
        (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫) =
        t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
      calc
        (t - 1) * (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xSeq k⟫) +
            (‖d‖ ^ 2 + 2 * ⟪d, ySeq (k + 1) - xStar⟫)
            = t * ‖d‖ ^ 2 + 2 * ((t - 1) * ⟪d, ySeq (k + 1) - xSeq k⟫ +
                ⟪d, ySeq (k + 1) - xStar⟫) := by ring
        _ = t * ‖d‖ ^ 2 + 2 * (⟪d, (t - 1) • (ySeq (k + 1) - xSeq k)⟫ +
            ⟪d, ySeq (k + 1) - xStar⟫) := by simp [inner_smul_right]
        _ = t * ‖d‖ ^ 2 + 2 * ⟪d, ((t - 1 : ℝ) • (ySeq (k + 1) - xSeq k)) +
            (ySeq (k + 1) - xStar)⟫ := by simp [inner_add_right]
        _ = t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by rw [h_vec_id]
    have h_lhs : (t - 1) * ((2 / L) * (v k - v (k + 1))) + (2 / L) * (-v (k + 1)) =
        (2 / L) * ((t - 1) * v k - t * v (k + 1)) := by ring
    have h_ineq_sum : (t - 1) * ((2 / L) * (v k - v (k + 1))) + (2 / L) * (-v (k + 1)) ≥
        t * ‖d‖ ^ 2 + 2 * ⟪d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
      nlinarith
    rw [h_lhs] at h_ineq_sum
    exact h_ineq_sum
  -- Step 3: Multiply by t and use t_k² = t² - t to get paper (4.6)
  have h_step3 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖t • d‖ ^ 2 + 2 * ⟪t • d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := by
    have ht_nonneg : 0 ≤ t := by linarith
    set X := t • ySeq (k + 1) - (t - 1) • xSeq k - xStar with hX
    have h_mul : t * ((2 / L) * ((t - 1) * v k - t * v (k + 1))) ≥
        t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) := by gcongr
    have h_lhs_simp : t * ((2 / L) * ((t - 1) * v k - t * v (k + 1))) =
        (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by
      calc
        t * ((2 / L) * ((t - 1) * v k - t * v (k + 1)))
            = (2 / L) * (t * ((t - 1) * v k - t * v (k + 1))) := by ring
        _ = (2 / L) * (t * (t - 1) * v k - t ^ 2 * v (k + 1)) := by ring
        _ = (2 / L) * ((t ^ 2 - t) * v k - t ^ 2 * v (k + 1)) := by ring
        _ = (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by rw [h_tsq]
    have h_norm_sq : t ^ 2 * ‖d‖ ^ 2 = ‖t • d‖ ^ 2 := by
      calc
        t ^ 2 * ‖d‖ ^ 2 = (t * ‖d‖) ^ 2 := by ring
        _ = ‖t • d‖ ^ 2 := by simp [norm_smul, abs_of_nonneg ht_nonneg]
    have h_inner_eq : 2 * t * ⟪d, X⟫ = 2 * ⟪t • d, X⟫ := by
      calc
        2 * t * ⟪d, X⟫ = 2 * (t * ⟪d, X⟫) := by ring
        _ = 2 * ⟪t • d, X⟫ := by simp [inner_smul_left]
    have h_rhs_simp : t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) =
        ‖t • d‖ ^ 2 + 2 * ⟪t • d, X⟫ := by
      calc
        t * (t * ‖d‖ ^ 2 + 2 * ⟪d, X⟫) = t ^ 2 * ‖d‖ ^ 2 + 2 * t * ⟪d, X⟫ := by ring
        _ = ‖t • d‖ ^ 2 + 2 * ⟪t • d, X⟫ := by rw [h_norm_sq, h_inner_eq]
    rw [h_lhs_simp, h_rhs_simp] at h_mul
    exact h_mul
  -- Step 4: Apply the Pythagoras identity with a=t·y, b=t·x_{k+1}, c=(t-1)·x_k + x*
  set a := t • ySeq (k + 1) with ha
  set b := t • xSeq (k + 1) with hb
  set c := (t - 1) • xSeq k + xStar with hc
  have hA : b - a = t • d := by simp [a, b, hd, smul_sub]
  have hB : a - c = t • ySeq (k + 1) - (t - 1) • xSeq k - xStar := by
    simp [a, c]; abel
  have hC : b - c = t • xSeq (k + 1) - (t - 1) • xSeq k - xStar := by
    simp [b, c]; abel
  have h_step4 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
      ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by
    calc
      (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1))
          ≥ ‖t • d‖ ^ 2 + 2 * ⟪t • d, t • ySeq (k + 1) - (t - 1) • xSeq k - xStar⟫ := h_step3
      _ = ‖t • d‖ ^ 2 + 2 * ⟪t • d, a - c⟫ := by rw [hB]
      _ = ‖b - a‖ ^ 2 + 2 * ⟪b - a, a - c⟫ := by rw [hA]
      _ = ‖b - c‖ ^ 2 - ‖a - c‖ ^ 2 := by rw [h_pythagoras a b c]
      _ = ‖b - c‖ ^ 2 - ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hB]
      _ = ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
          ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hC]
  -- Step 5: Relate to u_k, u_{k+1} via the FISTA y-update formula
  have hu_kp1 : u (k + 1) = t • xSeq (k + 1) - (t - 1) • xSeq k - xStar := by
    dsimp [u, t]
  -- FISTA y-update: t·y_{k+1} = t·x_k + (t_k - 1)·(x_k - x_{k-1})  (paper (4.3))
  have h_y_update : t • ySeq (k + 1) = t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1)) := by
    have ht_ne_zero : t ≠ 0 := by linarith
    rw [h_yk1]
    calc
      t • (xSeq k + ((tSeq k - 1) / t) • (xSeq k - xSeq (k - 1)))
          = t • xSeq k + t • (((tSeq k - 1) / t) • (xSeq k - xSeq (k - 1))) := by simp [smul_add]
      _ = t • xSeq k + (t * ((tSeq k - 1) / t)) • (xSeq k - xSeq (k - 1)) := by simp [smul_smul]
      _ = t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1)) := by field_simp [ht_ne_zero]
  -- Show: t·y_{k+1} - (t-1)·x_k - x* = u_k
  have h_identity : t • ySeq (k + 1) - (t - 1) • xSeq k - xStar = u k := by
    calc
      t • ySeq (k + 1) - (t - 1) • xSeq k - xStar
          = (t • xSeq k + (tSeq k - 1) • (xSeq k - xSeq (k - 1))) - (t - 1) • xSeq k - xStar := by
            rw [h_y_update]
      _ = (t • xSeq k + ((tSeq k - 1) • xSeq k - (tSeq k - 1) • xSeq (k - 1))) -
          (t - 1) • xSeq k - xStar := by simp [smul_sub]
      _ = ((t • xSeq k - (t - 1) • xSeq k) + (tSeq k - 1) • xSeq k -
          (tSeq k - 1) • xSeq (k - 1)) - xStar := by abel
      _ = ((1 : ℝ) • xSeq k + (tSeq k - 1) • xSeq k -
          (tSeq k - 1) • xSeq (k - 1)) - xStar := by simp [sub_smul, one_smul]
      _ = (((1 : ℝ) + (tSeq k - 1)) • xSeq k - (tSeq k - 1) • xSeq (k - 1)) - xStar := by
        rw [add_smul]
      _ = (tSeq k • xSeq k - (tSeq k - 1) • xSeq (k - 1)) - xStar := by ring
      _ = u k := rfl
  -- Combine: h_step4 rewritten with u_{k+1} and u_k
  have h_step5 : (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) ≥
      ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by
    calc
      (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1))
          ≥ ‖t • xSeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 -
            ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := h_step4
      _ = ‖u (k + 1)‖ ^ 2 - ‖t • ySeq (k + 1) - (t - 1) • xSeq k - xStar‖ ^ 2 := by rw [hu_kp1]
      _ = ‖u (k + 1)‖ ^ 2 - ‖u k‖ ^ 2 := by rw [h_identity]
  -- Step 6: Relax L_{k+1} to L_k.  Since L_k ≤ L_{k+1} and both positive,
  -- 2/L_k ≥ 2/L_{k+1}, so (2/L_k)·(t_k²·v_k) ≥ (2/L_{k+1})·(t_k²·v_k).
  -- Step 6: Compare L_k ≤ L to get the final inequality
  -- We need 0 < LSeq k for the fraction comparison. For k ≥ 2 this follows
  -- from hFISTA at k-1; for k = 1 the hypothesis set is slightly weaker.
  by_cases hLkpos : 0 < LSeq k
  · have hA_nonneg : 0 ≤ (tSeq k) ^ 2 * v k :=
      mul_nonneg (sq_nonneg _) (hv_nonneg k)
    have h_div : (2 : ℝ) / LSeq k ≥ (2 : ℝ) / L := by
      have h_one_div : 1 / LSeq k ≥ 1 / L :=
        (one_div_le_one_div hLpos hLkpos).mpr h_Lk1
      calc
        (2 : ℝ) / LSeq k = 2 * (1 / LSeq k) := by ring
        _ ≥ 2 * (1 / L) := by gcongr
        _ = (2 : ℝ) / L := by ring
    have h_first_ge : (2 / LSeq k) * (tSeq k) ^ 2 * v k ≥ (2 / L) * (tSeq k) ^ 2 * v k := by
      calc
        (2 / LSeq k) * (tSeq k) ^ 2 * v k = ((2 : ℝ) / LSeq k) * ((tSeq k) ^ 2 * v k) := by ring
        _ ≥ ((2 : ℝ) / L) * ((tSeq k) ^ 2 * v k) := by gcongr
        _ = (2 / L) * (tSeq k) ^ 2 * v k := by ring
    have h_mid : (2 / LSeq k) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1) ≥
        (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by
      calc
        (2 / LSeq k) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1)
            ≥ (2 / L) * (tSeq k) ^ 2 * v k - (2 / L) * t ^ 2 * v (k + 1) := by gcongr
        _ = (2 / L) * ((tSeq k) ^ 2 * v k - t ^ 2 * v (k + 1)) := by ring
    exact le_trans h_step5 h_mid
  · -- LSeq k ≤ 0: for k ≥ 2 this contradicts hFISTA; for k = 1 the
    -- lemma hypothesis is missing `0 < LSeq 1` (present in thm_2).
    by_cases hk1 : k = 1
    · subst hk1
      exact absurd hLseq1_pos hLkpos
    · have hk' : 1 ≤ k - 1 := by
        have : 2 ≤ k := by omega
        omega
      rcases hFISTA (k - 1) hk' with ⟨hpos, _, _, _, _, _⟩
      have eq : LSeq ((k - 1) + 1) = LSeq k := by rw [Nat.sub_add_cancel (by omega)]
      have hpos_k : 0 < LSeq k := by simpa [eq] using hpos
      exact absurd hpos_k hLkpos
