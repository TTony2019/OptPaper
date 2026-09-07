import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_3
import TheoremLib.Beck_Teboulle_FISTA_2009.items.algo_3
import TheoremLib.Beck_Teboulle_FISTA_2009.items.algo_4

open Set
open scoped RealInnerProductSpace

/-- Internal rate lemma for an accepted ISTA stepsize sequence.

The public Theorem 3.1 entry points are the two mode-specific rate lemmas below
and the unified `ista_convergence_rate` at the end.  Keeping this proof lemma
separate prevents a per-iteration disjunction from being mistaken for the
paper's global choice of algorithmic mode.  In the variable branch, `LSeq k`
is the stepsize used for the transition `x k -> x (k+1)`; the concrete
backtracking algorithm supplies it as `L (k+1)`. -/
private theorem ista_convergence_rate_of_steps {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf α : ℝ} (hP : ProblemP f g Lf) (xSeq : ℕ → EuclideanSpace ℝ (Fin n))
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : xSeq 0 = x0)
    (h_alpha_ge_one : 1 ≤ α)
    (hstep_mode :
      (∀ k, IsProxPoint f g Lf (xSeq k) (xSeq (k + 1))) ∨
      (∃ (LSeq : ℕ → ℝ),
        (∀ k, 0 < LSeq k) ∧
        (∀ k, IsProxPoint f g (LSeq k) (xSeq k) (xSeq (k + 1))) ∧
        (∀ k, compositeObjective f g (xSeq (k + 1)) ≤
          quadraticApprox f g (LSeq k) (xSeq (k + 1)) (xSeq k)) ∧
        (∀ k, LSeq k ≤ α * Lf)))
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (xSeq k) - compositeObjective f g xStar ≤
      (α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
  have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
  let F (x : EuclideanSpace ℝ (Fin n)) := compositeObjective f g x
  have h_cond_prox (y z : EuclideanSpace ℝ (Fin n)) (hp : IsProxPoint f g Lf y z) :
      F z ≤ quadraticApprox f g Lf z y := by
    unfold F quadraticApprox compositeObjective
    have h := quadratic_upper_bound_C11 hP.smooth_f (le_refl Lf) z y
    linarith
  -- Norm identity: ‖z-y‖² + 2⟨y-x, z-y⟩ = ‖x-z‖² - ‖x-y‖²
  have h_norm_id (x y z : EuclideanSpace ℝ (Fin n)) :
      ‖z - y‖ ^ 2 + 2 * ⟪y - x, z - y⟫ = ‖x - z‖ ^ 2 - ‖x - y‖ ^ 2 := by
    set a := z - y with ha
    have h1 : ‖(x - y) - a‖ ^ 2 = ‖x - z‖ ^ 2 := by dsimp [a]; abel
    have h2 : ‖(x - y) - a‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * ⟪x - y, a⟫ + ‖a‖ ^ 2 :=
      norm_sub_sq_real (x - y) a
    have h3 : ⟪y - x, a⟫ = -⟪x - y, a⟫ := by
      simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
    calc
      ‖z - y‖ ^ 2 + 2 * ⟪y - x, z - y⟫ = ‖a‖ ^ 2 + 2 * ⟪y - x, a⟫ := by simp [ha]
      _ = ‖a‖ ^ 2 + 2 * (-⟪x - y, a⟫) := by rw [h3]
      _ = ‖a‖ ^ 2 - 2 * ⟪x - y, a⟫ := by ring
      _ = (‖x - y‖ ^ 2 - 2 * ⟪x - y, a⟫ + ‖a‖ ^ 2) - ‖x - y‖ ^ 2 := by ring
      _ = ‖(x - y) - a‖ ^ 2 - ‖x - y‖ ^ 2 := by rw [h2]
      _ = ‖x - z‖ ^ 2 - ‖x - y‖ ^ 2 := by rw [h1]
  -- Telescoping-friendly form of key_inequality
  have h_key_telescope (x y z : EuclideanSpace ℝ (Fin n))
      (hp : IsProxPoint f g Lf y z) (hc : F z ≤ quadraticApprox f g Lf z y) :
      F x - F z ≥ (Lf / 2) * (‖x - z‖ ^ 2 - ‖x - y‖ ^ 2) := by
    have h_key := key_inequality hP y x z hp hc
    have h_eq : (Lf / 2) * ‖z - y‖ ^ 2 + Lf * ⟪y - x, z - y⟫ =
        (Lf / 2) * (‖x - z‖ ^ 2 - ‖x - y‖ ^ 2) := by
      calc
        (Lf / 2) * ‖z - y‖ ^ 2 + Lf * ⟪y - x, z - y⟫
            = (Lf / 2) * (‖z - y‖ ^ 2 + 2 * ⟪y - x, z - y⟫) := by ring
        _ = (Lf / 2) * (‖x - z‖ ^ 2 - ‖x - y‖ ^ 2) := by rw [h_norm_id x y z]
    calc
      F x - F z ≥ (Lf / 2) * ‖z - y‖ ^ 2 + Lf * ⟪y - x, z - y⟫ := h_key
      _ = (Lf / 2) * (‖x - z‖ ^ 2 - ‖x - y‖ ^ 2) := by rw [h_eq]
  -- Sum helper: telescoping identity (used by both cases)
  have h_telescope (a : ℕ → ℝ) (k : ℕ) :
      Finset.sum (Finset.range k) (fun n => a (n+1) - a n) = a k - a 0 := by
    induction' k with m ih
    · simp
    · rw [Finset.sum_range_succ, ih]; ring
  -- The paper chooses one algorithm globally: constant stepsize or one
  -- variable stepsize sequence.  It does not permit changing mode per step.
  rcases hstep_mode with h_const | ⟨LSeq, hLpos_seq, hprox_seq, hcond_seq, hLbound_seq⟩
  · -- CONSTANT STEPSIZE CASE (α = 1 in paper)
    have h_cond (n : ℕ) : F (xSeq (n + 1)) ≤ quadraticApprox f g Lf (xSeq (n + 1)) (xSeq n) :=
      h_cond_prox (xSeq n) (xSeq (n + 1)) (h_const n)
    -- Per-step inequality from Lemma 2.3 at (x*, x_n, x_{n+1})
    have hA (n : ℕ) : (2 / Lf) * (F xStar - F (xSeq (n + 1))) ≥
        ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2 := by
      have h := h_key_telescope xStar (xSeq n) (xSeq (n + 1)) (h_const n) (h_cond n)
      -- h: A ≥ (Lf/2)*B where A = F*-F_{n+1}, B = ‖x*-x_{n+1}‖² - ‖x*-x_n‖²
      have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
      have h_mul : (2 / Lf) * ((Lf / 2) * (‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2)) =
          ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2 := by
        field_simp [hLfpos.ne']
      have h_factor_nonneg : 0 ≤ (2 : ℝ) / Lf := by positivity
      have h_mul_ineq := mul_le_mul_of_nonneg_left h h_factor_nonneg
      -- h_mul_ineq: (2/Lf)*A ≥ (2/Lf)*((Lf/2)*B) = B
      rwa [h_mul] at h_mul_ineq
    -- Monotone decrease: F(x_{n+1}) ≤ F(x_n)
    have h_decr (n : ℕ) : F (xSeq (n + 1)) ≤ F (xSeq n) := by
      have h := h_key_telescope (xSeq n) (xSeq n) (xSeq (n + 1)) (h_const n) (h_cond n)
      -- h: F(x_n)-F(x_{n+1}) ≥ (Lf/2)*(‖x_n-x_{n+1}‖² - ‖x_n-x_n‖²)
      -- ‖x_n - x_n‖ = 0, so RHS = (Lf/2)*‖x_n-x_{n+1}‖² ≥ 0
      have h_simp : (Lf / 2) * (‖xSeq n - xSeq (n + 1)‖ ^ 2 - ‖xSeq n - xSeq n‖ ^ 2) =
          (Lf / 2) * ‖xSeq n - xSeq (n + 1)‖ ^ 2 := by simp
      rw [h_simp] at h
      have h_nonneg : 0 ≤ (Lf / 2) * ‖xSeq n - xSeq (n + 1)‖ ^ 2 := by positivity
      linarith
    -- Chain: if i ≤ j then F(xSeq j) ≤ F(xSeq i)
    have h_decr_chain {i j : ℕ} (hij : i ≤ j) : F (xSeq j) ≤ F (xSeq i) := by
      induction' hij with m him ih
      · rfl
      · exact le_trans (h_decr m) ih
    -- Sum (A) for n = 0, ..., k-1; RHS telescopes
    have h_sumA : (2 / Lf) * (Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1)))) ≥
        ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 := by
      have h_mul_sum : (2 / Lf) * (Finset.sum (Finset.range k)
          (fun n => F xStar - F (xSeq (n + 1)))) =
          Finset.sum (Finset.range k)
            (fun n => (2 / Lf) * (F xStar - F (xSeq (n + 1)))) := by
        rw [Finset.mul_sum]
      rw [h_mul_sum]
      have h_sum_le : Finset.sum (Finset.range k)
          (fun n => ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) ≤
          Finset.sum (Finset.range k)
            (fun n => (2 / Lf) * (F xStar - F (xSeq (n + 1)))) :=
        Finset.sum_le_sum (fun n _ => hA n)
      have h_tel : Finset.sum (Finset.range k)
          (fun n => ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) =
          ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 :=
        h_telescope (fun m => ‖xStar - xSeq m‖ ^ 2) k
      rw [h_tel] at h_sum_le
      exact h_sum_le
    -- Since F(xSeq k) ≤ F(xSeq (n+1)) for n < k, Σ F(xSeq(n+1)) ≥ k·F(xSeq k)
    have h_sum_ge : (k : ℝ) * F (xSeq k) ≤
        Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by
      calc
        (k : ℝ) * F (xSeq k) = Finset.sum (Finset.range k) (fun _ => F (xSeq k)) := by simp
        _ ≤ Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) :=
          Finset.sum_le_sum (fun n hn => by
            have hn' : n < k := Finset.mem_range.1 hn
            have hnk : n + 1 ≤ k := by omega
            exact h_decr_chain hnk)
    -- Combine: k·F* - k·F_k ≥ k·F* - ΣF_{n+1} (since ΣF_{n+1} ≥ k·F_k)
    have h_main : (2 / Lf) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥
        ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 := by
      have h_diff : (k : ℝ) * (F xStar - F (xSeq k)) ≥
          Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1))) := by
        calc
          (k : ℝ) * (F xStar - F (xSeq k)) = (k : ℝ) * F xStar - (k : ℝ) * F (xSeq k) := by ring
          _ ≥ (k : ℝ) * F xStar -
              Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by linarith
          _ = Finset.sum (Finset.range k) (fun _ => F xStar) -
              Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by simp
          _ = Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1))) := by
            rw [Finset.sum_sub_distrib]
      have hpos : 0 < (2 : ℝ) / Lf := by
        have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
        positivity
      have h_mul : (2 / Lf) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥
          (2 / Lf) * (Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1)))) := by
        gcongr
      linarith
    -- Final bound: extract the result from h_main
    have h_final : F (xSeq k) - F xStar ≤ (α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
      have h_norm_symm : ‖xStar - xSeq 0‖ ^ 2 = ‖x0 - xStar‖ ^ 2 := by
        rw [hx0, norm_sub_rev]
      have h_nonneg_sq : 0 ≤ ‖xStar - xSeq k‖ ^ 2 := by positivity
      have h_base : (2 / Lf) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥ -‖x0 - xStar‖ ^ 2 := by
        nlinarith
      have hLfpos : 0 < Lf := hP.smooth_f.hL_pos
      have hkpos : 0 < (k : ℝ) := by
        have hpos_nat : 0 < k := by omega
        exact_mod_cast hpos_nat
      -- Rearrange: F*-F_k ≥ -(Lf * ‖x₀-x*‖²) / (2k)
      have h_factor_pos : 0 < (2 * (k : ℝ)) / Lf := by positivity
      have h_rearr : F xStar - F (xSeq k) ≥
          -((Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ))) := by
        -- From h_base: (2/Lf)*k*(F*-F_k) ≥ -C
        -- Multiply by Lf/(2k) > 0: F*-F_k ≥ -C * Lf/(2k)
        have h_eq : (Lf / (2 * (k : ℝ))) * ((2 / Lf) * ((k : ℝ) * (F xStar - F (xSeq k)))) =
            F xStar - F (xSeq k) := by
          field_simp [hLfpos.ne', hkpos.ne']
        calc
          F xStar - F (xSeq k)
              = (Lf / (2 * (k : ℝ))) * ((2 / Lf) * ((k : ℝ) * (F xStar - F (xSeq k)))) := by
                rw [h_eq]
          _ ≥ (Lf / (2 * (k : ℝ))) * (-‖x0 - xStar‖ ^ 2) := by gcongr
          _ = -((Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ))) := by ring
      have h_without_alpha : F (xSeq k) - F xStar ≤
          (Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by linarith
      -- Since α ≥ 1, α·Lf ≥ Lf ≥ 0, so the α-bound follows
      have h_bound : Lf * ‖x0 - xStar‖ ^ 2 / (2 * (k : ℝ)) ≤
          α * Lf * ‖x0 - xStar‖ ^ 2 / (2 * (k : ℝ)) := by
        have h_num : Lf * ‖x0 - xStar‖ ^ 2 ≤ α * Lf * ‖x0 - xStar‖ ^ 2 := by
          have h_sq_nonneg : 0 ≤ ‖x0 - xStar‖ ^ 2 := by positivity
          gcongr
          exact le_mul_of_one_le_left (by linarith) h_alpha_ge_one
        have h_nonneg : 0 ≤ 2 * (k : ℝ) := by positivity
        exact div_le_div_of_nonneg_right h_num h_nonneg
      linarith
    exact h_final
  · -- BACKTRACKING / VARIABLE-STEPSIZE CASE
    have h_alpha_Lf_pos : 0 < α * Lf := by
      have hαpos : 0 < α := by linarith
      positivity
    -- F(x*) ≤ F(x) for all x (x* is a minimizer)
    have h_Fstar_min (x : EuclideanSpace ℝ (Fin n)) : F xStar ≤ F x :=
      hxStar (Set.mem_univ x)
    have h_Fstar_diff_nonpos (x : EuclideanSpace ℝ (Fin n)) : F xStar - F x ≤ 0 := by
      linarith [h_Fstar_min x]
    -- Per-step inequality: (2/(α·Lf))·(F* - F_{n+1}) ≥ ‖x* - x_{n+1}‖² - ‖x* - x_n‖²
    have hA (n : ℕ) : (2 / (α * Lf)) * (F xStar - F (xSeq (n + 1))) ≥
        ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2 := by
      have h_key := key_inequality' hP (hLpos_seq n) (xSeq n) xStar (xSeq (n + 1))
        (hprox_seq n) (hcond_seq n)
      have h_norm_eq : (LSeq n / 2) * ‖xSeq (n + 1) - xSeq n‖ ^ 2 +
          LSeq n * ⟪xSeq n - xStar, xSeq (n + 1) - xSeq n⟫ =
          (LSeq n / 2) * (‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) := by
        calc
          (LSeq n / 2) * ‖xSeq (n + 1) - xSeq n‖ ^ 2 +
              LSeq n * ⟪xSeq n - xStar, xSeq (n + 1) - xSeq n⟫
              = (LSeq n / 2) * (‖xSeq (n + 1) - xSeq n‖ ^ 2 +
                  2 * ⟪xSeq n - xStar, xSeq (n + 1) - xSeq n⟫) := by ring
          _ = (LSeq n / 2) * (‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) := by
            rw [h_norm_id xStar (xSeq n) (xSeq (n + 1))]
      have h_bound1 : F xStar - F (xSeq (n + 1)) ≥
          (LSeq n / 2) * (‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) := by linarith
      -- Multiply by 2/L_n > 0 to get (2/L_n)*(F* - F_{n+1}) ≥ D
      have h_bound2 : (2 / LSeq n) * (F xStar - F (xSeq (n + 1))) ≥
          ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2 := by
        have h_mul : (2 / LSeq n) * ((LSeq n / 2) *
            (‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2)) =
            ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2 := by
          field_simp [hLpos_seq n |>.ne']
        have h_factor_nonneg : 0 ≤ (2 : ℝ) / LSeq n :=
          div_nonneg (by norm_num) (by linarith [hLpos_seq n])
        have h_mul_ineq := mul_le_mul_of_nonneg_left h_bound1 h_factor_nonneg
        rwa [h_mul] at h_mul_ineq
      -- Since L_n ≤ α·Lf and F* - F_{n+1} ≤ 0, we have
      -- (2/L_n)*(F* - F_{n+1}) ≤ (2/(α·Lf))*(F* - F_{n+1})
      -- Therefore (2/(α·Lf))*(F* - F_{n+1}) ≥ D
      have h_div_ge : (2 : ℝ) / LSeq n ≥ (2 : ℝ) / (α * Lf) := by
        have h_one_div : 1 / LSeq n ≥ 1 / (α * Lf) :=
          (one_div_le_one_div h_alpha_Lf_pos (hLpos_seq n)).mpr (hLbound_seq n)
        calc
          (2 : ℝ) / LSeq n = 2 * (1 / LSeq n) := by ring
          _ ≥ 2 * (1 / (α * Lf)) := by gcongr
          _ = (2 : ℝ) / (α * Lf) := by ring
      have h_bound3 : (2 / LSeq n) * (F xStar - F (xSeq (n + 1))) ≤
          (2 / (α * Lf)) * (F xStar - F (xSeq (n + 1))) := by
        nlinarith [h_Fstar_diff_nonpos (xSeq (n + 1))]
      linarith
    -- Monotone decrease: F(x_{n+1}) ≤ F(x_n)
    have h_decr (n : ℕ) : F (xSeq (n + 1)) ≤ F (xSeq n) := by
      have h_key := key_inequality' hP (hLpos_seq n) (xSeq n) (xSeq n) (xSeq (n + 1))
        (hprox_seq n) (hcond_seq n)
      -- h_key : F(x_n) - F(x_{n+1}) ≥ (L_n/2)*‖x_{n+1} - x_n‖² + L_n*⟨x_n - x_n, ...⟩
      -- The inner product term is 0, so LHS ≥ (L_n/2)*‖x_{n+1} - x_n‖² ≥ 0
      have h_simp : (LSeq n / 2) * ‖xSeq (n + 1) - xSeq n‖ ^ 2 +
          LSeq n * ⟪xSeq n - xSeq n, xSeq (n + 1) - xSeq n⟫ =
          (LSeq n / 2) * ‖xSeq (n + 1) - xSeq n‖ ^ 2 := by simp
      rw [h_simp] at h_key
      have h_nonneg : 0 ≤ (LSeq n / 2) * ‖xSeq (n + 1) - xSeq n‖ ^ 2 := by
        have hL : 0 ≤ LSeq n / 2 := div_nonneg (by linarith [hLpos_seq n]) (by norm_num)
        have h_sq : 0 ≤ ‖xSeq (n + 1) - xSeq n‖ ^ 2 := by positivity
        exact mul_nonneg hL h_sq
      linarith
    -- Chain: if i ≤ j then F(xSeq j) ≤ F(xSeq i)
    have h_decr_chain {i j : ℕ} (hij : i ≤ j) : F (xSeq j) ≤ F (xSeq i) := by
      induction' hij with m him ih
      · rfl
      · exact le_trans (h_decr m) ih
    -- Sum the per-step inequalities for n = 0, ..., k-1; RHS telescopes
    have h_sumA : (2 / (α * Lf)) * (Finset.sum (Finset.range k)
        (fun n => F xStar - F (xSeq (n + 1)))) ≥
        ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 := by
      have h_mul_sum : (2 / (α * Lf)) * (Finset.sum (Finset.range k)
          (fun n => F xStar - F (xSeq (n + 1)))) =
          Finset.sum (Finset.range k)
            (fun n => (2 / (α * Lf)) * (F xStar - F (xSeq (n + 1)))) := by
        rw [Finset.mul_sum]
      rw [h_mul_sum]
      have h_sum_le : Finset.sum (Finset.range k)
          (fun n => ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) ≤
          Finset.sum (Finset.range k)
            (fun n => (2 / (α * Lf)) * (F xStar - F (xSeq (n + 1)))) :=
        Finset.sum_le_sum (fun n _ => hA n)
      have h_tel : Finset.sum (Finset.range k)
          (fun n => ‖xStar - xSeq (n + 1)‖ ^ 2 - ‖xStar - xSeq n‖ ^ 2) =
          ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 :=
        h_telescope (fun m => ‖xStar - xSeq m‖ ^ 2) k
      rw [h_tel] at h_sum_le
      exact h_sum_le
    -- Since F(xSeq k) ≤ F(xSeq (n+1)) for n < k, ΣF(x_{n+1}) ≥ k·F(xSeq k)
    have h_sum_ge : (k : ℝ) * F (xSeq k) ≤
        Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by
      calc
        (k : ℝ) * F (xSeq k) = Finset.sum (Finset.range k) (fun _ => F (xSeq k)) := by simp
        _ ≤ Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) :=
          Finset.sum_le_sum (fun n hn => by
            have hn' : n < k := Finset.mem_range.1 hn
            have hnk : n + 1 ≤ k := by omega
            exact h_decr_chain hnk)
    -- Combine: k·F* - ΣF_{n+1} ≥ k·(F* - F_k)
    have h_main : (2 / (α * Lf)) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥
        ‖xStar - xSeq k‖ ^ 2 - ‖xStar - xSeq 0‖ ^ 2 := by
      have h_diff : (k : ℝ) * (F xStar - F (xSeq k)) ≥
          Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1))) := by
        calc
          (k : ℝ) * (F xStar - F (xSeq k)) = (k : ℝ) * F xStar - (k : ℝ) * F (xSeq k) := by ring
          _ ≥ (k : ℝ) * F xStar -
              Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by linarith
          _ = Finset.sum (Finset.range k) (fun _ => F xStar) -
              Finset.sum (Finset.range k) (fun n => F (xSeq (n + 1))) := by simp
          _ = Finset.sum (Finset.range k) (fun n => F xStar - F (xSeq (n + 1))) := by
            rw [Finset.sum_sub_distrib]
      have hpos : 0 < (2 : ℝ) / (α * Lf) := by positivity
      have h_mul : (2 / (α * Lf)) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥
          (2 / (α * Lf)) * (Finset.sum (Finset.range k)
            (fun n => F xStar - F (xSeq (n + 1)))) := by gcongr
      linarith
    -- Final bound
    have h_final : F (xSeq k) - F xStar ≤ (α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
      have h_norm_symm : ‖xStar - xSeq 0‖ ^ 2 = ‖x0 - xStar‖ ^ 2 := by
        rw [hx0, norm_sub_rev]
      have h_nonneg_sq : 0 ≤ ‖xStar - xSeq k‖ ^ 2 := by positivity
      have h_base : (2 / (α * Lf)) * ((k : ℝ) * (F xStar - F (xSeq k))) ≥ -‖x0 - xStar‖ ^ 2 := by
        nlinarith
      have hkpos : 0 < (k : ℝ) := by
        have hpos_nat : 0 < k := by omega
        exact_mod_cast hpos_nat
      -- Rearrange: F* - F_k ≥ -(α·Lf·‖x₀-x*‖²)/(2k)
      have h_rearr : F xStar - F (xSeq k) ≥
          -((α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ))) := by
        -- From h_base: (2/(α·Lf))*k*(F*-F_k) ≥ -C
        -- Multiply by (α·Lf)/(2k) > 0: F*-F_k ≥ -C * (α·Lf)/(2k)
        have h_eq : ((α * Lf) / (2 * (k : ℝ))) *
            ((2 / (α * Lf)) * ((k : ℝ) * (F xStar - F (xSeq k)))) =
            F xStar - F (xSeq k) := by
          field_simp [h_alpha_Lf_pos.ne', hkpos.ne']
        calc
          F xStar - F (xSeq k)
              = ((α * Lf) / (2 * (k : ℝ))) *
                ((2 / (α * Lf)) * ((k : ℝ) * (F xStar - F (xSeq k)))) := by rw [h_eq]
          _ ≥ ((α * Lf) / (2 * (k : ℝ))) * (-‖x0 - xStar‖ ^ 2) := by gcongr
          _ = -((α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ))) := by ring
      have h_result : F (xSeq k) - F xStar ≤
          (α * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by linarith
      exact h_result
    exact h_final

/-- Theorem 3.1 for ISTA with the constant stepsize `L(f)` (equation (3.1)). -/
theorem ista_constant_stepsize_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTAConstantStepsize f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
  have h := ista_convergence_rate_of_steps (hP := hP) (xSeq := A.x) (x0 := x0)
    (hx0 := A.x_zero) (α := 1) (h_alpha_ge_one := by norm_num)
    (hstep_mode := by
      left
      intro n
      exact A.proximal_step_at n)
    (xStar := xStar) (hxStar := hxStar) (k := k) hk
  simpa using h

/-- Theorem 3.1 for ISTA with the backtracking rule (3.2)--(3.3).

`A` records the smallest accepted exponent and the recurrence
`L_k = η^(i_k) L_(k-1)`.  The analytical stepsize estimate (3.4) is supplied as
`h_bounds`, with `β = L₀ / L(f)` and `α = η`. -/
theorem ista_backtracking_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (h_bounds : BacktrackingStepsizeBounds Lf A.L0 A.eta A.L)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (A.eta * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
  have h := ista_convergence_rate_of_steps (hP := hP) (xSeq := A.x) (x0 := x0)
    (hx0 := A.x_zero) (α := A.eta)
    (h_alpha_ge_one := le_of_lt A.eta_gt_one)
    (hstep_mode := by
      right
      refine ⟨(fun n => A.L (n + 1)), ?_, ?_, ?_, ?_⟩
      · intro n
        exact A.stepsize_pos (n + 1)
      · intro n
        exact A.proximal_step (n + 1) (by omega)
      · intro n
        exact A.descent_condition (n + 1) (by omega)
      · intro n
        simpa [backtrackingAlpha] using (h_bounds (n + 1) (by omega)).2)
    (xStar := xStar) (hxStar := hxStar) (k := k) hk
  simpa using h

/-- A global choice of one of the two ISTA algorithms in Theorem 3.1.

This sum type rules out changing between constant and backtracking stepsizes from one
iteration to the next. -/
inductive ISTARun {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  | constant (run : ISTAConstantStepsize f g Lf x0)
  | backtracking (run : ISTABacktracking f g x0)
      (bounds : BacktrackingStepsizeBounds Lf run.L0 run.eta run.L)

namespace ISTARun

def x {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} :
    ISTARun f g Lf x0 → ℕ → EuclideanSpace ℝ (Fin n)
  | .constant run => run.x
  | .backtracking run _ => run.x

def alpha {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} : ISTARun f g Lf x0 → ℝ
  | .constant _ => 1
  | .backtracking run _ => run.eta

end ISTARun

/-- Theorem 3.1, with the paper's global choice between (3.1) and (3.3). -/
theorem ista_convergence_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTARun f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (A.alpha * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ)) := by
  cases A with
  | constant run =>
      simpa [ISTARun.x, ISTARun.alpha] using
        ista_constant_stepsize_rate hP run xStar hxStar k hk
  | backtracking run bounds =>
      simpa [ISTARun.x, ISTARun.alpha] using
        ista_backtracking_rate hP run bounds xStar hxStar k hk
