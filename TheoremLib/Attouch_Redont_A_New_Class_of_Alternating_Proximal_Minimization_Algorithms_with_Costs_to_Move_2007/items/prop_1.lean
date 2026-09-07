import Mathlib

/-!
# Proposition 2.1: Limit Points are Inertial Nash Equilibria
From: H. Attouch, P. Redont, A. Soubeyran (2007).

Proof: uses the eventuality definition of lower semicontinuity to get
pointwise eventual lower bounds. No liminf decomposition needed.
-/

open Set
open Filter
open scoped Topology

structure CA2 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) where
  x : ℕ → X
  y : ℕ → Y
  step_x (n : ℕ) (ξ : X) :
    f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
    f ξ + α n * h (x n) ξ + β n * c ξ (y n)
  step_y (n : ℕ) (η : Y) :
    g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
    g η + μ n * c (x (n+1)) η + ν n * k (y n) η

def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

structure H11toH14 (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) : Prop where
  f_lsc : LowerSemicontinuous f
  g_lsc : LowerSemicontinuous g
  f_bdd_below : ∃ Mf : ℝ, ∀ x : X, f x ≥ Mf
  g_bdd_below : ∃ Mg : ℝ, ∀ y : Y, g y ≥ Mg
  h_lsc : LowerSemicontinuous (fun (p : X × X) => h p.1 p.2)
  k_lsc : LowerSemicontinuous (fun (p : Y × Y) => k p.1 p.2)
  c_lsc : LowerSemicontinuous (fun (p : X × Y) => c p.1 p.2)
  h_sep_cont : (∀ (y : X), Continuous (fun (x : X) => h x y)) ∧
               (∀ (x : X), Continuous (fun (y : X) => h x y))
  k_sep_cont : (∀ (y : Y), Continuous (fun (x : Y) => k x y)) ∧
               (∀ (x : Y), Continuous (fun (y : Y) => k x y))
  c_sep_cont : (∀ (y : Y), Continuous (fun (x : X) => c x y)) ∧
               (∀ (x : X), Continuous (fun (y : Y) => c x y))
  h_nonneg : ∀ x x' : X, h x x' ≥ 0
  k_nonneg : ∀ y y' : Y, k y y' ≥ 0
  c_nonneg : ∀ x : X, ∀ y : Y, c x y ≥ 0
  alpha_nonneg : ∀ n, α n ≥ 0
  beta_nonneg : ∀ n, β n ≥ 0
  mu_nonneg : ∀ n, μ n ≥ 0
  nu_nonneg : ∀ n, ν n ≥ 0
  beta_conv : ∃ β_inf : ℝ, Tendsto β atTop (𝓝 β_inf)
  mu_conv : ∃ μ_inf : ℝ, Tendsto μ atTop (𝓝 μ_inf)

theorem proposition_2_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (hyp : H11toH14 X Y f g h k c α β μ ν)
    (xbar : X) (ybar : Y) (hx : Tendsto alg.x atTop (𝓝 xbar)) (hy : Tendsto alg.y atTop (𝓝 ybar))
    (α_inf : ℝ) (hα : Tendsto α atTop (𝓝 α_inf))
    (β_inf : ℝ) (hβ : Tendsto β atTop (𝓝 β_inf))
    (μ_inf : ℝ) (hμ : Tendsto μ atTop (𝓝 μ_inf))
    (ν_inf : ℝ) (hν : Tendsto ν atTop (𝓝 ν_inf)) :
    IsINE f g h k c α_inf β_inf μ_inf ν_inf xbar ybar := by
  rcases hyp with ⟨f_lsc, g_lsc, f_bdd, g_bdd, h_lsc, k_lsc, c_lsc,
    h_sep, k_sep, c_sep, h_nn, k_nn, c_nn, α_nn, β_nn, μ_nn, ν_nn, _, _⟩
  rcases h_sep with ⟨h_sep1, h_sep2⟩
  rcases k_sep with ⟨k_sep1, k_sep2⟩
  rcases c_sep with ⟨c_sep1, c_sep2⟩

  -- shifted convergence
  have hx_succ : Tendsto (fun n : ℕ => alg.x (n+1)) atTop (𝓝 xbar) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hy_succ : Tendsto (fun n : ℕ => alg.y (n+1)) atTop (𝓝 ybar) :=
    hy.comp (tendsto_add_atTop_nat 1)

  -- product convergences using Filter.Tendsto.prodMk_nhds
  have hx_pair : Tendsto (fun n : ℕ => (alg.x n, alg.x (n+1))) atTop (𝓝 (xbar, xbar)) :=
    Filter.Tendsto.prodMk_nhds hx hx_succ
  have hy_pair : Tendsto (fun n : ℕ => (alg.y n, alg.y (n+1))) atTop (𝓝 (ybar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hy hy_succ
  have hxy_pair_c : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y n)) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_succ hy
  have hxy_pair_c2 : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y (n+1))) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_succ hy_succ

  -- ============================================================
  -- Nonnegativity of limit values
  -- ============================================================
  have hα_inf_nonneg : α_inf ≥ 0 := by
    have h_ev : ∀ᶠ n in atTop, (0 : ℝ) ≤ α n := by
      apply eventually_atTop.mpr; exact ⟨0, fun n _ => α_nn n⟩
    exact ge_of_tendsto hα h_ev
  have hβ_inf_nonneg : β_inf ≥ 0 := by
    have h_ev : ∀ᶠ n in atTop, (0 : ℝ) ≤ β n := by
      apply eventually_atTop.mpr; exact ⟨0, fun n _ => β_nn n⟩
    exact ge_of_tendsto hβ h_ev
  have hμ_inf_nonneg : μ_inf ≥ 0 := by
    have h_ev : ∀ᶠ n in atTop, (0 : ℝ) ≤ μ n := by
      apply eventually_atTop.mpr; exact ⟨0, fun n _ => μ_nn n⟩
    exact ge_of_tendsto hμ h_ev
  have hν_inf_nonneg : ν_inf ≥ 0 := by
    have h_ev : ∀ᶠ n in atTop, (0 : ℝ) ≤ ν n := by
      apply eventually_atTop.mpr; exact ⟨0, fun n _ => ν_nn n⟩
    exact ge_of_tendsto hν h_ev
  have h_hbar_nonneg : h xbar xbar ≥ 0 := h_nn _ _
  have h_kbar_nonneg : k ybar ybar ≥ 0 := k_nn _ _
  have h_cbar_nonneg : c xbar ybar ≥ 0 := c_nn _ _

  -- ============================================================
  -- LSC EVENTUAL BOUNDS (LowerSemicontinuousAt + Tendsto.eventually)
  -- ============================================================
  -- LowerSemicontinuousAt f x := ∀ y, f x > y → ∀ᶠ x' in 𝓝 x, f x' > y
  have h_fx_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, f xbar - ε < f (alg.x (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 xbar, f z > f xbar - ε :=
      (f_lsc xbar) (f xbar - ε) (by linarith)
    filter_upwards [hx_succ.eventually h_nhds] with n hn
    exact hn

  have h_gy_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, g ybar - ε < g (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 ybar, g z > g ybar - ε :=
      (g_lsc ybar) (g ybar - ε) (by linarith)
    filter_upwards [hy_succ.eventually h_nhds] with n hn
    exact hn

  have h_h_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, h xbar xbar - ε < h (alg.x n) (alg.x (n+1)) := by
    have h_nhds : ∀ᶠ (z : X × X) in 𝓝 (xbar, xbar), h z.1 z.2 > h xbar xbar - ε :=
      (h_lsc (xbar, xbar)) (h xbar xbar - ε) (by linarith)
    filter_upwards [hx_pair.eventually h_nhds] with n hn
    exact hn

  have h_k_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, k ybar ybar - ε < k (alg.y n) (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ (z : Y × Y) in 𝓝 (ybar, ybar), k z.1 z.2 > k ybar ybar - ε :=
      (k_lsc (ybar, ybar)) (k ybar ybar - ε) (by linarith)
    filter_upwards [hy_pair.eventually h_nhds] with n hn
    exact hn

  have h_c_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, c xbar ybar - ε < c (alg.x (n+1)) (alg.y n) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - ε :=
      (c_lsc (xbar, ybar)) (c xbar ybar - ε) (by linarith)
    filter_upwards [hxy_pair_c.eventually h_nhds] with n hn
    exact hn

  have h_c2_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, c xbar ybar - ε < c (alg.x (n+1)) (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - ε :=
      (c_lsc (xbar, ybar)) (c xbar ybar - ε) (by linarith)
    filter_upwards [hxy_pair_c2.eventually h_nhds] with n hn
    exact hn

  -- Convergence: if a_n → a_inf, then for δ > 0, eventually a_n > a_inf - δ
  -- Use isOpen_Ioi: {x | a_inf - δ < x} is an open nhd of a_inf (since a_inf - δ < a_inf)
  have h_alpha_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, α_inf - δ < α n := by
    have h_open : IsOpen {x : ℝ | α_inf - δ < x} := isOpen_Ioi
    have h_mem : α_inf ∈ {x : ℝ | α_inf - δ < x} :=
      show α_inf - δ < α_inf by linarith
    have h_nhd : {x : ℝ | α_inf - δ < x} ∈ 𝓝 α_inf := h_open.mem_nhds h_mem
    filter_upwards [hα.eventually h_nhd] with n hn
    exact hn

  have h_beta_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, β_inf - δ < β n := by
    have h_open : IsOpen {x : ℝ | β_inf - δ < x} := isOpen_Ioi
    have h_mem : β_inf ∈ {x : ℝ | β_inf - δ < x} :=
      show β_inf - δ < β_inf by linarith
    have h_nhd : {x : ℝ | β_inf - δ < x} ∈ 𝓝 β_inf := h_open.mem_nhds h_mem
    filter_upwards [hβ.eventually h_nhd] with n hn
    exact hn

  have h_mu_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, μ_inf - δ < μ n := by
    have h_open : IsOpen {x : ℝ | μ_inf - δ < x} := isOpen_Ioi
    have h_mem : μ_inf ∈ {x : ℝ | μ_inf - δ < x} :=
      show μ_inf - δ < μ_inf by linarith
    have h_nhd : {x : ℝ | μ_inf - δ < x} ∈ 𝓝 μ_inf := h_open.mem_nhds h_mem
    filter_upwards [hμ.eventually h_nhd] with n hn
    exact hn

  have h_nu_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, ν_inf - δ < ν n := by
    have h_open : IsOpen {x : ℝ | ν_inf - δ < x} := isOpen_Ioi
    have h_mem : ν_inf ∈ {x : ℝ | ν_inf - δ < x} :=
      show ν_inf - δ < ν_inf by linarith
    have h_nhd : {x : ℝ | ν_inf - δ < x} ∈ 𝓝 ν_inf := h_open.mem_nhds h_mem
    filter_upwards [hν.eventually h_nhd] with n hn
    exact hn

  -- ============================================================
  -- RHS convergence (separate continuity + product of limits)
  -- ============================================================
  have hRHS_x (ξ : X) :
      Tendsto (fun n : ℕ => f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n)) atTop
      (𝓝 (f ξ + α_inf * h xbar ξ + β_inf * c ξ ybar)) := by
    have hhξ : Tendsto (fun n : ℕ => h (alg.x n) ξ) atTop (𝓝 (h xbar ξ)) :=
      ((h_sep1 ξ).tendsto xbar).comp hx
    have hcξ : Tendsto (fun n : ℕ => c ξ (alg.y n)) atTop (𝓝 (c ξ ybar)) :=
      ((c_sep2 ξ).tendsto ybar).comp hy
    have hαhξ : Tendsto (fun n : ℕ => α n * h (alg.x n) ξ) atTop (𝓝 (α_inf * h xbar ξ)) :=
      Filter.Tendsto.mul hα hhξ
    have hβcξ : Tendsto (fun n : ℕ => β n * c ξ (alg.y n)) atTop (𝓝 (β_inf * c ξ ybar)) :=
      Filter.Tendsto.mul hβ hcξ
    simpa [add_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => f ξ) atTop _).add hαhξ).add hβcξ

  have hRHS_y (η : Y) :
      Tendsto (fun n : ℕ => g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η) atTop
      (𝓝 (g η + μ_inf * c xbar η + ν_inf * k ybar η)) := by
    have hcη : Tendsto (fun n : ℕ => c (alg.x (n+1)) η) atTop (𝓝 (c xbar η)) :=
      ((c_sep1 η).tendsto xbar).comp hx_succ
    have hkη : Tendsto (fun n : ℕ => k (alg.y n) η) atTop (𝓝 (k ybar η)) :=
      ((k_sep1 η).tendsto ybar).comp hy
    have hμcη : Tendsto (fun n : ℕ => μ n * c (alg.x (n+1)) η) atTop (𝓝 (μ_inf * c xbar η)) :=
      Filter.Tendsto.mul hμ hcη
    have hνkη : Tendsto (fun n : ℕ => ν n * k (alg.y n) η) atTop (𝓝 (ν_inf * k ybar η)) :=
      Filter.Tendsto.mul hν hkη
    simpa [add_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => g η) atTop _).add hμcη).add hνkη

  -- ============================================================
  -- MAIN PROOF
  -- Product lower bound lemma: for nonnegative converging sequences,
  -- eventually a_n * b_n > a_lim * b_lim - ε
  -- ============================================================

  set_option maxHeartbeats 600000 in
  have h_prod_ev_lower {a_n b_n : ℕ → ℝ} {a_lim b_lim : ℝ} {ε : ℝ} (hε : ε > 0)
      (ha_nn : ∀ n, 0 ≤ a_n n) (hb_nn : ∀ n, 0 ≤ b_n n)
      (ha_tendsto : Tendsto a_n atTop (𝓝 a_lim))
      (hb_lim_nonneg : 0 ≤ b_lim)
      (hb_lower : ∀ δ > 0, ∀ᶠ n in atTop, b_lim - δ < b_n n) :
      ∀ᶠ n in atTop, a_lim * b_lim - ε < a_n n * b_n n := by
    have ha_lim_nonneg : 0 ≤ a_lim :=
      ge_of_tendsto ha_tendsto (eventually_atTop.mpr ⟨0, fun n _ => ha_nn n⟩)
    rcases eq_or_lt_of_le ha_lim_nonneg with (rfl | ha_lim_pos)
    · -- a_lim = 0: then a_lim * b_lim = 0, and a_n * b_n ≥ 0 > 0 - ε = -ε
      filter_upwards [] with n
      have h_nonneg_prod : 0 ≤ a_n n * b_n n := mul_nonneg (ha_nn n) (hb_nn n)
      linarith
    -- a_lim > 0 case. Choose η > 0 small enough
    set denom : ℝ := a_lim + b_lim + 1 with h_denom_def
    have h_denom_pos : 0 < denom := by
      dsimp [denom]; nlinarith
    set η := min (a_lim / 2) (ε / (2 * denom)) with hη_def
    have hη_pos : 0 < η := by
      refine lt_min_iff.mpr ⟨by linarith, div_pos hε (by nlinarith)⟩
    have hη_lt_a_lim : η < a_lim := by
      calc
        η ≤ a_lim / 2 := min_le_left _ _
        _ < a_lim := by nlinarith
    have h_prod_bound : a_lim * b_lim - ε < (a_lim - η) * (b_lim - η) := by
      have h_aux : η * (a_lim + b_lim - η) < ε := by
        have hη_le : η ≤ ε / (2 * denom) := min_le_right _ _
        have h_ineq : a_lim + b_lim - η < denom := by
          dsimp [denom]; nlinarith
        have h_mid : η * (a_lim + b_lim - η) < η * denom :=
          mul_lt_mul_of_pos_left h_ineq hη_pos
        have h_bound : η * denom ≤ ε / 2 := by
          calc
            η * denom ≤ (ε / (2 * denom)) * denom :=
              mul_le_mul_of_nonneg_right hη_le (by linarith)
            _ = ε / 2 := by
              field_simp [h_denom_pos.ne.symm]
        have h_eps_half_lt : ε / 2 < ε := by linarith
        nlinarith
      nlinarith
    have ha_ev : ∀ᶠ n in atTop, a_lim - η < a_n n := by
      have h_open : IsOpen {x : ℝ | a_lim - η < x} := isOpen_Ioi
      have h_mem : a_lim ∈ {x : ℝ | a_lim - η < x} :=
        show a_lim - η < a_lim by linarith
      have h_nhd : {x : ℝ | a_lim - η < x} ∈ 𝓝 a_lim := h_open.mem_nhds h_mem
      filter_upwards [ha_tendsto.eventually h_nhd] with n hn
      exact hn
    have hb_ev : ∀ᶠ n in atTop, b_lim - η < b_n n := hb_lower η hη_pos
    filter_upwards [ha_ev, hb_ev] with n ha_low hb_low
    have h_main : a_lim * b_lim - ε < a_n n * b_n n := by
      by_cases h_b_low_nonneg : 0 < b_lim - η
      · calc
          a_lim * b_lim - ε < (a_lim - η) * (b_lim - η) := h_prod_bound
          _ < a_n n * b_n n := mul_lt_mul ha_low hb_low.le h_b_low_nonneg (ha_nn n)
      · -- b_lim - η ≤ 0, so (a_lim - η) * (b_lim - η) ≤ 0 ≤ a_n n * b_n n
        have h_nonpos : (a_lim - η) * (b_lim - η) ≤ 0 := by
          have h_nonneg_a : 0 ≤ a_lim - η := by linarith
          nlinarith
        have h_nonneg_prod : 0 ≤ a_n n * b_n n := mul_nonneg (ha_nn n) (hb_nn n)
        linarith
    exact h_main

  -- x-INE condition
  have h_xine : ∀ (ξ : X), f xbar + β_inf * c xbar ybar + α_inf * h xbar xbar ≤
      f ξ + α_inf * h xbar ξ + β_inf * c ξ ybar := by
    intro ξ
    set L_target := f xbar + α_inf * h xbar xbar + β_inf * c xbar ybar
    set R_limit := f ξ + α_inf * h xbar ξ + β_inf * c ξ ybar
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    -- RHS convergence: eventually RHS_n < R_limit + ε/2
    have hRHS_ev : ∀ᶠ n in atTop,
        (f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n)) < R_limit + ε / 2 := by
      have ht := hRHS_x ξ
      have hball : Metric.ball (R_limit : ℝ) (ε / 2) ∈ 𝓝 (R_limit : ℝ) :=
        Metric.ball_mem_nhds R_limit (by linarith)
      filter_upwards [ht.eventually hball] with n hn
      have hball_mem : dist (f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n)) R_limit < ε / 2 := hn
      rw [Real.dist_eq] at hball_mem
      have h_abs := abs_lt.mp hball_mem
      linarith
    -- LHS lower bounds via product lemma
    have h_f_ev : ∀ᶠ n in atTop, f xbar - ε / 6 < f (alg.x (n+1)) :=
      h_fx_lower (ε / 6) (by linarith)
    have h_αh_ev : ∀ᶠ n in atTop, α_inf * h xbar xbar - ε / 6 < α n * h (alg.x n) (alg.x (n+1)) :=
      h_prod_ev_lower (by linarith) α_nn (λ n => h_nn _ _) hα h_hbar_nonneg h_h_lower
    have h_βc_ev : ∀ᶠ n in atTop, β_inf * c xbar ybar - ε / 6 < β n * c (alg.x (n+1)) (alg.y n) :=
      h_prod_ev_lower (by linarith) β_nn (λ n => c_nn _ _) hβ h_cbar_nonneg h_c_lower
    -- Gather all eventual bounds
    have h_all : ∀ᶠ n in atTop,
        f xbar - ε / 6 < f (alg.x (n+1)) ∧
        α_inf * h xbar xbar - ε / 6 < α n * h (alg.x n) (alg.x (n+1)) ∧
        β_inf * c xbar ybar - ε / 6 < β n * c (alg.x (n+1)) (alg.y n) ∧
        (f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
         f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n)) ∧
        (f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) < R_limit + ε / 2) := by
      filter_upwards [h_f_ev, h_αh_ev, h_βc_ev, hRHS_ev] with n hf h_αh h_βc hRHS
      have h_step : f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) +
          β n * c (alg.x (n+1)) (alg.y n) ≤
          f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) :=
        alg.step_x n ξ
      exact ⟨hf, h_αh, h_βc, h_step, hRHS⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hf, h_αh, h_βc, hstep, hRHS⟩
    -- Chain: L_target - ε/2 < LHS_n ≤ RHS_n < R_limit + ε/2
    have hLHS_lower : L_target - ε / 2 < f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) +
        β n * c (alg.x (n+1)) (alg.y n) := by
      dsimp [L_target]
      nlinarith
    have h_total : L_target < R_limit + ε := by
      nlinarith
    simpa [L_target, R_limit, add_comm, add_left_comm, add_assoc] using h_total

  -- y-INE condition (symmetric to x-INE)
  have h_yine : ∀ (η : Y), g ybar + μ_inf * c xbar ybar + ν_inf * k ybar ybar ≤
      g η + μ_inf * c xbar η + ν_inf * k ybar η := by
    intro η
    set L_target := g ybar + μ_inf * c xbar ybar + ν_inf * k ybar ybar
    set R_limit := g η + μ_inf * c xbar η + ν_inf * k ybar η
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    -- RHS convergence
    have hRHS_ev : ∀ᶠ n in atTop,
        (g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η) < R_limit + ε / 2 := by
      have ht := hRHS_y η
      have hball : Metric.ball (R_limit : ℝ) (ε / 2) ∈ 𝓝 (R_limit : ℝ) :=
        Metric.ball_mem_nhds R_limit (by linarith)
      filter_upwards [ht.eventually hball] with n hn
      have hball_mem : dist (g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η) R_limit < ε / 2 := hn
      rw [Real.dist_eq] at hball_mem
      have h_abs := abs_lt.mp hball_mem
      linarith
    -- LHS lower bounds via product lemma
    have h_g_ev : ∀ᶠ n in atTop, g ybar - ε / 6 < g (alg.y (n+1)) :=
      h_gy_lower (ε / 6) (by linarith)
    have h_μc_ev : ∀ᶠ n in atTop, μ_inf * c xbar ybar - ε / 6 < μ n * c (alg.x (n+1)) (alg.y (n+1)) :=
      h_prod_ev_lower (by linarith) μ_nn (λ n => c_nn _ _) hμ h_cbar_nonneg h_c2_lower
    have h_νk_ev : ∀ᶠ n in atTop, ν_inf * k ybar ybar - ε / 6 < ν n * k (alg.y n) (alg.y (n+1)) :=
      h_prod_ev_lower (by linarith) ν_nn (λ n => k_nn _ _) hν h_kbar_nonneg h_k_lower
    -- Gather all eventual bounds
    have h_all : ∀ᶠ n in atTop,
        g ybar - ε / 6 < g (alg.y (n+1)) ∧
        μ_inf * c xbar ybar - ε / 6 < μ n * c (alg.x (n+1)) (alg.y (n+1)) ∧
        ν_inf * k ybar ybar - ε / 6 < ν n * k (alg.y n) (alg.y (n+1)) ∧
        (g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) ≤
         g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η) ∧
        (g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η < R_limit + ε / 2) := by
      filter_upwards [h_g_ev, h_μc_ev, h_νk_ev, hRHS_ev] with n hg h_μc h_νk hRHS
      have h_step : g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) +
          ν n * k (alg.y n) (alg.y (n+1)) ≤
          g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η :=
        alg.step_y n η
      exact ⟨hg, h_μc, h_νk, h_step, hRHS⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hg, h_μc, h_νk, hstep, hRHS⟩
    -- Chain
    have hLHS_lower : L_target - ε / 2 < g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) +
        ν n * k (alg.y n) (alg.y (n+1)) := by
      dsimp [L_target]
      nlinarith
    have h_total : L_target < R_limit + ε := by
      nlinarith
    simpa [L_target, R_limit, add_comm, add_left_comm, add_assoc] using h_total

  refine ⟨?_, ?_⟩
  · intro ξ; simpa [add_comm, add_left_comm, add_assoc] using h_xine ξ
  · intro η; simpa [add_comm, add_left_comm, add_assoc] using h_yine η
