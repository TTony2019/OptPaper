## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/prop_1.lean`

## Lean statement
```lean
theorem proposition_2_1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (hyp : H11toH14 X Y f g h k c α β μ ν)
    (xbar : X) (ybar : Y) (hx : Tendsto alg.x atTop (𝓝 xbar)) (hy : Tendsto alg.y atTop (𝓝 ybar))
    (α_inf : ℝ) (hα : Tendsto α atTop (𝓝 α_inf))
    (β_inf : ℝ) (hβ : Tendsto β atTop (𝓝 β_inf))
    (μ_inf : ℝ) (hμ : Tendsto μ atTop (𝓝 μ_inf))
    (ν_inf : ℝ) (hν : Tendsto ν atTop (𝓝 ν_inf)) :
    IsINE f g h k c α_inf β_inf μ_inf ν_inf xbar ybar
```

## Statement explanation
The declaration says the following. Let $X$ and $Y$ be topological spaces. There are real-valued functions

$$
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,
$$

and two-variable real-valued functions

$$
h:X\times X\to\mathbb R,\qquad k:Y\times Y\to\mathbb R,\qquad c:X\times Y\to\mathbb R,
$$

where the Lean type $X\to X\to\mathbb R$ is the curried form of a function on $X\times X$. There are also four sequences of real numbers

$$
\alpha,\beta,\mu,\nu:\mathbb N\to\mathbb R.
$$

The hypothesis `alg : CA2 X Y f g h k c α β μ ν` supplies an alternating scheme whose state sequences are denoted by

$$
x_n:=\text{alg.x}(n)\in X,\qquad y_n:=\text{alg.y}(n)\in Y.
$$

The visible step inequalities from `alg` used in the proof are, for every $n\in\mathbb N$, every $\xi\in X$, and every $\eta\in Y$,

$$
f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n)
\le
f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n),
$$

and

$$
g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})
\le
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta).
$$

The hypothesis `hyp : H11toH14 ...` is unpacked in the proof into lower semicontinuity, boundedness, separate continuity, and nonnegativity assumptions. The components actually used are:

- $f$ is lower semicontinuous at $\bar x$, and $g$ is lower semicontinuous at $\bar y$;
- $h$ is lower semicontinuous at $(\bar x,\bar x)$, $k$ at $(\bar y,\bar y)$, and $c$ at $(\bar x,\bar y)$;
- the partial maps $x\mapsto h(x,\xi)$, $y\mapsto k(y,\eta)$, $x\mapsto c(x,\eta)$, and $y\mapsto c(\xi,y)$ are continuous;
- $h,k,c$ are nonnegative everywhere;
- the sequences $\alpha,\beta,\mu,\nu$ are nonnegative.

The components `f_bdd` and `g_bdd`, as well as the two final ignored components of `hyp`, are not used in the proof.

The convergence hypotheses are

$$
x_n\to \bar x,\qquad y_n\to \bar y,
$$

and

$$
\alpha_n\to \alpha_\infty,\qquad
\beta_n\to \beta_\infty,\qquad
\mu_n\to \mu_\infty,\qquad
\nu_n\to \nu_\infty.
$$

The conclusion `IsINE f g h k c α_inf β_inf μ_inf ν_inf xbar ybar` is, as revealed by the final two goals, the conjunction of the two limiting inequalities

$$
f(\bar x)+\beta_\infty c(\bar x,\bar y)+\alpha_\infty h(\bar x,\bar x)
\le
f(\xi)+\alpha_\infty h(\bar x,\xi)+\beta_\infty c(\xi,\bar y)
$$

for every $\xi\in X$, and

$$
g(\bar y)+\mu_\infty c(\bar x,\bar y)+\nu_\infty k(\bar y,\bar y)
\le
g(\eta)+\mu_\infty c(\bar x,\eta)+\nu_\infty k(\bar y,\eta)
$$

for every $\eta\in Y$. Thus the theorem says that if the alternating scheme converges and the parameter sequences converge, then the limit pair $(\bar x,\bar y)$ satisfies the limiting versions of the two optimality inequalities.

## Lean proof
```lean
by
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
```

## Proof explanation
The proof begins with `rcases hyp with ...`, which destructs the hypothesis `H11toH14` into its component assumptions: lower semicontinuity of $f,g,h,k,c$, separate continuity of $h,k,c$, nonnegativity of $h,k,c$, and nonnegativity of $\alpha,\beta,\mu,\nu$. It then further splits the separate-continuity hypotheses into their first- and second-variable parts. The proof does not use every component of `hyp`; only the lower semicontinuity, separate continuity, and nonnegativity parts are needed.

Next the proof builds shifted and paired convergence statements. From $x_n\to\bar x$, the sequence $x_{n+1}\to\bar x$, because the map $n\mapsto n+1$ tends to infinity on $\mathbb N$. The lemma `tendsto_add_atTop_nat 1` supplies precisely this fact, and composing it with `hx` gives `hx_succ`. Similarly, `hy_succ` gives $y_{n+1}\to\bar y$. The lemma `Filter.Tendsto.prodMk_nhds` says that if two sequences converge in their respective topological spaces, then the paired sequence converges in the product topology to the pair of limits. Thus the proof obtains

$$
(x_n,x_{n+1})\to(\bar x,\bar x),\qquad
(y_n,y_{n+1})\to(\bar y,\bar y),
$$

and

$$
(x_{n+1},y_n)\to(\bar x,\bar y),\qquad
(x_{n+1},y_{n+1})\to(\bar x,\bar y).
$$

These are exactly the inputs needed to apply lower semicontinuity of $h,k,c$ at the limit pairs.

The proof then shows that the limiting parameter values are nonnegative. For example, since $\alpha_n\ge0$ for every $n$, the sequence $\alpha_n$ is eventually nonnegative, and because $\alpha_n\to\alpha_\infty$, the lemma `ge_of_tendsto` gives $\alpha_\infty\ge0$. The same reasoning gives

$$
\beta_\infty\ge0,\qquad \mu_\infty\ge0,\qquad \nu_\infty\ge0.
$$

Directly from the nonnegativity assumptions for the two-variable functions, the proof also has

$$
h(\bar x,\bar x)\ge0,\qquad k(\bar y,\bar y)\ge0,\qquad c(\bar x,\bar y)\ge0.
$$

The lower semicontinuity hypotheses are then converted into eventual lower bounds along the algorithm. The definition of lower semicontinuity at a point says that if $u$ is a lower semicontinuity point of a function $\phi$, then for every real threshold $r<\phi(u)$, we have $\phi(z)>r$ for all $z$ sufficiently close to $u$. Taking $r=\phi(u)-\epsilon$ with $\epsilon>0$, this becomes: eventually near $u$,

$$
\phi(u)-\epsilon<\phi(z).
$$

Applying this to $f$ at $\bar x$ along $x_{n+1}\to\bar x$ gives eventually

$$
f(\bar x)-\epsilon<f(x_{n+1}).
$$

Similarly the proof obtains eventually

$$
g(\bar y)-\epsilon<g(y_{n+1}),
$$

$$
h(\bar x,\bar x)-\epsilon<h(x_n,x_{n+1}),
$$

$$
k(\bar y,\bar y)-\epsilon<k(y_n,y_{n+1}),
$$

$$
c(\bar x,\bar y)-\epsilon<c(x_{n+1},y_n),
$$

and

$$
c(\bar x,\bar y)-\epsilon<c(x_{n+1},y_{n+1}).
$$

The `filter_upwards` tactic is used repeatedly to pass from a neighborhood statement in the limit to the corresponding eventual statement along the convergent sequence.

Similarly, from convergence of the parameter sequences, the proof records that for every $\delta>0$, eventually

$$
\alpha_\infty-\delta<\alpha_n,
$$

and similarly for $\beta,\mu,\nu$. This is proved by observing that the interval $(\alpha_\infty-\delta,\infty)$ is open and contains $\alpha_\infty$, hence is a neighborhood of $\alpha_\infty$; convergence of $\alpha_n$ to $\alpha_\infty$ therefore eventually puts $\alpha_n$ inside that interval. The lemma `isOpen_Ioi` states that intervals of the form $\{x:\alpha_\infty-\delta<x\}$ are open, and `h_open.mem_nhds` turns membership into a neighborhood condition.

The proof next establishes convergence of the right-hand sides appearing in the step inequalities. For fixed $\xi\in X$, separate continuity of $h$ in the first variable gives $h(x_n,\xi)\to h(\bar x,\xi)$, and separate continuity of $c$ in the second variable gives $c(\xi,y_n)\to c(\xi,\bar y)$. Multiplying by the convergent sequences $\alpha_n$ and $\beta_n$ uses `Filter.Tendsto.mul`, which says that the product of two convergent real sequences converges to the product of the limits. Adding a constant sequence and using the sum rule for limits gives

$$
f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n)
\to
f(\xi)+\alpha_\infty h(\bar x,\xi)+\beta_\infty c(\xi,\bar y).
$$

This is `hRHS_x`. The symmetric statement `hRHS_y` gives, for fixed $\eta\in Y$,

$$
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta)
\to
g(\eta)+\mu_\infty c(\bar x,\eta)+\nu_\infty k(\bar y,\eta),
$$

using the convergence $x_{n+1}\to\bar x$, $y_n\to\bar y$ and the separate continuity of $c$ and $k$.

A central auxiliary lemma is `h_prod_ev_lower`. It states that if $a_n,b_n\ge0$, $a_n\to a_\infty$, $b_\infty\ge0$, and for every $\delta>0$ eventually $b_\infty-\delta<b_n$, then for every $\epsilon>0$, eventually

$$
a_\infty b_\infty-\epsilon<a_n b_n.
$$

The proof first derives $a_\infty\ge0$ by `ge_of_tendsto`. If $a_\infty=0$, then $a_\infty b_\infty=0$, and since $a_nb_n\ge0> -\epsilon$, the desired inequality is immediate. If $a_\infty>0$, the proof sets

$$
d=a_\infty+b_\infty+1>0
$$

and

$$
\eta=\min\left(\frac{a_\infty}{2},\frac{\epsilon}{2d}\right)>0.
$$

Then $\eta<a_\infty$. The elementary product estimate

$$
a_\infty b_\infty-\epsilon
<
(a_\infty-\eta)(b_\infty-\eta)
$$

follows because

$$
(a_\infty-\eta)(b_\infty-\eta)
=a_\infty b_\infty-\eta(a_\infty+b_\infty-\eta),
$$

and $\eta(a_\infty+b_\infty-\eta)<\epsilon$. This last inequality comes from $\eta\le\epsilon/(2d)$, $a_\infty+b_\infty-\eta<d$, and $\epsilon/2<\epsilon$. Since $a_n\to a_\infty$, eventually $a_\infty-\eta<a_n$; by the assumed lower bound for $b_n$, eventually $b_\infty-\eta<b_n$. If $b_\infty-\eta>0$, multiplying the two lower bounds gives

$$
(a_\infty-\eta)(b_\infty-\eta)<a_nb_n.
$$

If $b_\infty-\eta\le0$, then $(a_\infty-\eta)(b_\infty-\eta)\le0\le a_nb_n$, so the same conclusion holds. This lemma is used to handle products such as $\alpha_n h(x_n,x_{n+1})$, $\beta_n c(x_{n+1},y_n)$, $\mu_n c(x_{n+1},y_{n+1})$, and $\nu_n k(y_n,y_{n+1})$, where one factor converges and the other only has eventual lower bounds from lower semicontinuity.

The $x$-inequality is proved as follows. For fixed $\xi\in X$, define

$$
L=f(\bar x)+\alpha_\infty h(\bar x,\bar x)+\beta_\infty c(\bar x,\bar y)
$$

and

$$
R=f(\xi)+\alpha_\infty h(\bar x,\xi)+\beta_\infty c(\xi,\bar y).
$$

The goal is $L\le R$. The proof uses `le_of_forall_pos_lt_add`: it is enough to show $L<R+\epsilon$ for every $\epsilon>0$. Fix such an $\epsilon$. From `hRHS_x`, eventually the right-hand side of the $x$-step inequality is less than $R+\epsilon/2$. From lower semicontinuity and the product lemma, eventually each of the three terms on the left-hand side of the $x$-step inequality is larger than its limiting value minus $\epsilon/6$:

$$
f(\bar x)-\frac{\epsilon}{6}<f(x_{n+1}),
$$

$$
\alpha_\infty h(\bar x,\bar x)-\frac{\epsilon}{6}<\alpha_n h(x_n,x_{n+1}),
$$

$$
\beta_\infty c(\bar x,\bar y)-\frac{\epsilon}{6}<\beta_n c(x_{n+1},y_n).
$$

Combining these three eventual inequalities gives eventually

$$
L-\frac{\epsilon}{2}
<
f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n).
$$

But the $x$-step inequality of the algorithm says the right-hand side is at most

$$
f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n),
$$

and by the convergence bound this is eventually less than $R+\epsilon/2$. Since finitely many eventual statements hold simultaneously, `Filter.Eventually.exists` chooses an actual index $n$ satisfying all of them. Chaining the inequalities gives

$$
L-\frac{\epsilon}{2}<R+\frac{\epsilon}{2},
$$

hence $L<R+\epsilon$. Since $\epsilon>0$ was arbitrary, $L\le R$. The final `simpa` only reorders additions using commutativity and associativity to match the exact form of `IsINE`.

The $y$-inequality is proved in exactly the same way. For fixed $\eta\in Y$, set

$$
L'=g(\bar y)+\mu_\infty c(\bar x,\bar y)+\nu_\infty k(\bar y,\bar y)
$$

and

$$
R'=g(\eta)+\mu_\infty c(\bar x,\eta)+\nu_\infty k(\bar y,\eta).
$$

The convergence `hRHS_y` gives eventually

$$
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta)<R'+\frac{\epsilon}{2}.
$$

Lower semicontinuity gives eventually

$$
g(\bar y)-\frac{\epsilon}{6}<g(y_{n+1}),
$$

and the product lemma gives eventually

$$
\mu_\infty c(\bar x,\bar y)-\frac{\epsilon}{6}
<\mu_n c(x_{n+1},y_{n+1}),
$$

$$
\nu_\infty k(\bar y,\bar y)-\frac{\epsilon}{6}
<\nu_n k(y_n,y_{n+1}).
$$

Together with the $y$-step inequality of `alg`, these imply eventually

$$
L'-\frac{\epsilon}{2}
<
g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})
\le
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta)
<
R'+\frac{\epsilon}{2}.
$$

Thus $L'<R'+\epsilon$ for every $\epsilon>0$, so $L'\le R'$. The final `refine ⟨?_, ?_⟩` splits the conjunction `IsINE` into these two inequalities, and the two `simpa` commands identify the proved inequalities with the exact order of additions in the target statement.

