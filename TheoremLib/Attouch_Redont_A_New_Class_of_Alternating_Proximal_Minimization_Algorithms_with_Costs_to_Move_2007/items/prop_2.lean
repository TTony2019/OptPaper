import Mathlib

/-!
# Proposition 2.2: Limit Points with Bounded Parameters
From: H. Attouch, P. Redont, A. Soubeyran (2007).

Proof: uses the eventuality definition of lower semicontinuity to get
pointwise eventual lower bounds. No liminf decomposition needed.
Adapted from the Proposition 2.1 proof, handling α_n, ν_n with only
limsup bounds (rather than convergence).
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

def IsSeparatelyContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → Y → ℝ) : Prop :=
  (∀ (y : Y), Continuous (fun (x : X) => F x y)) ∧
  (∀ (x : X), Continuous (fun (y : Y) => F x y))

set_option maxHeartbeats 800000 in
theorem proposition_2_2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (xbar : X) (ybar : Y)
    (hx : Tendsto alg.x atTop (𝓝 xbar)) (hy : Tendsto alg.y atTop (𝓝 ybar))
    (hf_lsc : LowerSemicontinuous f) (hg_lsc : LowerSemicontinuous g)
    (hf_bdd_below : ∃ M : ℝ, ∀ x : X, f x ≥ M)
    (hg_bdd_below : ∃ M : ℝ, ∀ y : Y, g y ≥ M)
    (hh_lsc : LowerSemicontinuous (fun (p : X × X) => h p.1 p.2))
    (hk_lsc : LowerSemicontinuous (fun (p : Y × Y) => k p.1 p.2))
    (hc_lsc : LowerSemicontinuous (fun (p : X × Y) => c p.1 p.2))
    (hh_sep : IsSeparatelyContinuous h)
    (hk_sep : IsSeparatelyContinuous k)
    (hc_sep : IsSeparatelyContinuous c)
    (hh_nonneg : ∀ x x' : X, h x x' ≥ 0)
    (hk_nonneg : ∀ y y' : Y, k y y' ≥ 0)
    (hc_nonneg : ∀ x : X, ∀ y : Y, c x y ≥ 0)
    (hα_nonneg : ∀ n, α n ≥ 0) (hβ_nonneg : ∀ n, β n ≥ 0)
    (hμ_nonneg : ∀ n, μ n ≥ 0) (hν_nonneg : ∀ n, ν n ≥ 0)
    (β_inf : ℝ) (hβ : Tendsto β atTop (𝓝 β_inf))
    (μ_inf : ℝ) (hμ : Tendsto μ atTop (𝓝 μ_inf))
    (h_diag_h : ∀ x : X, h x x = 0) (h_diag_k : ∀ y : Y, k y y = 0)
    (αbar νbar : ℝ)
    (hαbar : ∀ ε > 0, ∀ᶠ n in atTop, α n ≤ αbar + ε)
    (hνbar : ∀ ε > 0, ∀ᶠ n in atTop, ν n ≤ νbar + ε)
    (α_val ν_val : ℝ) (hα_ge : α_val ≥ αbar) (hν_ge : ν_val ≥ νbar) :
    IsINE f g h k c α_val β_inf μ_inf ν_val xbar ybar := by
  -- Shifted convergence
  have hx_shift : Tendsto (fun n : ℕ => alg.x (n+1)) atTop (𝓝 xbar) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hy_shift : Tendsto (fun n : ℕ => alg.y (n+1)) atTop (𝓝 ybar) :=
    hy.comp (tendsto_add_atTop_nat 1)
  rcases hh_sep with ⟨hh_sep1, hh_sep2⟩
  rcases hk_sep with ⟨hk_sep1, hk_sep2⟩
  rcases hc_sep with ⟨hc_sep1, hc_sep2⟩

  -- ============================================================
  -- Nonnegativity of limsup bounds (follows from α_n ≥ 0)
  -- ============================================================
  have h_αbar_nonneg : αbar ≥ 0 := by
    by_contra! h_neg
    -- h_neg: αbar < 0
    have h_ε_pos : 0 < -αbar / 2 := by linarith
    have h_event : ∀ᶠ n in atTop, α n ≤ αbar + (-αbar / 2) := hαbar (-αbar / 2) h_ε_pos
    have h_simp : αbar + (-αbar / 2) = αbar / 2 := by ring
    have h_bound_ev : ∀ᶠ n in atTop, α n ≤ αbar / 2 := by
      simpa [h_simp] using h_event
    have h_neg_bound : αbar / 2 < 0 := by linarith
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_bound_ev
    have h_nonneg_n : α n ≥ 0 := hα_nonneg n
    linarith

  have h_νbar_nonneg : νbar ≥ 0 := by
    by_contra! h_neg
    -- h_neg: νbar < 0
    have h_ε_pos : 0 < -νbar / 2 := by linarith
    have h_event : ∀ᶠ n in atTop, ν n ≤ νbar + (-νbar / 2) := hνbar (-νbar / 2) h_ε_pos
    have h_simp : νbar + (-νbar / 2) = νbar / 2 := by ring
    have h_bound_ev : ∀ᶠ n in atTop, ν n ≤ νbar / 2 := by
      simpa [h_simp] using h_event
    have h_neg_bound : νbar / 2 < 0 := by linarith
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_bound_ev
    have h_nonneg_n : ν n ≥ 0 := hν_nonneg n
    linarith

  -- ============================================================
  -- Limits of β, μ are nonnegative
  -- ============================================================
  have h_βinf_nonneg : β_inf ≥ 0 :=
    ge_of_tendsto hβ (eventually_atTop.mpr ⟨0, fun n _ => hβ_nonneg n⟩)
  have h_μinf_nonneg : μ_inf ≥ 0 :=
    ge_of_tendsto hμ (eventually_atTop.mpr ⟨0, fun n _ => hμ_nonneg n⟩)

  -- ============================================================
  -- Nonnegativity of limit evaluations
  -- ============================================================
  have h_hbar_nonneg : h xbar xbar ≥ 0 := hh_nonneg _ _
  have h_kbar_nonneg : k ybar ybar ≥ 0 := hk_nonneg _ _
  have h_cbar_nonneg : c xbar ybar ≥ 0 := hc_nonneg _ _

  -- ============================================================
  -- Joint convergence of pairs
  -- ============================================================
  have hxy_pair_c : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y n)) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_shift hy

  -- ============================================================
  -- LSC EVENTUAL LOWER BOUNDS
  -- ============================================================
  have h_fx_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, f xbar - ε < f (alg.x (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 xbar, f z > f xbar - ε :=
      (hf_lsc xbar) (f xbar - ε) (by linarith)
    filter_upwards [hx_shift.eventually h_nhds] with n hn
    exact hn

  have h_c_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, c xbar ybar - ε < c (alg.x (n+1)) (alg.y n) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - ε :=
      (hc_lsc (xbar, ybar)) (c xbar ybar - ε) (by linarith)
    filter_upwards [hxy_pair_c.eventually h_nhds] with n hn
    exact hn

  have h_gy_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, g ybar - ε < g (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 ybar, g z > g ybar - ε :=
      (hg_lsc ybar) (g ybar - ε) (by linarith)
    filter_upwards [hy_shift.eventually h_nhds] with n hn
    exact hn

  -- Pair (x_{n+1}, y_{n+1})
  have hxy_pair_c2 : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y (n+1))) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_shift hy_shift

  have h_c2_lower (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in atTop, c xbar ybar - ε < c (alg.x (n+1)) (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - ε :=
      (hc_lsc (xbar, ybar)) (c xbar ybar - ε) (by linarith)
    filter_upwards [hxy_pair_c2.eventually h_nhds] with n hn
    exact hn

  -- ============================================================
  -- β-lower bound (converging sequence)
  -- ============================================================
  have h_beta_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, β_inf - δ < β n := by
    have h_open : IsOpen {x : ℝ | β_inf - δ < x} := isOpen_Ioi
    have h_mem : β_inf ∈ {x : ℝ | β_inf - δ < x} := show β_inf - δ < β_inf by linarith
    have h_nhd : {x : ℝ | β_inf - δ < x} ∈ 𝓝 β_inf := h_open.mem_nhds h_mem
    filter_upwards [hβ.eventually h_nhd] with n hn
    exact hn

  have h_mu_lower (δ : ℝ) (hδ : δ > 0) : ∀ᶠ n in atTop, μ_inf - δ < μ n := by
    have h_open : IsOpen {x : ℝ | μ_inf - δ < x} := isOpen_Ioi
    have h_mem : μ_inf ∈ {x : ℝ | μ_inf - δ < x} := show μ_inf - δ < μ_inf by linarith
    have h_nhd : {x : ℝ | μ_inf - δ < x} ∈ 𝓝 μ_inf := h_open.mem_nhds h_mem
    filter_upwards [hμ.eventually h_nhd] with n hn
    exact hn

  -- ============================================================
  -- PRODUCT LOWER BOUND LEMMA (adapted from prop_1)
  -- For nonnegative converging a_n, and b_n with lsc lower bound:
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

  -- ============================================================
  -- UPPER BOUND LEMMA: for α_n with limsup ≤ αbar,
  -- and h(x_n, ξ) → h(xbar, ξ) via separate continuity,
  -- we have eventually α_n * h(x_n, ξ) < αbar * h(xbar, ξ) + ε
  -- ============================================================
  have h_αh_upper_bound (ξ : X) (ε : ℝ) (hε : ε > 0) :
      ∀ᶠ n in atTop, α n * h (alg.x n) ξ < αbar * h xbar ξ + ε := by
    have h_hξ_nonneg : h xbar ξ ≥ 0 := hh_nonneg _ _
    have h_hξ_tendsto : Tendsto (fun n : ℕ => h (alg.x n) ξ) atTop (𝓝 (h xbar ξ)) :=
      (hh_sep1 ξ).continuousAt.tendsto.comp hx
    -- Choose δ small enough so that (αbar + δ)*(h(xbar,ξ) + δ) < αbar*h(xbar,ξ) + ε
    -- Need to handle the case where αbar + h(xbar,ξ) = 0 carefully
    set coeff : ℝ := αbar + h xbar ξ + 1 with h_coeff
    have h_coeff_pos : 0 < coeff := by
      dsimp [coeff]; nlinarith
    set δ := min ((ε / (2 * coeff))) 1 with hδ_def
    have hδ_pos : 0 < δ := by
      refine lt_min_iff.mpr ⟨div_pos hε (by nlinarith), by norm_num⟩
    have hδ_le : δ ≤ 1 := min_le_right _ _
    have hδ_le_eps_div : δ ≤ ε / (2 * coeff) := min_le_left _ _
    have hδ_mul : δ * coeff ≤ (ε / (2 * coeff)) * coeff :=
      mul_le_mul_of_nonneg_right hδ_le_eps_div (by linarith)
    have h_bound : (αbar + δ) * (h xbar ξ + δ) < αbar * h xbar ξ + ε := by
      calc
        (αbar + δ) * (h xbar ξ + δ) = αbar * h xbar ξ + δ * (αbar + h xbar ξ + δ) := by ring
        _ ≤ αbar * h xbar ξ + δ * (αbar + h xbar ξ + 1) := by
          have : αbar + h xbar ξ + δ ≤ αbar + h xbar ξ + 1 := by linarith
          nlinarith
        _ = αbar * h xbar ξ + δ * coeff := by simp [coeff]
        _ ≤ αbar * h xbar ξ + (ε / (2 * coeff)) * coeff := by linarith
        _ = αbar * h xbar ξ + ε / 2 := by
          field_simp [h_coeff_pos.ne.symm]
        _ < αbar * h xbar ξ + ε := by linarith
    -- Get eventual bounds
    have h_α_bound : ∀ᶠ n in atTop, α n ≤ αbar + δ := hαbar δ hδ_pos
    -- Note: α n ≥ 0, so α n ≤ αbar + δ (but α n could be ≤ the bound trivially)
    have h_h_close : ∀ᶠ n in atTop, h (alg.x n) ξ < h xbar ξ + δ := by
      have h_nhd : Metric.ball (h xbar ξ) δ ∈ 𝓝 (h xbar ξ) :=
        Metric.ball_mem_nhds (h xbar ξ) hδ_pos
      filter_upwards [h_hξ_tendsto.eventually h_nhd] with n hn
      rw [Real.dist_eq] at hn
      have h_lt := (abs_lt.mp hn).right
      linarith
    filter_upwards [h_α_bound, h_h_close] with n hn_α hn_h
    -- Now α n ≤ αbar + δ and h(x_n, ξ) < h(xbar, ξ) + δ
    -- Since α_n ≥ 0 and h(xbar, ξ) ≥ 0, δ ≤ 1, we have:
    -- α n * h(x_n, ξ) ≤ (αbar + δ) * (h(xbar, ξ) + δ) < αbar * h(xbar, ξ) + ε
    have h_nonneg_h : 0 ≤ h (alg.x n) ξ := hh_nonneg _ _
    have h_nonneg_hbar_add_δ : 0 ≤ h xbar ξ + δ := by nlinarith
    calc
      α n * h (alg.x n) ξ ≤ (αbar + δ) * h (alg.x n) ξ :=
        mul_le_mul_of_nonneg_right hn_α h_nonneg_h
      _ ≤ (αbar + δ) * (h xbar ξ + δ) :=
        mul_le_mul_of_nonneg_left hn_h.le (by nlinarith [h_αbar_nonneg])
      _ < αbar * h xbar ξ + ε := h_bound

  -- ============================================================
  -- UPPER BOUND LEMMA for ν_n * k(y_n, η)
  -- ============================================================
  have h_νk_upper_bound (η : Y) (ε : ℝ) (hε : ε > 0) :
      ∀ᶠ n in atTop, ν n * k (alg.y n) η < νbar * k ybar η + ε := by
    have h_kη_nonneg : k ybar η ≥ 0 := hk_nonneg _ _
    have h_kη_tendsto : Tendsto (fun n : ℕ => k (alg.y n) η) atTop (𝓝 (k ybar η)) :=
      (hk_sep1 η).continuousAt.tendsto.comp hy
    set coeff : ℝ := νbar + k ybar η + 1 with h_coeff
    have h_coeff_pos : 0 < coeff := by
      dsimp [coeff]; nlinarith
    set δ := min ((ε / (2 * coeff))) 1 with hδ_def
    have hδ_pos : 0 < δ := by
      refine lt_min_iff.mpr ⟨div_pos hε (by nlinarith), by norm_num⟩
    have hδ_le : δ ≤ 1 := min_le_right _ _
    have hδ_le_eps_div : δ ≤ ε / (2 * coeff) := min_le_left _ _
    have hδ_mul : δ * coeff ≤ (ε / (2 * coeff)) * coeff :=
      mul_le_mul_of_nonneg_right hδ_le_eps_div (by linarith)
    have h_bound : (νbar + δ) * (k ybar η + δ) < νbar * k ybar η + ε := by
      calc
        (νbar + δ) * (k ybar η + δ) = νbar * k ybar η + δ * (νbar + k ybar η + δ) := by ring
        _ ≤ νbar * k ybar η + δ * (νbar + k ybar η + 1) := by
          have : νbar + k ybar η + δ ≤ νbar + k ybar η + 1 := by linarith
          nlinarith
        _ = νbar * k ybar η + δ * coeff := by simp [coeff]
        _ ≤ νbar * k ybar η + (ε / (2 * coeff)) * coeff := by linarith
        _ = νbar * k ybar η + ε / 2 := by
          field_simp [h_coeff_pos.ne.symm]
        _ < νbar * k ybar η + ε := by linarith
    have h_ν_bound : ∀ᶠ n in atTop, ν n ≤ νbar + δ := hνbar δ hδ_pos
    have h_k_close : ∀ᶠ n in atTop, k (alg.y n) η < k ybar η + δ := by
      have h_nhd : Metric.ball (k ybar η) δ ∈ 𝓝 (k ybar η) :=
        Metric.ball_mem_nhds (k ybar η) hδ_pos
      filter_upwards [h_kη_tendsto.eventually h_nhd] with n hn
      rw [Real.dist_eq] at hn
      have h_lt := (abs_lt.mp hn).right
      linarith
    filter_upwards [h_ν_bound, h_k_close] with n hn_ν hn_k
    have h_nonneg_k : 0 ≤ k (alg.y n) η := hk_nonneg _ _
    calc
      ν n * k (alg.y n) η ≤ (νbar + δ) * k (alg.y n) η :=
        mul_le_mul_of_nonneg_right hn_ν h_nonneg_k
      _ ≤ (νbar + δ) * (k ybar η + δ) :=
        mul_le_mul_of_nonneg_left hn_k.le (by nlinarith [h_νbar_nonneg])
      _ < νbar * k ybar η + ε := h_bound

  -- ============================================================
  -- RHS CONVERGENCE (excluding α_n terms which don't converge)
  -- β_n * c(ξ, y_n) → β_inf * c(ξ, ybar) (converges)
  -- ============================================================
  have hRHS_x_partial (ξ : X) :
      Tendsto (fun n : ℕ => f ξ + β n * c ξ (alg.y n)) atTop
      (𝓝 (f ξ + β_inf * c ξ ybar)) := by
    have hcξ : Tendsto (fun n : ℕ => c ξ (alg.y n)) atTop (𝓝 (c ξ ybar)) :=
      ((hc_sep2 ξ).continuousAt.tendsto).comp hy
    have hβcξ : Tendsto (fun n : ℕ => β n * c ξ (alg.y n)) atTop (𝓝 (β_inf * c ξ ybar)) :=
      Filter.Tendsto.mul hβ hcξ
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => f ξ) atTop _).add hβcξ)

  -- ============================================================
  -- MAIN PROOF: First INE conjunct (x-coordinate)
  -- f xbar + β_inf * c xbar ybar ≤ f ξ + β_inf * c ξ ybar + α_val * h xbar ξ
  -- ============================================================
  have h_xine : ∀ (ξ : X), f xbar + β_inf * c xbar ybar + α_val * h xbar xbar ≤
      f ξ + β_inf * c ξ ybar + α_val * h xbar ξ := by
    intro ξ
    have h_hbar_diag_zero : h xbar xbar = 0 := h_diag_h xbar
    -- The goal simplifies to: f xbar + β_inf * c xbar ybar ≤ f ξ + β_inf * c ξ ybar + α_val * h xbar ξ
    have h_target : f xbar + β_inf * c xbar ybar + α_val * h xbar xbar =
        f xbar + β_inf * c xbar ybar := by
      simp [h_hbar_diag_zero]
    rw [h_target]
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    -- Write ε = ε₁ + ε₂ + ε₃ (three sources of error)
    set ε₀ := ε / 5 with hε₀
    have hε₀pos : ε₀ > 0 := by linarith
    -- (1) f(xbar) - ε₀ < f(x_{n+1}) eventually
    have h_f_ev : ∀ᶠ n in atTop, f xbar - ε₀ < f (alg.x (n+1)) :=
      h_fx_lower ε₀ hε₀pos
    -- (2) β_inf * c(xbar, ybar) - ε₀ < β_n * c(x_{n+1}, y_n) eventually (product lemma)
    have h_βc_ev : ∀ᶠ n in atTop, β_inf * c xbar ybar - ε₀ < β n * c (alg.x (n+1)) (alg.y n) :=
      h_prod_ev_lower hε₀pos hβ_nonneg (λ n => hc_nonneg _ _) hβ h_cbar_nonneg h_c_lower
    -- (3) α_n * h(x_n, x_{n+1}) ≥ 0 (dropped from LHS)
    have h_αh_nonneg (n : ℕ) : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) :=
      mul_nonneg (hα_nonneg n) (hh_nonneg _ _)
    -- (4) RHS partial bound: f(ξ) + β_n * c(ξ, y_n) < f(ξ) + β_inf * c(ξ, ybar) + ε₀
    have hRHS_partial_ev : ∀ᶠ n in atTop,
        f ξ + β n * c ξ (alg.y n) < f ξ + β_inf * c ξ ybar + ε₀ := by
      have ht := hRHS_x_partial ξ
      have hball : Metric.ball (f ξ + β_inf * c ξ ybar : ℝ) ε₀ ∈ 𝓝 (f ξ + β_inf * c ξ ybar : ℝ) :=
        Metric.ball_mem_nhds _ hε₀pos
      filter_upwards [ht.eventually hball] with n hn
      have hdist : dist (f ξ + β n * c ξ (alg.y n)) (f ξ + β_inf * c ξ ybar) < ε₀ := hn
      rw [Real.dist_eq] at hdist
      have h_abs := abs_lt.mp hdist
      linarith
    -- (5) α_n * h(x_n, ξ) < αbar * h(xbar, ξ) + ε₀ eventually (upper bound lemma)
    have h_αh_upper_ev : ∀ᶠ n in atTop, α n * h (alg.x n) ξ < αbar * h xbar ξ + ε₀ :=
      h_αh_upper_bound ξ ε₀ hε₀pos
    -- Gather all eventual bounds
    have h_all : ∀ᶠ n in atTop,
        f xbar - ε₀ < f (alg.x (n+1)) ∧
        β_inf * c xbar ybar - ε₀ < β n * c (alg.x (n+1)) (alg.y n) ∧
        (f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
         f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n)) ∧
        α n * h (alg.x n) ξ < αbar * h xbar ξ + ε₀ ∧
        f ξ + β n * c ξ (alg.y n) < f ξ + β_inf * c ξ ybar + ε₀ := by
      filter_upwards [h_f_ev, h_βc_ev, h_αh_upper_ev, hRHS_partial_ev] with
        n hf hβc hαh_upper hRHSpart
      have h_step : f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) +
          β n * c (alg.x (n+1)) (alg.y n) ≤
          f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) :=
        alg.step_x n ξ
      exact ⟨hf, hβc, h_step, hαh_upper, hRHSpart⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hf, hβc, hstep, hαh_upper, hRHSpart⟩
    -- Chain inequalities:
    -- LHS: (f(xbar) - ε₀) + (β_inf*c(xbar,ybar) - ε₀) < LHS_n
    -- LHS_n ≤ RHS_n (from algorithm)
    -- RHS_n = f(ξ) + α_n*h(x_n,ξ) + β_n*c(ξ,y_n) < f(ξ) + (αbar*h(xbar,ξ) + ε₀) + (f(ξ) + β_inf*c(ξ,ybar) + ε₀ - f(ξ))
    -- Wait, RHS_n = f(ξ) + α_n*h(x_n,ξ) + β_n*c(ξ,y_n)
    -- < f(ξ) + (αbar*h(xbar,ξ) + ε₀) + β_n*c(ξ,y_n) [using hαh_upper]
    -- Let's do: RHS_n < f(ξ) + αbar*h(xbar,ξ) + ε₀ + β_n*c(ξ,y_n)
    -- And β_n*c(ξ,y_n) < f(ξ) + β_inf*c(ξ,ybar) + ε₀ - f(ξ) = β_inf*c(ξ,ybar) + ε₀ [from hRHSpart]
    -- So RHS_n < f(ξ) + αbar*h(xbar,ξ) + β_inf*c(ξ,ybar) + 2ε₀
    -- Now use α_val ≥ αbar: αbar*h(xbar,ξ) ≤ α_val*h(xbar,ξ)
    -- RHS_n < f(ξ) + α_val*h(xbar,ξ) + β_inf*c(ξ,ybar) + 2ε₀
    -- And LHS_n ≤ RHS_n from algorithm, combined with LHS lower bound:
    -- f(xbar) + β_inf*c(xbar,ybar) - 2ε₀ < LHS_n + α_n*h(x_n,x_{n+1}) [hmm, we need to be careful]
    -- Actually: LHS_n = f(x_{n+1}) + α_n*h(x_n, x_{n+1}) + β_n*c(x_{n+1},y_n)
    -- Since α_n*h(x_n, x_{n+1}) ≥ 0:
    -- f(x_{n+1}) + β_n*c(x_{n+1},y_n) ≤ LHS_n
    -- But hstep gives: LHS_n ≤ RHS_n
    -- Lower bound on f + βc: (f(xbar) - ε₀) + (β_inf*c(xbar,ybar) - ε₀) < f(x_{n+1}) + β_n*c(x_{n+1},y_n)
    -- So: f(xbar) + β_inf*c(xbar,ybar) - 2ε₀ < f(x_{n+1}) + β_n*c(x_{n+1},y_n) ≤ LHS_n ≤ RHS_n
    -- RHS_n = f(ξ) + α_n*h(x_n,ξ) + β_n*c(ξ,y_n)
    -- < f(ξ) + (αbar*h(xbar,ξ) + ε₀) + (β_inf*c(ξ,ybar) + ε₀)  [subtracting f(ξ) from hRHSpart]
    -- Wait: hRHSpart says f(ξ) + β_n*c(ξ,y_n) < f(ξ) + β_inf*c(ξ,ybar) + ε₀
    -- So β_n*c(ξ,y_n) < β_inf*c(ξ,ybar) + ε₀
    -- And hαh_upper says α_n*h(x_n,ξ) < αbar*h(xbar,ξ) + ε₀
    -- So RHS_n = f(ξ) + α_n*h(x_n,ξ) + β_n*c(ξ,y_n)
    -- < f(ξ) + αbar*h(xbar,ξ) + ε₀ + β_inf*c(ξ,ybar) + ε₀
    -- = f(ξ) + αbar*h(xbar,ξ) + β_inf*c(ξ,ybar) + 2ε₀
    -- Now since α_val ≥ αbar and h(xbar,ξ) ≥ 0:
    -- αbar*h(xbar,ξ) ≤ α_val*h(xbar,ξ)
    -- So RHS_n < f(ξ) + α_val*h(xbar,ξ) + β_inf*c(ξ,ybar) + 2ε₀
    -- Therefore: f(xbar) + β_inf*c(xbar,ybar) - 2ε₀ < f(ξ) + α_val*h(xbar,ξ) + β_inf*c(ξ,ybar) + 2ε₀
    -- So: f(xbar) + β_inf*c(xbar,ybar) < f(ξ) + α_val*h(xbar,ξ) + β_inf*c(ξ,ybar) + 4ε₀
    -- And 4ε₀ = 4ε/5 < ε, done.
    have hLHS_simple_lower : f xbar + β_inf * c xbar ybar - 2 * ε₀ <
        f (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) := by
      nlinarith
    have hLHS_le_RHS : f (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
        f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) := by
      have h_nonneg_term : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) := h_αh_nonneg n
      linarith
    have hRHS_upper : f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) <
        f ξ + α_val * h xbar ξ + β_inf * c ξ ybar + 2 * ε₀ := by
      -- α_n*h(x_n,ξ) < αbar*h(xbar,ξ) + ε₀ ≤ α_val*h(xbar,ξ) + ε₀ (since h ≥ 0)
      have h_α_term : α n * h (alg.x n) ξ ≤ α_val * h xbar ξ + ε₀ := by
        have h_nonneg_h : 0 ≤ h xbar ξ := hh_nonneg _ _
        have : αbar * h xbar ξ ≤ α_val * h xbar ξ :=
          mul_le_mul_of_nonneg_right hα_ge h_nonneg_h
        linarith
      -- β_n*c(ξ,y_n) < β_inf*c(ξ,ybar) + ε₀ (from hRHSpart)
      -- hRHSpart: f(ξ) + β_n*c(ξ,y_n) < f(ξ) + β_inf*c(ξ,ybar) + ε₀
      -- So β_n*c(ξ,y_n) < β_inf*c(ξ,ybar) + ε₀
      nlinarith
    have h_final : f xbar + β_inf * c xbar ybar <
        f ξ + α_val * h xbar ξ + β_inf * c ξ ybar + ε := by
      nlinarith
    linarith

  -- ============================================================
  -- MAIN PROOF: Second INE conjunct (y-coordinate)
  -- g ybar + μ_inf * c xbar ybar ≤ g η + μ_inf * c xbar η + ν_val * k ybar η
  -- ============================================================
  have h_yine : ∀ (η : Y), g ybar + μ_inf * c xbar ybar + ν_val * k ybar ybar ≤
      g η + μ_inf * c xbar η + ν_val * k ybar η := by
    intro η
    have h_kbar_diag_zero : k ybar ybar = 0 := h_diag_k ybar
    -- The goal simplifies to: g ybar + μ_inf * c xbar ybar ≤ g η + μ_inf * c xbar η + ν_val * k ybar η
    have h_target : g ybar + μ_inf * c xbar ybar + ν_val * k ybar ybar =
        g ybar + μ_inf * c xbar ybar := by
      simp [h_kbar_diag_zero]
    rw [h_target]
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    set ε₀ := ε / 5 with hε₀
    have hε₀pos : ε₀ > 0 := by linarith
    -- (1) g(ybar) - ε₀ < g(y_{n+1}) eventually
    have h_g_ev : ∀ᶠ n in atTop, g ybar - ε₀ < g (alg.y (n+1)) :=
      h_gy_lower ε₀ hε₀pos
    -- (2) μ_inf * c(xbar, ybar) - ε₀ < μ_n * c(x_{n+1}, y_{n+1}) eventually (product lemma)
    have h_μc_ev : ∀ᶠ n in atTop, μ_inf * c xbar ybar - ε₀ < μ n * c (alg.x (n+1)) (alg.y (n+1)) :=
      h_prod_ev_lower hε₀pos hμ_nonneg (λ n => hc_nonneg _ _) hμ h_cbar_nonneg h_c2_lower
    -- (3) ν_n * k(y_n, y_{n+1}) ≥ 0 (dropped from LHS)
    have h_νk_nonneg (n : ℕ) : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) :=
      mul_nonneg (hν_nonneg n) (hk_nonneg _ _)
    -- (4) RHS partial bound (c(x_{n+1}, η) → c(xbar, η), μ_n → μ_inf converge)
    have hRHS_y_partial (η : Y) :
        Tendsto (fun n : ℕ => g η + μ n * c (alg.x (n+1)) η) atTop
        (𝓝 (g η + μ_inf * c xbar η)) := by
      have hcη : Tendsto (fun n : ℕ => c (alg.x (n+1)) η) atTop (𝓝 (c xbar η)) :=
        ((hc_sep1 η).continuousAt.tendsto).comp hx_shift
      have hμcη : Tendsto (fun n : ℕ => μ n * c (alg.x (n+1)) η) atTop (𝓝 (μ_inf * c xbar η)) :=
        Filter.Tendsto.mul hμ hcη
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => g η) atTop _).add hμcη)
    have hRHS_partial_ev : ∀ᶠ n in atTop,
        g η + μ n * c (alg.x (n+1)) η < g η + μ_inf * c xbar η + ε₀ := by
      have ht := hRHS_y_partial η
      have hball : Metric.ball (g η + μ_inf * c xbar η : ℝ) ε₀ ∈ 𝓝 (g η + μ_inf * c xbar η : ℝ) :=
        Metric.ball_mem_nhds _ hε₀pos
      filter_upwards [ht.eventually hball] with n hn
      have hdist : dist (g η + μ n * c (alg.x (n+1)) η) (g η + μ_inf * c xbar η) < ε₀ := hn
      rw [Real.dist_eq] at hdist
      have h_abs := abs_lt.mp hdist
      linarith
    -- (5) ν_n * k(y_n, η) < νbar * k(ybar, η) + ε₀ eventually (upper bound lemma)
    have h_νk_upper_ev : ∀ᶠ n in atTop, ν n * k (alg.y n) η < νbar * k ybar η + ε₀ :=
      h_νk_upper_bound η ε₀ hε₀pos
    -- Gather all eventual bounds
    have h_all : ∀ᶠ n in atTop,
        g ybar - ε₀ < g (alg.y (n+1)) ∧
        μ_inf * c xbar ybar - ε₀ < μ n * c (alg.x (n+1)) (alg.y (n+1)) ∧
        (g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) ≤
         g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η) ∧
        ν n * k (alg.y n) η < νbar * k ybar η + ε₀ ∧
        g η + μ n * c (alg.x (n+1)) η < g η + μ_inf * c xbar η + ε₀ := by
      filter_upwards [h_g_ev, h_μc_ev, h_νk_upper_ev, hRHS_partial_ev] with
        n hg hμc hνk_upper hRHSpart
      have h_step : g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) +
          ν n * k (alg.y n) (alg.y (n+1)) ≤
          g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η :=
        alg.step_y n η
      exact ⟨hg, hμc, h_step, hνk_upper, hRHSpart⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hg, hμc, hstep, hνk_upper, hRHSpart⟩
    -- Chain inequalities (same pattern as x-coordinate)
    have hLHS_simple_lower : g ybar + μ_inf * c xbar ybar - 2 * ε₀ <
        g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) := by
      nlinarith
    have hLHS_le_RHS : g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) ≤
        g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η := by
      have h_nonneg_term : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) := h_νk_nonneg n
      linarith
    have hRHS_upper : g η + μ n * c (alg.x (n+1)) η + ν n * k (alg.y n) η <
        g η + ν_val * k ybar η + μ_inf * c xbar η + 2 * ε₀ := by
      have h_ν_term : ν n * k (alg.y n) η ≤ ν_val * k ybar η + ε₀ := by
        have h_nonneg_k : 0 ≤ k ybar η := hk_nonneg _ _
        have : νbar * k ybar η ≤ ν_val * k ybar η :=
          mul_le_mul_of_nonneg_right hν_ge h_nonneg_k
        linarith
      nlinarith
    have h_final : g ybar + μ_inf * c xbar ybar <
        g η + ν_val * k ybar η + μ_inf * c xbar η + ε := by
      nlinarith
    nlinarith

  refine ⟨?_, ?_⟩
  · intro ξ
    -- Need: f xbar + β_inf * c xbar ybar + α_val * h xbar xbar ≤ f ξ + β_inf * c ξ ybar + α_val * h xbar ξ
    -- This is exactly h_xine ξ
    have h := h_xine ξ
    -- h_xine ξ gives: f xbar + β_inf * c xbar ybar + α_val * h xbar xbar ≤ f ξ + β_inf * c ξ ybar + α_val * h xbar ξ
    -- But the IsINE definition has the terms in a different order. Use ring/add_comm/add_assoc.
    simpa [add_comm, add_left_comm, add_assoc] using h
  · intro η
    have h := h_yine η
    simpa [add_comm, add_left_comm, add_assoc] using h
