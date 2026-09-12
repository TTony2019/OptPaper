## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/thm_3.lean`

## Lean statement
```lean
theorem theorem_3_1 {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X] [CompleteSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν ε : ℕ → ℝ} (alg : ACA2 X Y f g h k c α β μ ν ε)
    (hyp : H31toH37 X Y f g h k c α β μ ν ε)
    (beta_mono mu_mono : MonotonicityBehavior)
    (hbeta_mono_prop : beta_mono.toProp (β := β))
    (hmu_mono_prop : mu_mono.toProp (β := μ)) :
    ∃ (xbar : X) (ybar : Y) (β_inf μ_inf : ℝ),
    (Tendsto β atTop (𝓝 β_inf) ∧ Tendsto μ atTop (𝓝 μ_inf)) ∧
    (Tendsto alg.x atTop (𝓝 xbar) ∧ Tendsto alg.y atTop (𝓝 ybar)) ∧
    (IsINE f g h k c (limsup α atTop) β_inf μ_inf (limsup ν atTop) xbar ybar)
```

## Statement explanation
Let $X$ and $Y$ be complete metric spaces. The theorem concerns the following data: functions $f:X\to\mathbb R$, $g:Y\to\mathbb R$, $h:X\times X\to\mathbb R$, $k:Y\times Y\to\mathbb R$, $c:X\times Y\to\mathbb R$, and sequences $\alpha,\beta,\mu,\nu,\varepsilon:\mathbb N\to\mathbb R$. An object `alg : ACA2 X Y f g h k c α β μ ν ε` supplies sequences $x_n\in X$, $y_n\in Y$, a strictly positive error sequence $\varepsilon_n>0$, and the two approximate minimization inequalities

$$
f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n)
\le
f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n)+\varepsilon_n
$$

for every $n$ and every $\xi\in X$, and

$$
g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})
\le
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta)+\varepsilon_n
$$

for every $n$ and every $\eta\in Y$.

The hypothesis `hyp : H31toH37 ...` is a bundled list of assumptions. The proof unpacks it into the following concrete requirements: $f$ and $g$ are lower semicontinuous; $c$ is lower semicontinuous on the product $X\times Y$; $f$ and $g$ are bounded below by constants $M_f,M_g$; $h,k,c$ are nonnegative; $h$ and $k$ vanish on the diagonal; $h$ and $k$ are jointly continuous on their product spaces, while $c$ is separately continuous; the metric distances are controlled by the cost functions, in the sense $d_X(x,x')\le h(x,x')$ and $d_Y(y,y')\le k(y,y')$; $\beta_n>0$ and $\mu_n>0$ for all $n$; $\beta_n\to\beta_\infty$ and $\mu_n\to\mu_\infty$ for some positive real limits; $\alpha_n,\nu_n\ge0$; $\alpha$ and $\nu$ are bounded above; $\alpha$ and $\nu$ have positive eventual lower bounds; and $\sum_n\varepsilon_n$ is summable.

The parameters `beta_mono` and `mu_mono` are monotonicity behaviors for $\beta$ and $\mu$, and `hbeta_mono_prop` and `hmu_mono_prop` assert that $\beta$ and $\mu$ indeed satisfy those monotonicity properties, either nonincreasing or nondecreasing.

The conclusion is that there exist $\bar x\in X$, $\bar y\in Y$, and real numbers $\beta_\infty,\mu_\infty$ such that

$$
\beta_n\to\beta_\infty,\qquad \mu_n\to\mu_\infty,\qquad x_n\to\bar x,\qquad y_n\to\bar y,
$$

and the pair $(\bar x,\bar y)$ satisfies the `IsINE` condition

$$
\forall \xi\in X,\quad
f(\bar x)+\beta_\infty c(\bar x,\bar y)+(\limsup_{n\to\infty}\alpha_n)h(\bar x,\bar x)
\le
f(\xi)+\beta_\infty c(\xi,\bar y)+(\limsup_{n\to\infty}\alpha_n)h(\bar x,\xi),
$$

and

$$
\forall \eta\in Y,\quad
g(\bar y)+\mu_\infty c(\bar x,\bar y)+(\limsup_{n\to\infty}\nu_n)k(\bar y,\bar y)
\le
g(\eta)+\mu_\infty c(\bar x,\eta)+(\limsup_{n\to\infty}\nu_n)k(\bar y,\eta).
$$

Since $h(\bar x,\bar x)=0$ and $k(\bar y,\bar y)=0$, the diagonal terms vanish, but the definition of `IsINE` includes them. Thus the theorem says that the ACA2 iterates converge to a point satisfying the limiting INE variational inequalities with coefficients $\limsup\alpha$, $\beta_\infty$, $\mu_\infty$, and $\limsup\nu$.

## Lean proof
```lean
by
  -- Destructure
  rcases hyp with ⟨hf_lsc, hg_lsc, hf_bdd, hg_bdd, hc_nonneg, hc_lsc, hh_cont, hk_cont,
    hh_nonneg, hk_nonneg, hh_diag, hk_diag, hh_dist, hk_dist, hbeta_pos, hmu_pos,
    hbeta_conv, hmu_conv, halpha_nonneg, hnu_nonneg, halpha_bdd, hnu_bdd,
    halpha_liminf, hnu_liminf, heps_summable, hc_sep⟩
  rcases alg with ⟨x, y, heps_pos, hstep_x, hstep_y⟩
  rcases hbeta_conv with ⟨β_inf, hβ_inf_pos, hβ_tendsto⟩
  rcases hmu_conv with ⟨μ_inf, hμ_inf_pos, hμ_tendsto⟩
  rcases hf_bdd with ⟨Mf, hMf⟩
  rcases hg_bdd with ⟨Mg, hMg⟩
  rcases heps_summable with ⟨S, hε_hasSum⟩
  rcases hc_sep with ⟨hc_sep1, hc_sep2⟩
  rcases halpha_liminf with ⟨a, ha_pos, ha_event⟩
  rcases hnu_liminf with ⟨v, hv_pos, hv_event⟩
  have hε_summable : Summable ε := ⟨S, hε_hasSum⟩
  have hε_tendsto0 : Tendsto ε atTop (𝓝 0) := hε_summable.tendsto_atTop_zero
  -- δ_n setup
  set δ := deltaSeq β μ beta_mono mu_mono with hδ_def
  have hδ_pos : ∀ n, δ n > 0 := by
    intro n; unfold δ deltaSeq
    match beta_mono, mu_mono with
    | .nonincreasing, .nonincreasing => norm_num
    | .nonincreasing, .nondecreasing => exact hmu_pos n
    | .nondecreasing, .nonincreasing => exact hbeta_pos n
    | .nondecreasing, .nondecreasing => exact mul_pos (hbeta_pos n) (hmu_pos n)
  have hδ_nonneg (n) : δ n ≥ 0 := le_of_lt (hδ_pos n)
  have hmud_nonneg (n) : μ n / δ n ≥ 0 :=
    div_nonneg (le_of_lt (hmu_pos n)) (hδ_nonneg n)
  have hbetd_nonneg (n) : β n / δ n ≥ 0 :=
    div_nonneg (le_of_lt (hbeta_pos n)) (hδ_nonneg n)
  have hbetamud_nonneg (n) : (β n * μ n) / δ n ≥ 0 :=
    div_nonneg (mul_nonneg (le_of_lt (hbeta_pos n)) (le_of_lt (hmu_pos n))) (hδ_nonneg n)
  have hmud_mono : ∀ n, μ (n+1) / δ (n+1) ≤ μ n / δ n := by
    simpa [hδ_def] using
      thm3_mu_div_delta_nonincreasing β μ beta_mono mu_mono hbeta_pos hmu_pos
        hbeta_mono_prop hmu_mono_prop
  have hbetd_mono : ∀ n, β (n+1) / δ (n+1) ≤ β n / δ n := by
    simpa [hδ_def] using
      thm3_beta_div_delta_nonincreasing β μ beta_mono mu_mono hbeta_pos hmu_pos
        hbeta_mono_prop hmu_mono_prop
  have hbetamud_mono : ∀ n, (β (n+1) * μ (n+1)) / δ (n+1) ≤ (β n * μ n) / δ n := by
    simpa [hδ_def] using
      thm3_betamu_div_delta_nonincreasing β μ beta_mono mu_mono hbeta_pos hmu_pos
        hbeta_mono_prop hmu_mono_prop
  let E : ℕ → ℝ := fun n =>
    (μ n / δ n) * (f (x n) - Mf) +
    (β n / δ n) * (g (y n) - Mg) +
    ((β n * μ n) / δ n) * c (x n) (y n)
  let WH : ℕ → ℝ := fun n => (μ n / δ n) * α n * h (x n) (x (n+1))
  let WK : ℕ → ℝ := fun n => (β n / δ n) * ν n * k (y n) (y (n+1))
  let W : ℕ → ℝ := fun n => WH n + WK n
  let R : ℕ → ℝ := fun n => (μ n / δ n + β n / δ n) * ε n
  have hE_nonneg : ∀ n, 0 ≤ E n := by
    intro n
    have hf_nonneg : 0 ≤ f (x n) - Mf := sub_nonneg.mpr (hMf (x n))
    have hg_nonneg : 0 ≤ g (y n) - Mg := sub_nonneg.mpr (hMg (y n))
    have hc_nonneg_n : 0 ≤ c (x n) (y n) := hc_nonneg (x n) (y n)
    dsimp [E]
    nlinarith [
      mul_nonneg (hmud_nonneg n) hf_nonneg,
      mul_nonneg (hbetd_nonneg n) hg_nonneg,
      mul_nonneg (hbetamud_nonneg n) hc_nonneg_n]
  have hWH_nonneg : ∀ n, 0 ≤ WH n := by
    intro n
    dsimp [WH]
    nlinarith [
      mul_nonneg (mul_nonneg (hmud_nonneg n) (halpha_nonneg n)) (hh_nonneg (x n) (x (n+1)))]
  have hWK_nonneg : ∀ n, 0 ≤ WK n := by
    intro n
    dsimp [WK]
    nlinarith [
      mul_nonneg (mul_nonneg (hbetd_nonneg n) (hnu_nonneg n)) (hk_nonneg (y n) (y (n+1)))]
  have hW_nonneg : ∀ n, 0 ≤ W n := by
    intro n
    dsimp [W]
    exact add_nonneg (hWH_nonneg n) (hWK_nonneg n)
  have hR_nonneg : ∀ n, 0 ≤ R n := by
    intro n
    dsimp [R]
    exact mul_nonneg (add_nonneg (hmud_nonneg n) (hbetd_nonneg n)) (le_of_lt (heps_pos n))
  let RawNext : ℕ → ℝ := fun n =>
    (μ n / δ n) * (f (x (n+1)) - Mf) +
    (β n / δ n) * (g (y (n+1)) - Mg) +
    ((β n * μ n) / δ n) * c (x (n+1)) (y (n+1))
  have hraw_scaled : ∀ n, RawNext n + W n ≤ E n + R n := by
    intro n
    have hraw := thm3_raw_scaled_update (X := X) (Y := Y) (f := f) (g := g)
      (h := h) (k := k) (c := c) (x := x) (y := y) (α := α) (β := β)
      (μ := μ) (ν := ν) (ε := ε) (δ := δ) (Mf := Mf) (Mg := Mg)
      hδ_pos hh_diag hk_diag hbeta_pos hmu_pos hstep_x hstep_y n
    dsimp [RawNext, W, WH, WK, E, R]
    nlinarith
  have hdescent : ∀ n, E (n+1) + W n ≤ E n + R n :=
    thm3_descent_from_raw (X := X) (Y := Y) (f := f) (g := g) (c := c)
      (x := x) (y := y) (β := β) (μ := μ) (δ := δ) (Mf := Mf) (Mg := Mg)
      hMf hMg hc_nonneg hmud_mono hbetd_mono hbetamud_mono RawNext E W R
      (by intro n; rfl) (by intro n; rfl) hraw_scaled
  have hmud_le_zero : ∀ n, μ n / δ n ≤ μ 0 / δ 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact le_trans (hmud_mono n) ih
  have hbetd_le_zero : ∀ n, β n / δ n ≤ β 0 / δ 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact le_trans (hbetd_mono n) ih
  have hR_le_const_mul : ∀ n,
      R n ≤ (μ 0 / δ 0 + β 0 / δ 0) * ε n := by
    intro n
    dsimp [R]
    exact mul_le_mul_of_nonneg_right
      (add_le_add (hmud_le_zero n) (hbetd_le_zero n))
      (le_of_lt (heps_pos n))
  have hR_summable : Summable R := by
    refine Summable.of_nonneg_of_le hR_nonneg hR_le_const_mul ?_
    exact hε_summable.mul_left (μ 0 / δ 0 + β 0 / δ 0)
  have hW_summable : Summable W :=
    thm3_telescope_summable E W R hE_nonneg hW_nonneg hR_nonneg hR_summable hdescent
  have hWH_le_W : ∀ n, WH n ≤ W n := by
    intro n
    dsimp [W]
    nlinarith [hWK_nonneg n]
  have hWK_le_W : ∀ n, WK n ≤ W n := by
    intro n
    dsimp [W]
    nlinarith [hWH_nonneg n]
  have hWH_summable : Summable WH :=
    Summable.of_nonneg_of_le hWH_nonneg hWH_le_W hW_summable
  have hWK_summable : Summable WK :=
    Summable.of_nonneg_of_le hWK_nonneg hWK_le_W hW_summable
  have hμ_lower_ev : ∀ᶠ n in atTop, μ_inf / 2 ≤ μ n :=
    thm3_eventually_half_le_of_tendsto_pos hμ_inf_pos hμ_tendsto
  have hβ_lower_ev : ∀ᶠ n in atTop, β_inf / 2 ≤ β n :=
    thm3_eventually_half_le_of_tendsto_pos hβ_inf_pos hβ_tendsto
  have hμ_upper_ev : ∀ᶠ n in atTop, μ n ≤ μ_inf + 1 :=
    thm3_eventually_le_add_one_of_tendsto hμ_tendsto
  have hβ_upper_ev : ∀ᶠ n in atTop, β n ≤ β_inf + 1 :=
    thm3_eventually_le_add_one_of_tendsto hβ_tendsto
  have hcoeffH_lower :
      ∃ CH > 0, ∀ᶠ n in atTop, CH ≤ (μ n / δ n) * α n := by
    cases beta_mono <;> cases mu_mono
    · refine ⟨(μ_inf / 2) * a, by nlinarith [hμ_inf_pos, ha_pos], ?_⟩
      filter_upwards [hμ_lower_ev, ha_event] with n hμlow halow
      have hmul : (μ_inf / 2) * a ≤ μ n * α n :=
        mul_le_mul hμlow halow (le_of_lt ha_pos) (le_of_lt (hmu_pos n))
      simpa [hδ_def, deltaSeq] using hmul
    · refine ⟨a, ha_pos, ?_⟩
      filter_upwards [ha_event] with n halow
      have hμne : μ n ≠ 0 := (hmu_pos n).ne'
      simpa [hδ_def, deltaSeq, hμne] using halow
    · refine ⟨((μ_inf / 2) / (β_inf + 1)) * a, by
          have hden : 0 < β_inf + 1 := by nlinarith [hβ_inf_pos]
          positivity, ?_⟩
      filter_upwards [hμ_lower_ev, hβ_upper_ev, ha_event] with n hμlow hβup halow
      have hratio : (μ_inf / 2) / (β_inf + 1) ≤ μ n / β n :=
        div_le_div₀ (le_of_lt (hmu_pos n)) hμlow (hbeta_pos n) hβup
      have hmul : ((μ_inf / 2) / (β_inf + 1)) * a ≤ (μ n / β n) * α n :=
        mul_le_mul hratio halow (le_of_lt ha_pos)
          (div_nonneg (le_of_lt (hmu_pos n)) (le_of_lt (hbeta_pos n)))
      simpa [hδ_def, deltaSeq] using hmul
    · refine ⟨(1 / (β_inf + 1)) * a, by
          have hden : 0 < β_inf + 1 := by nlinarith [hβ_inf_pos]
          positivity, ?_⟩
      filter_upwards [hβ_upper_ev, ha_event] with n hβup halow
      have hratio : 1 / (β_inf + 1) ≤ μ n / (β n * μ n) := by
        have hβone : 1 / (β_inf + 1) ≤ 1 / β n :=
          one_div_le_one_div_of_le (hbeta_pos n) hβup
        have hμne : μ n ≠ 0 := (hmu_pos n).ne'
        have hβne : β n ≠ 0 := (hbeta_pos n).ne'
        calc
          1 / (β_inf + 1) ≤ 1 / β n := hβone
          _ = μ n / (β n * μ n) := by
            field_simp [hβne, hμne]
      have hmul : (1 / (β_inf + 1)) * a ≤ (μ n / (β n * μ n)) * α n :=
        mul_le_mul hratio halow (le_of_lt ha_pos)
          (div_nonneg (le_of_lt (hmu_pos n))
            (mul_nonneg (le_of_lt (hbeta_pos n)) (le_of_lt (hmu_pos n))))
      simpa [hδ_def, deltaSeq] using hmul
  have hcoeffK_lower :
      ∃ CK > 0, ∀ᶠ n in atTop, CK ≤ (β n / δ n) * ν n := by
    cases beta_mono <;> cases mu_mono
    · refine ⟨(β_inf / 2) * v, by nlinarith [hβ_inf_pos, hv_pos], ?_⟩
      filter_upwards [hβ_lower_ev, hv_event] with n hβlow hvlow
      have hmul : (β_inf / 2) * v ≤ β n * ν n :=
        mul_le_mul hβlow hvlow (le_of_lt hv_pos) (le_of_lt (hbeta_pos n))
      simpa [hδ_def, deltaSeq] using hmul
    · refine ⟨((β_inf / 2) / (μ_inf + 1)) * v, by
          have hden : 0 < μ_inf + 1 := by nlinarith [hμ_inf_pos]
          positivity, ?_⟩
      filter_upwards [hβ_lower_ev, hμ_upper_ev, hv_event] with n hβlow hμup hvlow
      have hratio : (β_inf / 2) / (μ_inf + 1) ≤ β n / μ n :=
        div_le_div₀ (le_of_lt (hbeta_pos n)) hβlow (hmu_pos n) hμup
      have hmul : ((β_inf / 2) / (μ_inf + 1)) * v ≤ (β n / μ n) * ν n :=
        mul_le_mul hratio hvlow (le_of_lt hv_pos)
          (div_nonneg (le_of_lt (hbeta_pos n)) (le_of_lt (hmu_pos n)))
      simpa [hδ_def, deltaSeq] using hmul
    · refine ⟨v, hv_pos, ?_⟩
      filter_upwards [hv_event] with n hvlow
      have hβne : β n ≠ 0 := (hbeta_pos n).ne'
      simpa [hδ_def, deltaSeq, hβne] using hvlow
    · refine ⟨(1 / (μ_inf + 1)) * v, by
          have hden : 0 < μ_inf + 1 := by nlinarith [hμ_inf_pos]
          positivity, ?_⟩
      filter_upwards [hμ_upper_ev, hv_event] with n hμup hvlow
      have hratio : 1 / (μ_inf + 1) ≤ β n / (β n * μ n) := by
        have hμone : 1 / (μ_inf + 1) ≤ 1 / μ n :=
          one_div_le_one_div_of_le (hmu_pos n) hμup
        have hμne : μ n ≠ 0 := (hmu_pos n).ne'
        have hβne : β n ≠ 0 := (hbeta_pos n).ne'
        calc
          1 / (μ_inf + 1) ≤ 1 / μ n := hμone
          _ = β n / (β n * μ n) := by
            field_simp [hβne, hμne]
      have hmul : (1 / (μ_inf + 1)) * v ≤ (β n / (β n * μ n)) * ν n :=
        mul_le_mul hratio hvlow (le_of_lt hv_pos)
          (div_nonneg (le_of_lt (hbeta_pos n))
            (mul_nonneg (le_of_lt (hbeta_pos n)) (le_of_lt (hmu_pos n))))
      simpa [hδ_def, deltaSeq] using hmul
  rcases hcoeffH_lower with ⟨CH, hCH_pos, hCH_event⟩
  rcases hcoeffK_lower with ⟨CK, hCK_pos, hCK_event⟩
  have hh_summable : Summable (fun n : ℕ => h (x n) (x (n+1))) := by
    refine thm3_summable_of_eventually_le_const_mul
      (u := fun n : ℕ => h (x n) (x (n+1))) (v := WH)
      (C := 1 / CH)
      (fun n => hh_nonneg (x n) (x (n+1))) hWH_summable
      (by positivity) ?_
    filter_upwards [hCH_event] with n hCH
    have hh_nonneg_n : 0 ≤ h (x n) (x (n+1)) := hh_nonneg (x n) (x (n+1))
    have hmul :
        CH * h (x n) (x (n+1)) ≤
        ((μ n / δ n) * α n) * h (x n) (x (n+1)) :=
      mul_le_mul_of_nonneg_right hCH hh_nonneg_n
    calc
      h (x n) (x (n+1)) = (1 / CH) * (CH * h (x n) (x (n+1))) := by
        field_simp [hCH_pos.ne']
      _ ≤ (1 / CH) * (((μ n / δ n) * α n) * h (x n) (x (n+1))) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (1 / CH) * WH n := by
        dsimp [WH]
  have hk_summable : Summable (fun n : ℕ => k (y n) (y (n+1))) := by
    refine thm3_summable_of_eventually_le_const_mul
      (u := fun n : ℕ => k (y n) (y (n+1))) (v := WK)
      (C := 1 / CK)
      (fun n => hk_nonneg (y n) (y (n+1))) hWK_summable
      (by positivity) ?_
    filter_upwards [hCK_event] with n hCK
    have hk_nonneg_n : 0 ≤ k (y n) (y (n+1)) := hk_nonneg (y n) (y (n+1))
    have hmul :
        CK * k (y n) (y (n+1)) ≤
        ((β n / δ n) * ν n) * k (y n) (y (n+1)) :=
      mul_le_mul_of_nonneg_right hCK hk_nonneg_n
    calc
      k (y n) (y (n+1)) = (1 / CK) * (CK * k (y n) (y (n+1))) := by
        field_simp [hCK_pos.ne']
      _ ≤ (1 / CK) * (((β n / δ n) * ν n) * k (y n) (y (n+1))) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (1 / CK) * WK n := by
        dsimp [WK]
  have hxdist_summable : Summable (fun n : ℕ => dist (x n) (x (n+1))) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => h (x n) (x (n+1)))
      (g := fun n : ℕ => dist (x n) (x (n+1)))
      (fun n => dist_nonneg) ?_ hh_summable
    intro n
    exact hh_dist (x n) (x (n+1))
  have hydist_summable : Summable (fun n : ℕ => dist (y n) (y (n+1))) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => k (y n) (y (n+1)))
      (g := fun n : ℕ => dist (y n) (y (n+1)))
      (fun n => dist_nonneg) ?_ hk_summable
    intro n
    exact hk_dist (y n) (y (n+1))
  have hx_cauchy : CauchySeq x := by
    simpa [Nat.succ_eq_add_one] using cauchySeq_of_summable_dist hxdist_summable
  have hy_cauchy : CauchySeq y := by
    simpa [Nat.succ_eq_add_one] using cauchySeq_of_summable_dist hydist_summable
  rcases cauchySeq_tendsto_of_complete hx_cauchy with ⟨xbar, hx_tendsto⟩
  rcases cauchySeq_tendsto_of_complete hy_cauchy with ⟨ybar, hy_tendsto⟩
  let alg_full : ACA2 X Y f g h k c α β μ ν ε :=
    ⟨x, y, heps_pos, hstep_x, hstep_y⟩
  have hx_tendsto_full : Tendsto alg_full.x atTop (𝓝 xbar) := by
    simpa [alg_full] using hx_tendsto
  have hy_tendsto_full : Tendsto alg_full.y atTop (𝓝 ybar) := by
    simpa [alg_full] using hy_tendsto
  have hh_sep : IsSeparatelyContinuous h := by
    constructor
    · intro ξ
      simpa using
        hh_cont.comp (Continuous.prodMk_left ξ)
    · intro x0
      simpa using
        hh_cont.comp (Continuous.prodMk_right x0)
  have hk_sep : IsSeparatelyContinuous k := by
    constructor
    · intro η
      simpa using
        hk_cont.comp (Continuous.prodMk_left η)
    · intro y0
      simpa using
        hk_cont.comp (Continuous.prodMk_right y0)
  have hα_limsup_upper : ∀ r > 0, ∀ᶠ n in atTop, α n ≤ limsup α atTop + r := by
    intro r hr
    rcases halpha_bdd with ⟨M, hM⟩
    have hbounded : IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) α :=
      isBoundedUnder_of_eventually_le (a := M) (Eventually.of_forall hM)
    have hev : ∀ᶠ n in atTop, α n < limsup α atTop + r :=
      eventually_lt_of_limsup_lt (f := (atTop : Filter ℕ)) (u := α)
        (by linarith) hbounded
    filter_upwards [hev] with n hn
    exact le_of_lt hn
  have hν_limsup_upper : ∀ r > 0, ∀ᶠ n in atTop, ν n ≤ limsup ν atTop + r := by
    intro r hr
    rcases hnu_bdd with ⟨M, hM⟩
    have hbounded : IsBoundedUnder (· ≤ ·) (atTop : Filter ℕ) ν :=
      isBoundedUnder_of_eventually_le (a := M) (Eventually.of_forall hM)
    have hev : ∀ᶠ n in atTop, ν n < limsup ν atTop + r :=
      eventually_lt_of_limsup_lt (f := (atTop : Filter ℕ)) (u := ν)
        (by linarith) hbounded
    filter_upwards [hev] with n hn
    exact le_of_lt hn
  have hINE : IsINE f g h k c (limsup α atTop) β_inf μ_inf (limsup ν atTop) xbar ybar := by
    exact
      thm3_ACA2_limit_to_INE
        (alg := alg_full) xbar ybar hx_tendsto_full hy_tendsto_full
        hf_lsc hg_lsc hc_lsc hh_sep hk_sep ⟨hc_sep1, hc_sep2⟩
        hh_nonneg hk_nonneg hc_nonneg
        halpha_nonneg (fun n => le_of_lt (hbeta_pos n))
        (fun n => le_of_lt (hmu_pos n)) hnu_nonneg
        β_inf hβ_tendsto μ_inf hμ_tendsto hε_tendsto0
        hh_diag hk_diag
        (limsup α atTop) (limsup ν atTop)
        hα_limsup_upper hν_limsup_upper
        (limsup α atTop) (limsup ν atTop) le_rfl le_rfl
  exact ⟨xbar, ybar, β_inf, μ_inf, ⟨hβ_tendsto, hμ_tendsto⟩, ⟨hx_tendsto, hy_tendsto⟩, hINE⟩
```

## Proof explanation
The proof proceeds by first unpacking the bundled hypotheses and the ACA2 algorithm. The command `rcases hyp with ...` splits `H31toH37` into the lower semicontinuity, boundedness, nonnegativity, diagonal, continuity, distance-domination, positivity, convergence, boundedness, eventual-lower-bound, summability, and separate-continuity assumptions listed above. The command `rcases alg with ⟨x, y, heps_pos, hstep_x, hstep_y⟩` extracts the sequences $x,y$, the positivity $\varepsilon_n>0$, and the two step inequalities. Then the positive limits $\beta_\infty,\mu_\infty$ are extracted from the convergence assumptions, the lower bounds $M_f,M_g$ are extracted from the boundedness assumptions, and a sum $S$ with `HasSum ε S` is extracted from summability of $\varepsilon$.

From `HasSum ε S` the proof forms `hε_summable : Summable ε`, and then uses that a summable real sequence tends to zero: `hε_tendsto0 : Tendsto ε atTop (𝓝 0)`. This is the fact that if $\sum_n\varepsilon_n$ converges, then $\varepsilon_n\to0$. It is used later in the limiting INE theorem.

Next the proof defines

$$
\delta_n=\mathrm{deltaSeq}(\beta,\mu,\texttt{beta\_mono},\texttt{mu\_mono}).
$$

The definition `deltaSeq` is piecewise: if both behaviors are nonincreasing, $\delta_n=1$; if $\beta$ is nonincreasing and $\mu$ is nondecreasing, $\delta_n=\mu_n$; if $\beta$ is nondecreasing and $\mu$ is nonincreasing, $\delta_n=\beta_n$; and if both are nondecreasing, $\delta_n=\beta_n\mu_n$. The proof shows `hδ_pos : ∀ n, δ n > 0` by cases on `beta_mono` and `mu_mono`, using positivity of $\beta_n$ and $\mu_n$. Consequently $\delta_n\ge0$, and therefore the ratios

$$
\frac{\mu_n}{\delta_n},\qquad \frac{\beta_n}{\delta_n},\qquad \frac{\beta_n\mu_n}{\delta_n}
$$

are all nonnegative.

The three lemmas `thm3_mu_div_delta_nonincreasing`, `thm3_beta_div_delta_nonincreasing`, and `thm3_betamu_div_delta_nonincreasing` are then applied. Each states that, under positivity of $\beta,\mu$ and their declared monotonicity behaviors, the corresponding quotient with $\delta$ is nonincreasing. Thus the proof obtains

$$
\frac{\mu_{n+1}}{\delta_{n+1}}\le\frac{\mu_n}{\delta_n},\qquad
\frac{\beta_{n+1}}{\delta_{n+1}}\le\frac{\beta_n}{\delta_n},\qquad
\frac{\beta_{n+1}\mu_{n+1}}{\delta_{n+1}}\le\frac{\beta_n\mu_n}{\delta_n}.
$$

These monotonicities are the key to making the scaled energy decrease.

The proof then defines

$$
E_n=
\frac{\mu_n}{\delta_n}(f(x_n)-M_f)
+\frac{\beta_n}{\delta_n}(g(y_n)-M_g)
+\frac{\beta_n\mu_n}{\delta_n}c(x_n,y_n),
$$

$$
W^H_n=\frac{\mu_n}{\delta_n}\alpha_n h(x_n,x_{n+1}),\qquad
W^K_n=\frac{\beta_n}{\delta_n}\nu_n k(y_n,y_{n+1}),\qquad
W_n=W^H_n+W^K_n,
$$

and

$$
R_n=\left(\frac{\mu_n}{\delta_n}+\frac{\beta_n}{\delta_n}\right)\varepsilon_n.
$$

The proof shows $E_n,W^H_n,W^K_n,W_n,R_n\ge0$ for every $n$. For $E_n$, this uses $f(x_n)-M_f\ge0$, $g(y_n)-M_g\ge0$, $c(x_n,y_n)\ge0$, and nonnegativity of the ratios. For $W^H_n$ and $W^K_n$, it uses $\alpha_n,\nu_n\ge0$ and $h,k\ge0$.

The lemma `thm3_raw_scaled_update` is applied to the step inequalities. Its content, specialized here, is that if $\delta_n>0$, $h(x_n,x_n)=0$, $k(y_n,y_n)=0$, $\beta_n,\mu_n>0$, and the two ACA2 step inequalities hold, then

$$
\begin{aligned}
&\frac{\mu_n}{\delta_n}(f(x_{n+1})-M_f)
+\frac{\beta_n}{\delta_n}(g(y_{n+1})-M_g)
+\frac{\beta_n\mu_n}{\delta_n}c(x_{n+1},y_{n+1})\\
&\quad+\frac{\mu_n}{\delta_n}\alpha_n h(x_n,x_{n+1})
+\frac{\beta_n}{\delta_n}\nu_n k(y_n,y_{n+1})\\
&\le
\frac{\mu_n}{\delta_n}(f(x_n)-M_f)
+\frac{\beta_n}{\delta_n}(g(y_n)-M_g)
+\frac{\beta_n\mu_n}{\delta_n}c(x_n,y_n)
+\left(\frac{\mu_n}{\delta_n}+\frac{\beta_n}{\delta_n}\right)\varepsilon_n.
\end{aligned}
$$

Concretely, this is obtained by taking the $x$-step inequality with $\xi=x_n$ and the $y$-step inequality with $\eta=y_n$, multiplying the first by $\mu_n/\delta_n$ and the second by $\beta_n/\delta_n$, and adding. The diagonal terms $h(x_n,x_n)$ and $k(y_n,y_n)$ vanish, and the cross terms involving $c(x_{n+1},y_n)$ cancel. After unfolding the definitions of `RawNext`, $W$, $E$, and $R$, this gives exactly

$$
\mathrm{RawNext}_n+W_n\le E_n+R_n.
$$

Next, `thm3_descent_from_raw` is applied. That lemma says that if $f\ge M_f$, $g\ge M_g$, $c\ge0$, the three scaled ratios are nonincreasing, the sequences `RawNext` and $E$ have the displayed definitions, and $\mathrm{RawNext}_n+W_n\le E_n+R_n$, then

$$
E_{n+1}+W_n\le E_n+R_n
$$

for every $n$. The reason is that $E_{n+1}$ is obtained from $\mathrm{RawNext}_n$ by replacing the coefficients at $n$ by the smaller coefficients at $n+1$; since $f(x_{n+1})-M_f$, $g(y_{n+1})-M_g$, and $c(x_{n+1},y_{n+1})$ are nonnegative, this replacement only decreases the value. Thus the raw inequality implies the descent inequality.

The proof then shows that $\mu_n/\delta_n\le \mu_0/\delta_0$ and $\beta_n/\delta_n\le \beta_0/\delta_0$ by induction from the nontrivial monotonicities. Hence

$$
R_n\le
\left(\frac{\mu_0}{\delta_0}+\frac{\beta_0}{\delta_0}\right)\varepsilon_n.
$$

Since $\varepsilon$ is summable and $R\ge0$, the domination criterion for nonnegative sequences implies that $R$ is summable. The proof uses the standard fact that a nonnegative sequence bounded above by a summable sequence is summable.

The lemma `thm3_telescope_summable` is then applied to $E,W,R$. It states that if $E,W,R\ge0$, $R$ is summable, and $E_{n+1}+W_n\le E_n+R_n$ for all $n$, then $W$ is summable. The mathematical reason is telescoping:

$$
W_n\le E_n-E_{n+1}+R_n,
$$

so finite sums of $W_n$ are bounded by $E_0-E_{N+1}+\sum_{n\le N}R_n$, and $E_{N+1}\ge0$. Thus $W$ is summable. Since $W=W^H+W^K$ with both summands nonnegative, each of $W^H$ and $W^K$ is summable as well.

The proof next obtains eventual lower and upper bounds for $\mu$ and $\beta$. The lemma `thm3_eventually_half_le_of_tendsto_pos` says that if $L>0$ and $a_n\to L$, then eventually $L/2\le a_n$. Applied to $\mu$ and $\beta$, it gives eventually $\mu_\infty/2\le\mu_n$ and $\beta_\infty/2\le\beta_n$. The lemma `thm3_eventually_le_add_one_of_tendsto` says that if $a_n\to L$, then eventually $a_n\le L+1$. Applied to $\mu$ and $\beta$, this gives eventually $\mu_n\le\mu_\infty+1$ and $\beta_n\le\beta_\infty+1$.

Using these eventual bounds, the proof establishes positive eventual lower bounds for the coefficients

$$
C^H_n=\frac{\mu_n}{\delta_n}\alpha_n,\qquad
C^K_n=\frac{\beta_n}{\delta_n}\nu_n.
$$

It does this by cases on the four possible pairs of monotonicity behaviors, using the explicit definition of $\delta_n$. For example, when both are nonincreasing, $\delta_n=1$, so $C^H_n=\mu_n\alpha_n$, and the positive eventual lower bounds on $\mu_n$ and $\alpha_n$ give a positive constant $C_H$. The other cases similarly reduce $C^H_n$ to $\alpha_n$, to $(\mu_n/\beta_n)\alpha_n$, or to $(1/\beta_n)\alpha_n$, and the eventual upper bounds on $\beta$ convert the denominator into a positive constant. The same case analysis gives a positive eventual lower bound $C_K$ for $C^K_n$.

These lower bounds are used to prove summability of the actual cost increments. Since

$$
W^H_n=C^H_n h(x_n,x_{n+1}),
$$

and eventually $C_H\le C^H_n$ with $h(x_n,x_{n+1})\ge0$, we have eventually

$$
h(x_n,x_{n+1})\le \frac1{C_H}W^H_n.
$$

The lemma `thm3_summable_of_eventually_le_const_mul` states exactly that if $u_n\ge0$, $v$ is summable, $C\ge0$, and eventually $u_n\le C v_n$, then $u$ is summable. Applying it with $u_n=h(x_n,x_{n+1})$ and $v_n=W^H_n$ gives

$$
\sum_n h(x_n,x_{n+1})<\infty.
$$

The same argument with $C_K$ and $W^K_n$ gives

$$
\sum_n k(y_n,y_{n+1})<\infty.
$$

Because the distances are dominated by the costs, $d_X(x_n,x_{n+1})\le h(x_n,x_{n+1})$ and $d_Y(y_n,y_{n+1})\le k(y_n,y_{n+1})$, and the distances are nonnegative, the summability criterion again gives

$$
\sum_n d_X(x_n,x_{n+1})<\infty,\qquad
\sum_n d_Y(y_n,y_{n+1})<\infty.
$$

The standard lemma `cauchySeq_of_summable_dist` then implies that $x$ and $y$ are Cauchy sequences. Since $X$ and $Y$ are complete, `cauchySeq_tendsto_of_complete` gives limits $\bar x\in X$ and $\bar y\in Y$ with

$$
x_n\to\bar x,\qquad y_n\to\bar y.
$$

At this point the proof reconstructs an ACA2 object `alg_full` with the same $x,y,\varepsilon$, and step inequalities, so that it can be passed to the limiting theorem. It also derives separate continuity of $h$ and $k$. The hypothesis gives joint continuity of $(u,v)\mapsto h(u,v)$ and $(u,v)\mapsto k(u,v)$. For fixed $\xi$, the map $x\mapsto(x,\xi)$ is continuous, so composing with joint continuity gives continuity of $x\mapsto h(x,\xi)$. For fixed $x_0$, the map $y\mapsto(x_0,y)$ is continuous, giving continuity of $y\mapsto h(x_0,y)$. Hence `IsSeparatelyContinuous h`. The same argument gives `IsSeparatelyContinuous k`. The hypothesis already provides `IsSeparatelyContinuous c`, which is unpacked and repacked.

The proof then shows that for every $r>0$, eventually

$$
\alpha_n\le \limsup_{n\to\infty}\alpha_n+r,
\qquad
\nu_n\le \limsup_{n\to\infty}\nu_n+r.
$$

For $\alpha$, boundedness above supplies an eventual upper bound, and `eventually_lt_of_limsup_lt` gives eventually $\alpha_n<\limsup\alpha+r$; hence $\alpha_n\le\limsup\alpha+r$. The same reasoning applies to $\nu$.

Finally, the theorem `thm3_ACA2_limit_to_INE` is applied. That theorem says that if an ACA2 algorithm has $x_n\to\bar x$, $y_n\to\bar y$, $f,g,c$ are lower semicontinuous in the required senses, $h,k,c$ are separately continuous, $h,k,c\ge0$, the coefficient sequences are nonnegative, $\beta_n\to\beta_\infty$, $\mu_n\to\mu_\infty$, $\varepsilon_n\to0$, $h$ and $k$ vanish on the diagonal, and $\alpha,\nu$ have the eventual upper bounds against $\limsup\alpha,\limsup\nu$, then the limiting point satisfies

$$
\mathrm{IsINE}(f,g,h,k,c,\limsup\alpha,\beta_\infty,\mu_\infty,\limsup\nu,\bar x,\bar y).
$$

All hypotheses of that theorem are supplied by the previously unpacked assumptions and by the convergence, summability, separate-continuity, and limsup facts just proved. Therefore the proof obtains `hINE`. Finally, `exact ⟨xbar, ybar, β_inf, μ_inf, ⟨hβ_tendsto, hμ_tendsto⟩, ⟨hx_tendsto, hy_tendsto⟩, hINE⟩` packages the four witnesses, the convergence of $\beta,\mu$, the convergence of the iterates, and the INE conclusion into the existential statement of the theorem.

