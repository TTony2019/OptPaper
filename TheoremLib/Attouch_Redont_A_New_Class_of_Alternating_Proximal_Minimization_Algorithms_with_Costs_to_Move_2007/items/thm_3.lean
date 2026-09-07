import Mathlib

set_option maxHeartbeats 800000

open Set Filter
open scoped Topology BigOperators

/-! # Theorem 3.1: Convergence of (ACA²) -/

def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

structure ACA2 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) (ε : ℕ → ℝ) where
  x : ℕ → X
  y : ℕ → Y
  eps_pos (n : ℕ) : ε n > 0
  step_x (n : ℕ) (ξ : X) :
    f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
    f ξ + α n * h (x n) ξ + β n * c ξ (y n) + ε n
  step_y (n : ℕ) (η : Y) :
    g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
    g η + μ n * c (x (n+1)) η + ν n * k (y n) η + ε n

inductive MonotonicityBehavior | nonincreasing | nondecreasing deriving DecidableEq

def MonotonicityBehavior.toProp {β : ℕ → ℝ} (b : MonotonicityBehavior) : Prop :=
  match b with
  | .nonincreasing => ∀ n, β (n+1) ≤ β n
  | .nondecreasing => ∀ n, β n ≤ β (n+1)

noncomputable def deltaSeq (β μ : ℕ → ℝ) (bβ bμ : MonotonicityBehavior) : ℕ → ℝ :=
  match bβ, bμ with
  | .nonincreasing, .nonincreasing => fun _ => 1
  | .nonincreasing, .nondecreasing => fun n => μ n
  | .nondecreasing, .nonincreasing => fun n => β n
  | .nondecreasing, .nondecreasing => fun n => β n * μ n

def IsSeparatelyContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (F : X → Y → ℝ) : Prop :=
  (∀ (y : Y), Continuous (fun (x : X) => F x y)) ∧ (∀ (x : X), Continuous (fun (y : Y) => F x y))

structure H31toH37 (X Y : Type*) [MetricSpace X] [MetricSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν ε : ℕ → ℝ) : Prop where
  f_lsc : LowerSemicontinuous f
  g_lsc : LowerSemicontinuous g
  f_bdd_below : ∃ Mf : ℝ, ∀ x : X, f x ≥ Mf
  g_bdd_below : ∃ Mg : ℝ, ∀ y : Y, g y ≥ Mg
  c_nonneg : ∀ x : X, ∀ y : Y, c x y ≥ 0
  c_lsc : LowerSemicontinuous (fun (p : X × Y) => c p.1 p.2)
  h_cont : Continuous (fun (p : X × X) => h p.1 p.2)
  k_cont : Continuous (fun (p : Y × Y) => k p.1 p.2)
  h_nonneg : ∀ x ξ : X, h x ξ ≥ 0
  k_nonneg : ∀ y η : Y, k y η ≥ 0
  h_diag_zero : ∀ x : X, h x x = 0
  k_diag_zero : ∀ y : Y, k y y = 0
  h_dist : ∀ x ξ : X, h x ξ ≥ dist x ξ
  k_dist : ∀ y η : Y, k y η ≥ dist y η
  beta_pos : ∀ n : ℕ, β n > 0
  mu_pos : ∀ n : ℕ, μ n > 0
  beta_conv : ∃ β_inf > 0, Tendsto β atTop (𝓝 β_inf)
  mu_conv : ∃ μ_inf > 0, Tendsto μ atTop (𝓝 μ_inf)
  alpha_nonneg : ∀ n : ℕ, α n ≥ 0
  nu_nonneg : ∀ n : ℕ, ν n ≥ 0
  alpha_bdd : ∃ M, ∀ n : ℕ, α n ≤ M
  nu_bdd : ∃ M, ∀ n : ℕ, ν n ≤ M
  alpha_liminf_pos : ∃ a > 0, ∀ᶠ n in atTop, α n ≥ a
  nu_liminf_pos : ∃ v > 0, ∀ᶠ n in atTop, ν n ≥ v
  eps_summable : ∃ S, HasSum ε S
  c_sep_cont : IsSeparatelyContinuous c

private lemma thm3_monotone_nat_of_le_succ {a : ℕ → ℝ} (h : ∀ n, a n ≤ a (n+1)) : Monotone a := by
  exact monotone_nat_of_le_succ h

private lemma antitone_seq_ge_limit {a : ℕ → ℝ} (ha : Antitone a) (hL : Tendsto a atTop (𝓝 L))
    (hbdd : BddBelow (Set.range a)) : ∀ n, a n ≥ L := by
  have hiInf_eq : (⨅ n, a n) = L :=
    tendsto_nhds_unique (tendsto_atTop_ciInf ha hbdd) hL
  intro n; rw [← hiInf_eq]; exact ciInf_le hbdd n

private lemma monotone_seq_le_limit {a : ℕ → ℝ} (ha : Monotone a) (hL : Tendsto a atTop (𝓝 L))
    (hbdd : BddAbove (Set.range a)) : ∀ n, a n ≤ L := by
  have hiSup_eq : (⨆ n, a n) = L :=
    tendsto_nhds_unique (tendsto_atTop_ciSup ha hbdd) hL
  intro n; rw [← hiSup_eq]; exact le_ciSup hbdd n

private lemma thm3_mu_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, μ (n+1) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         μ n / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
      simp [hμ_prop n]
  | .nonincreasing, .nondecreasing =>
      field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
      exact le_rfl
  | .nondecreasing, .nonincreasing =>
      have hprod : μ (n+1) * β n ≤ μ n * β (n+1) := by
        calc
          μ (n+1) * β n ≤ μ n * β n :=
            mul_le_mul_of_nonneg_right (hμ_prop n) (le_of_lt hβpos_n)
          _ ≤ μ n * β (n+1) :=
            mul_le_mul_of_nonneg_left (hβ_prop n) (le_of_lt hμpos_n)
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  | .nondecreasing, .nondecreasing =>
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
      exact hβ_prop n

private lemma thm3_beta_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, β (n+1) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         β n / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
      simp [hβ_prop n]
  | .nonincreasing, .nondecreasing =>
      have hprod : β (n+1) * μ n ≤ β n * μ (n+1) := by
        calc
          β (n+1) * μ n ≤ β n * μ n :=
            mul_le_mul_of_nonneg_right (hβ_prop n) (le_of_lt hμpos_n)
          _ ≤ β n * μ (n+1) :=
            mul_le_mul_of_nonneg_left (hμ_prop n) (le_of_lt hβpos_n)
      field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  | .nondecreasing, .nonincreasing =>
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
      exact le_rfl
  | .nondecreasing, .nondecreasing =>
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
      exact hμ_prop n

private lemma thm3_betamu_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, (β (n+1) * μ (n+1)) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         (β n * μ n) / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
      have hprod : β (n+1) * μ (n+1) ≤ β n * μ n := by
        calc
          β (n+1) * μ (n+1) ≤ β n * μ (n+1) :=
            mul_le_mul_of_nonneg_right (hβ_prop n) (le_of_lt hμpos_n1)
          _ ≤ β n * μ n :=
            mul_le_mul_of_nonneg_left (hμ_prop n) (le_of_lt hβpos_n)
      simpa using hprod
  | .nonincreasing, .nondecreasing =>
      field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
      exact hβ_prop n
  | .nondecreasing, .nonincreasing =>
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
      exact hμ_prop n
  | .nondecreasing, .nondecreasing =>
      field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
      exact le_rfl

private lemma thm3_raw_scaled_update {X Y : Type*}
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {x : ℕ → X} {y : ℕ → Y} {α β μ ν ε δ : ℕ → ℝ}
    {Mf Mg : ℝ}
    (hδ_pos : ∀ n, 0 < δ n)
    (hh_diag : ∀ x : X, h x x = 0) (hk_diag : ∀ y : Y, k y y = 0)
    (hβ_pos : ∀ n, 0 < β n) (hμ_pos : ∀ n, 0 < μ n)
    (hstep_x : ∀ n ξ,
      f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
      f ξ + α n * h (x n) ξ + β n * c ξ (y n) + ε n)
    (hstep_y : ∀ n η,
      g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
      g η + μ n * c (x (n+1)) η + ν n * k (y n) η + ε n)
    (n : ℕ) :
    (μ n / δ n) * (f (x (n+1)) - Mf) +
    (β n / δ n) * (g (y (n+1)) - Mg) +
    ((β n * μ n) / δ n) * c (x (n+1)) (y (n+1)) +
    (μ n / δ n) * α n * h (x n) (x (n+1)) +
    (β n / δ n) * ν n * k (y n) (y (n+1)) ≤
    (μ n / δ n) * (f (x n) - Mf) +
    (β n / δ n) * (g (y n) - Mg) +
    ((β n * μ n) / δ n) * c (x n) (y n) +
    (μ n / δ n + β n / δ n) * ε n := by
  have hx := hstep_x n (x n)
  have hy := hstep_y n (y n)
  have hx' :
      f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
      f (x n) + β n * c (x n) (y n) + ε n := by
    simpa [hh_diag (x n), add_assoc] using hx
  have hy' :
      g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
      g (y n) + μ n * c (x (n+1)) (y n) + ε n := by
    simpa [hk_diag (y n), add_assoc] using hy
  have hμ_nonneg : 0 ≤ μ n := le_of_lt (hμ_pos n)
  have hβ_nonneg : 0 ≤ β n := le_of_lt (hβ_pos n)
  have hx_mul := mul_le_mul_of_nonneg_left hx' hμ_nonneg
  have hy_mul := mul_le_mul_of_nonneg_left hy' hβ_nonneg
  have hraw :
      μ n * f (x (n+1)) + β n * g (y (n+1)) +
      β n * μ n * c (x (n+1)) (y (n+1)) +
      μ n * α n * h (x n) (x (n+1)) +
      β n * ν n * k (y n) (y (n+1)) ≤
      μ n * f (x n) + β n * g (y n) +
      β n * μ n * c (x n) (y n) + (μ n + β n) * ε n := by
    nlinarith [hx_mul, hy_mul]
  have hδ_nonneg : 0 ≤ δ n := le_of_lt (hδ_pos n)
  have hdiv := div_le_div_of_nonneg_right hraw hδ_nonneg
  have hδ_ne : δ n ≠ 0 := (hδ_pos n).ne'
  field_simp [hδ_ne] at hdiv ⊢
  nlinarith

private lemma thm3_descent_from_raw {X Y : Type*}
    {f : X → ℝ} {g : Y → ℝ} {c : X → Y → ℝ}
    {x : ℕ → X} {y : ℕ → Y} {β μ δ : ℕ → ℝ} {Mf Mg : ℝ}
    (hMf : ∀ x : X, f x ≥ Mf) (hMg : ∀ y : Y, g y ≥ Mg)
    (hc_nonneg : ∀ x y, c x y ≥ 0)
    (hmud_mono : ∀ n, μ (n+1) / δ (n+1) ≤ μ n / δ n)
    (hbetd_mono : ∀ n, β (n+1) / δ (n+1) ≤ β n / δ n)
    (hbetamud_mono : ∀ n,
      (β (n+1) * μ (n+1)) / δ (n+1) ≤ (β n * μ n) / δ n)
    (RawNext E W R : ℕ → ℝ)
    (hRawNext_def : ∀ n,
      RawNext n =
        (μ n / δ n) * (f (x (n+1)) - Mf) +
        (β n / δ n) * (g (y (n+1)) - Mg) +
        ((β n * μ n) / δ n) * c (x (n+1)) (y (n+1)))
    (hE_def : ∀ n,
      E n =
        (μ n / δ n) * (f (x n) - Mf) +
        (β n / δ n) * (g (y n) - Mg) +
        ((β n * μ n) / δ n) * c (x n) (y n))
    (hraw : ∀ n, RawNext n + W n ≤ E n + R n) :
    ∀ n, E (n+1) + W n ≤ E n + R n := by
  intro n
  have hf_nonneg : 0 ≤ f (x (n+1)) - Mf := sub_nonneg.mpr (hMf (x (n+1)))
  have hg_nonneg : 0 ≤ g (y (n+1)) - Mg := sub_nonneg.mpr (hMg (y (n+1)))
  have hc_nonneg_n : 0 ≤ c (x (n+1)) (y (n+1)) := hc_nonneg (x (n+1)) (y (n+1))
  have h1 :
      (μ (n+1) / δ (n+1)) * (f (x (n+1)) - Mf) ≤
      (μ n / δ n) * (f (x (n+1)) - Mf) :=
    mul_le_mul_of_nonneg_right (hmud_mono n) hf_nonneg
  have h2 :
      (β (n+1) / δ (n+1)) * (g (y (n+1)) - Mg) ≤
      (β n / δ n) * (g (y (n+1)) - Mg) :=
    mul_le_mul_of_nonneg_right (hbetd_mono n) hg_nonneg
  have h3 :
      ((β (n+1) * μ (n+1)) / δ (n+1)) * c (x (n+1)) (y (n+1)) ≤
      ((β n * μ n) / δ n) * c (x (n+1)) (y (n+1)) :=
    mul_le_mul_of_nonneg_right (hbetamud_mono n) hc_nonneg_n
  have hE_le_raw : E (n+1) ≤ RawNext n := by
    rw [hE_def (n+1), hRawNext_def n]
    nlinarith
  have hEW : E (n+1) + W n ≤ RawNext n + W n := by
    nlinarith
  exact le_trans hEW (hraw n)

private lemma thm3_telescope_summable
    (E W R : ℕ → ℝ)
    (hE_nonneg : ∀ n, 0 ≤ E n)
    (hW_nonneg : ∀ n, 0 ≤ W n)
    (hR_nonneg : ∀ n, 0 ≤ R n)
    (hR_summable : Summable R)
    (hdescent : ∀ n, E (n+1) + W n ≤ E n + R n) :
    Summable W := by
  have htel : ∀ N, E N + (Finset.range N).sum W ≤ E 0 + (Finset.range N).sum R := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        nlinarith [ih, hdescent N]
  have hR_partial_mono : Monotone (fun N : ℕ => (Finset.range N).sum R) := by
    refine thm3_monotone_nat_of_le_succ ?_
    intro N
    rw [Finset.sum_range_succ]
    nlinarith [hR_nonneg N]
  have hR_partial_tendsto :
      Tendsto (fun N : ℕ => (Finset.range N).sum R) atTop (𝓝 (tsum R)) :=
    hR_summable.hasSum.tendsto_sum_nat
  have hR_partial_bdd : BddAbove (Set.range fun N : ℕ => (Finset.range N).sum R) :=
    hR_partial_tendsto.bddAbove_range
  have hR_partial_le_tsum : ∀ N, (Finset.range N).sum R ≤ tsum R :=
    monotone_seq_le_limit hR_partial_mono hR_partial_tendsto hR_partial_bdd
  refine summable_of_sum_range_le (c := E 0 + tsum R) hW_nonneg ?_
  intro N
  have htelN := htel N
  have hRle := hR_partial_le_tsum N
  have hEN := hE_nonneg N
  nlinarith

private lemma thm3_eventually_half_le_of_tendsto_pos {a : ℕ → ℝ} {L : ℝ}
    (hL_pos : 0 < L) (ha : Tendsto a atTop (𝓝 L)) :
    ∀ᶠ n in atTop, L / 2 ≤ a n := by
  have hball : Metric.ball L (L / 2) ∈ 𝓝 L :=
    Metric.ball_mem_nhds L (by linarith)
  filter_upwards [ha.eventually hball] with n hn
  rw [Real.dist_eq] at hn
  have h := (abs_lt.mp hn).left
  linarith

private lemma thm3_eventually_le_add_one_of_tendsto {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) :
    ∀ᶠ n in atTop, a n ≤ L + 1 := by
  have hball : Metric.ball L (1 : ℝ) ∈ 𝓝 L :=
    Metric.ball_mem_nhds L (by norm_num)
  filter_upwards [ha.eventually hball] with n hn
  rw [Real.dist_eq] at hn
  have h := (abs_lt.mp hn).right
  linarith

private lemma thm3_summable_of_eventually_le_const_mul
    {u v : ℕ → ℝ} {C : ℝ}
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hv_summable : Summable v)
    (_hC_nonneg : 0 ≤ C)
    (hev : ∀ᶠ n in atTop, u n ≤ C * v n) :
    Summable u := by
  rcases eventually_atTop.mp hev with ⟨N, hN⟩
  have hv_shift : Summable (fun n : ℕ => v (n + N)) :=
    (summable_nat_add_iff N).mpr hv_summable
  have hu_shift : Summable (fun n : ℕ => u (n + N)) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => C * v (n + N))
      (g := fun n : ℕ => u (n + N))
      (fun n => hu_nonneg (n + N)) ?_ ?_
    · intro n
      exact hN (n + N) (by omega)
    · exact hv_shift.mul_left C
  exact (summable_nat_add_iff N).mp hu_shift

private theorem thm3_ACA2_limit_to_INE {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ} {g : Y → ℝ} {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν ε : ℕ → ℝ} (alg : ACA2 X Y f g h k c α β μ ν ε)
    (xbar : X) (ybar : Y)
    (hx : Tendsto alg.x atTop (𝓝 xbar)) (hy : Tendsto alg.y atTop (𝓝 ybar))
    (hf_lsc : LowerSemicontinuous f) (hg_lsc : LowerSemicontinuous g)
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
    (hepsilon0 : Tendsto ε atTop (𝓝 0))
    (h_diag_h : ∀ x : X, h x x = 0) (h_diag_k : ∀ y : Y, k y y = 0)
    (αbar νbar : ℝ)
    (hαbar : ∀ η > 0, ∀ᶠ n in atTop, α n ≤ αbar + η)
    (hνbar : ∀ η > 0, ∀ᶠ n in atTop, ν n ≤ νbar + η)
    (α_val ν_val : ℝ) (hα_ge : α_val ≥ αbar) (hν_ge : ν_val ≥ νbar) :
    IsINE f g h k c α_val β_inf μ_inf ν_val xbar ybar := by
  have hx_shift : Tendsto (fun n : ℕ => alg.x (n+1)) atTop (𝓝 xbar) :=
    hx.comp (tendsto_add_atTop_nat 1)
  have hy_shift : Tendsto (fun n : ℕ => alg.y (n+1)) atTop (𝓝 ybar) :=
    hy.comp (tendsto_add_atTop_nat 1)
  rcases hh_sep with ⟨hh_sep1, _hh_sep2⟩
  rcases hk_sep with ⟨hk_sep1, _hk_sep2⟩
  rcases hc_sep with ⟨hc_sep1, hc_sep2⟩

  have h_αbar_nonneg : αbar ≥ 0 := by
    by_contra! h_neg
    have hη_pos : 0 < -αbar / 2 := by linarith
    have h_event : ∀ᶠ n in atTop, α n ≤ αbar + (-αbar / 2) := hαbar (-αbar / 2) hη_pos
    have h_simp : αbar + (-αbar / 2) = αbar / 2 := by ring
    have h_bound_ev : ∀ᶠ n in atTop, α n ≤ αbar / 2 := by
      simpa [h_simp] using h_event
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_bound_ev
    have h_nonneg_n : α n ≥ 0 := hα_nonneg n
    have h_neg_bound : αbar / 2 < 0 := by linarith
    linarith

  have h_νbar_nonneg : νbar ≥ 0 := by
    by_contra! h_neg
    have hη_pos : 0 < -νbar / 2 := by linarith
    have h_event : ∀ᶠ n in atTop, ν n ≤ νbar + (-νbar / 2) := hνbar (-νbar / 2) hη_pos
    have h_simp : νbar + (-νbar / 2) = νbar / 2 := by ring
    have h_bound_ev : ∀ᶠ n in atTop, ν n ≤ νbar / 2 := by
      simpa [h_simp] using h_event
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_bound_ev
    have h_nonneg_n : ν n ≥ 0 := hν_nonneg n
    have h_neg_bound : νbar / 2 < 0 := by linarith
    linarith

  have h_cbar_nonneg : c xbar ybar ≥ 0 := hc_nonneg _ _

  have hxy_pair_c : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y n)) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_shift hy
  have hxy_pair_c2 : Tendsto (fun n : ℕ => (alg.x (n+1), alg.y (n+1))) atTop (𝓝 (xbar, ybar)) :=
    Filter.Tendsto.prodMk_nhds hx_shift hy_shift

  have h_fx_lower (η : ℝ) (hη : η > 0) : ∀ᶠ n in atTop, f xbar - η < f (alg.x (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 xbar, f z > f xbar - η :=
      (hf_lsc xbar) (f xbar - η) (by linarith)
    filter_upwards [hx_shift.eventually h_nhds] with n hn
    exact hn

  have h_c_lower (η : ℝ) (hη : η > 0) : ∀ᶠ n in atTop, c xbar ybar - η < c (alg.x (n+1)) (alg.y n) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - η :=
      (hc_lsc (xbar, ybar)) (c xbar ybar - η) (by linarith)
    filter_upwards [hxy_pair_c.eventually h_nhds] with n hn
    exact hn

  have h_gy_lower (η : ℝ) (hη : η > 0) : ∀ᶠ n in atTop, g ybar - η < g (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ z in 𝓝 ybar, g z > g ybar - η :=
      (hg_lsc ybar) (g ybar - η) (by linarith)
    filter_upwards [hy_shift.eventually h_nhds] with n hn
    exact hn

  have h_c2_lower (η : ℝ) (hη : η > 0) : ∀ᶠ n in atTop, c xbar ybar - η < c (alg.x (n+1)) (alg.y (n+1)) := by
    have h_nhds : ∀ᶠ (z : X × Y) in 𝓝 (xbar, ybar), c z.1 z.2 > c xbar ybar - η :=
      (hc_lsc (xbar, ybar)) (c xbar ybar - η) (by linarith)
    filter_upwards [hxy_pair_c2.eventually h_nhds] with n hn
    exact hn

  set_option maxHeartbeats 600000 in
  have h_prod_ev_lower {a_n b_n : ℕ → ℝ} {a_lim b_lim : ℝ} {η : ℝ} (hη : η > 0)
      (ha_nn : ∀ n, 0 ≤ a_n n) (hb_nn : ∀ n, 0 ≤ b_n n)
      (ha_tendsto : Tendsto a_n atTop (𝓝 a_lim))
      (hb_lim_nonneg : 0 ≤ b_lim)
      (hb_lower : ∀ δ > 0, ∀ᶠ n in atTop, b_lim - δ < b_n n) :
      ∀ᶠ n in atTop, a_lim * b_lim - η < a_n n * b_n n := by
    have ha_lim_nonneg : 0 ≤ a_lim :=
      ge_of_tendsto ha_tendsto (eventually_atTop.mpr ⟨0, fun n _ => ha_nn n⟩)
    rcases eq_or_lt_of_le ha_lim_nonneg with (rfl | ha_lim_pos)
    · filter_upwards [] with n
      have h_nonneg_prod : 0 ≤ a_n n * b_n n := mul_nonneg (ha_nn n) (hb_nn n)
      linarith
    set denom : ℝ := a_lim + b_lim + 1 with h_denom_def
    have h_denom_pos : 0 < denom := by
      dsimp [denom]; nlinarith
    set δ := min (a_lim / 2) (η / (2 * denom)) with hδ_def
    have hδ_pos : 0 < δ := by
      refine lt_min_iff.mpr ⟨by linarith, div_pos hη (by nlinarith)⟩
    have hδ_lt_a_lim : δ < a_lim := by
      calc
        δ ≤ a_lim / 2 := min_le_left _ _
        _ < a_lim := by nlinarith
    have h_prod_bound : a_lim * b_lim - η < (a_lim - δ) * (b_lim - δ) := by
      have h_aux : δ * (a_lim + b_lim - δ) < η := by
        have hδ_le : δ ≤ η / (2 * denom) := min_le_right _ _
        have h_ineq : a_lim + b_lim - δ < denom := by
          dsimp [denom]; nlinarith
        have h_mid : δ * (a_lim + b_lim - δ) < δ * denom :=
          mul_lt_mul_of_pos_left h_ineq hδ_pos
        have h_bound : δ * denom ≤ η / 2 := by
          calc
            δ * denom ≤ (η / (2 * denom)) * denom :=
              mul_le_mul_of_nonneg_right hδ_le (by linarith)
            _ = η / 2 := by
              field_simp [h_denom_pos.ne.symm]
        have h_eta_half_lt : η / 2 < η := by linarith
        nlinarith
      nlinarith
    have ha_ev : ∀ᶠ n in atTop, a_lim - δ < a_n n := by
      have h_open : IsOpen {x : ℝ | a_lim - δ < x} := isOpen_Ioi
      have h_mem : a_lim ∈ {x : ℝ | a_lim - δ < x} :=
        show a_lim - δ < a_lim by linarith
      have h_nhd : {x : ℝ | a_lim - δ < x} ∈ 𝓝 a_lim := h_open.mem_nhds h_mem
      filter_upwards [ha_tendsto.eventually h_nhd] with n hn
      exact hn
    have hb_ev : ∀ᶠ n in atTop, b_lim - δ < b_n n := hb_lower δ hδ_pos
    filter_upwards [ha_ev, hb_ev] with n ha_low hb_low
    by_cases h_b_low_nonneg : 0 < b_lim - δ
    · calc
        a_lim * b_lim - η < (a_lim - δ) * (b_lim - δ) := h_prod_bound
        _ < a_n n * b_n n := mul_lt_mul ha_low hb_low.le h_b_low_nonneg (ha_nn n)
    · have h_nonpos : (a_lim - δ) * (b_lim - δ) ≤ 0 := by
        have h_nonneg_a : 0 ≤ a_lim - δ := by linarith
        nlinarith
      have h_nonneg_prod : 0 ≤ a_n n * b_n n := mul_nonneg (ha_nn n) (hb_nn n)
      linarith

  have h_αh_upper_bound (ξ : X) (η : ℝ) (hη : η > 0) :
      ∀ᶠ n in atTop, α n * h (alg.x n) ξ < αbar * h xbar ξ + η := by
    have h_hξ_nonneg : h xbar ξ ≥ 0 := hh_nonneg _ _
    have h_hξ_tendsto : Tendsto (fun n : ℕ => h (alg.x n) ξ) atTop (𝓝 (h xbar ξ)) :=
      (hh_sep1 ξ).continuousAt.tendsto.comp hx
    set coeff : ℝ := αbar + h xbar ξ + 1 with h_coeff
    have h_coeff_pos : 0 < coeff := by
      dsimp [coeff]; nlinarith
    set δ := min (η / (2 * coeff)) 1 with hδ_def
    have hδ_pos : 0 < δ := by
      refine lt_min_iff.mpr ⟨div_pos hη (by nlinarith), by norm_num⟩
    have hδ_le : δ ≤ 1 := min_le_right _ _
    have hδ_le_eta_div : δ ≤ η / (2 * coeff) := min_le_left _ _
    have h_bound : (αbar + δ) * (h xbar ξ + δ) < αbar * h xbar ξ + η := by
      calc
        (αbar + δ) * (h xbar ξ + δ) = αbar * h xbar ξ + δ * (αbar + h xbar ξ + δ) := by ring
        _ ≤ αbar * h xbar ξ + δ * (αbar + h xbar ξ + 1) := by
          have : αbar + h xbar ξ + δ ≤ αbar + h xbar ξ + 1 := by linarith
          nlinarith
        _ = αbar * h xbar ξ + δ * coeff := by simp [coeff]
        _ ≤ αbar * h xbar ξ + (η / (2 * coeff)) * coeff := by
          nlinarith
        _ = αbar * h xbar ξ + η / 2 := by
          field_simp [h_coeff_pos.ne.symm]
        _ < αbar * h xbar ξ + η := by linarith
    have h_α_bound : ∀ᶠ n in atTop, α n ≤ αbar + δ := hαbar δ hδ_pos
    have h_h_close : ∀ᶠ n in atTop, h (alg.x n) ξ < h xbar ξ + δ := by
      have h_nhd : Metric.ball (h xbar ξ) δ ∈ 𝓝 (h xbar ξ) :=
        Metric.ball_mem_nhds (h xbar ξ) hδ_pos
      filter_upwards [h_hξ_tendsto.eventually h_nhd] with n hn
      rw [Real.dist_eq] at hn
      have h_lt := (abs_lt.mp hn).right
      linarith
    filter_upwards [h_α_bound, h_h_close] with n hn_α hn_h
    have h_nonneg_h : 0 ≤ h (alg.x n) ξ := hh_nonneg _ _
    calc
      α n * h (alg.x n) ξ ≤ (αbar + δ) * h (alg.x n) ξ :=
        mul_le_mul_of_nonneg_right hn_α h_nonneg_h
      _ ≤ (αbar + δ) * (h xbar ξ + δ) :=
        mul_le_mul_of_nonneg_left hn_h.le (by nlinarith [h_αbar_nonneg])
      _ < αbar * h xbar ξ + η := h_bound

  have h_νk_upper_bound (η0 : Y) (η : ℝ) (hη : η > 0) :
      ∀ᶠ n in atTop, ν n * k (alg.y n) η0 < νbar * k ybar η0 + η := by
    have h_kη_nonneg : k ybar η0 ≥ 0 := hk_nonneg _ _
    have h_kη_tendsto : Tendsto (fun n : ℕ => k (alg.y n) η0) atTop (𝓝 (k ybar η0)) :=
      (hk_sep1 η0).continuousAt.tendsto.comp hy
    set coeff : ℝ := νbar + k ybar η0 + 1 with h_coeff
    have h_coeff_pos : 0 < coeff := by
      dsimp [coeff]; nlinarith
    set δ := min (η / (2 * coeff)) 1 with hδ_def
    have hδ_pos : 0 < δ := by
      refine lt_min_iff.mpr ⟨div_pos hη (by nlinarith), by norm_num⟩
    have hδ_le : δ ≤ 1 := min_le_right _ _
    have hδ_le_eta_div : δ ≤ η / (2 * coeff) := min_le_left _ _
    have h_bound : (νbar + δ) * (k ybar η0 + δ) < νbar * k ybar η0 + η := by
      calc
        (νbar + δ) * (k ybar η0 + δ) = νbar * k ybar η0 + δ * (νbar + k ybar η0 + δ) := by ring
        _ ≤ νbar * k ybar η0 + δ * (νbar + k ybar η0 + 1) := by
          have : νbar + k ybar η0 + δ ≤ νbar + k ybar η0 + 1 := by linarith
          nlinarith
        _ = νbar * k ybar η0 + δ * coeff := by simp [coeff]
        _ ≤ νbar * k ybar η0 + (η / (2 * coeff)) * coeff := by
          nlinarith
        _ = νbar * k ybar η0 + η / 2 := by
          field_simp [h_coeff_pos.ne.symm]
        _ < νbar * k ybar η0 + η := by linarith
    have h_ν_bound : ∀ᶠ n in atTop, ν n ≤ νbar + δ := hνbar δ hδ_pos
    have h_k_close : ∀ᶠ n in atTop, k (alg.y n) η0 < k ybar η0 + δ := by
      have h_nhd : Metric.ball (k ybar η0) δ ∈ 𝓝 (k ybar η0) :=
        Metric.ball_mem_nhds (k ybar η0) hδ_pos
      filter_upwards [h_kη_tendsto.eventually h_nhd] with n hn
      rw [Real.dist_eq] at hn
      have h_lt := (abs_lt.mp hn).right
      linarith
    filter_upwards [h_ν_bound, h_k_close] with n hn_ν hn_k
    have h_nonneg_k : 0 ≤ k (alg.y n) η0 := hk_nonneg _ _
    calc
      ν n * k (alg.y n) η0 ≤ (νbar + δ) * k (alg.y n) η0 :=
        mul_le_mul_of_nonneg_right hn_ν h_nonneg_k
      _ ≤ (νbar + δ) * (k ybar η0 + δ) :=
        mul_le_mul_of_nonneg_left hn_k.le (by nlinarith [h_νbar_nonneg])
      _ < νbar * k ybar η0 + η := h_bound

  have hRHS_x_partial (ξ : X) :
      Tendsto (fun n : ℕ => f ξ + β n * c ξ (alg.y n)) atTop
      (𝓝 (f ξ + β_inf * c ξ ybar)) := by
    have hcξ : Tendsto (fun n : ℕ => c ξ (alg.y n)) atTop (𝓝 (c ξ ybar)) :=
      ((hc_sep2 ξ).continuousAt.tendsto).comp hy
    have hβcξ : Tendsto (fun n : ℕ => β n * c ξ (alg.y n)) atTop (𝓝 (β_inf * c ξ ybar)) :=
      Filter.Tendsto.mul hβ hcξ
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => f ξ) atTop _).add hβcξ)

  have hRHS_y_partial (η0 : Y) :
      Tendsto (fun n : ℕ => g η0 + μ n * c (alg.x (n+1)) η0) atTop
      (𝓝 (g η0 + μ_inf * c xbar η0)) := by
    have hcη : Tendsto (fun n : ℕ => c (alg.x (n+1)) η0) atTop (𝓝 (c xbar η0)) :=
      ((hc_sep1 η0).continuousAt.tendsto).comp hx_shift
    have hμcη : Tendsto (fun n : ℕ => μ n * c (alg.x (n+1)) η0) atTop (𝓝 (μ_inf * c xbar η0)) :=
      Filter.Tendsto.mul hμ hcη
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => g η0) atTop _).add hμcη)

  have h_eps_small (η : ℝ) (hη : η > 0) : ∀ᶠ n in atTop, ε n < η := by
    have hball : Metric.ball (0 : ℝ) η ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hη
    filter_upwards [hepsilon0.eventually hball] with n hn
    rw [Real.dist_eq] at hn
    have h_abs := abs_lt.mp hn
    linarith

  have h_xine : ∀ (ξ : X), f xbar + β_inf * c xbar ybar + α_val * h xbar xbar ≤
      f ξ + β_inf * c ξ ybar + α_val * h xbar ξ := by
    intro ξ
    have h_target : f xbar + β_inf * c xbar ybar + α_val * h xbar xbar =
        f xbar + β_inf * c xbar ybar := by
      simp [h_diag_h xbar]
    rw [h_target]
    refine le_of_forall_pos_lt_add ?_
    intro η hη
    set η0 := η / 6 with hη0
    have hη0pos : η0 > 0 := by linarith
    have h_f_ev : ∀ᶠ n in atTop, f xbar - η0 < f (alg.x (n+1)) :=
      h_fx_lower η0 hη0pos
    have h_βc_ev : ∀ᶠ n in atTop, β_inf * c xbar ybar - η0 < β n * c (alg.x (n+1)) (alg.y n) :=
      h_prod_ev_lower hη0pos hβ_nonneg (fun n => hc_nonneg _ _) hβ h_cbar_nonneg h_c_lower
    have h_αh_nonneg (n : ℕ) : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) :=
      mul_nonneg (hα_nonneg n) (hh_nonneg _ _)
    have hRHS_partial_ev : ∀ᶠ n in atTop,
        f ξ + β n * c ξ (alg.y n) < f ξ + β_inf * c ξ ybar + η0 := by
      have ht := hRHS_x_partial ξ
      have hball : Metric.ball (f ξ + β_inf * c ξ ybar : ℝ) η0 ∈ 𝓝 (f ξ + β_inf * c ξ ybar : ℝ) :=
        Metric.ball_mem_nhds _ hη0pos
      filter_upwards [ht.eventually hball] with n hn
      rw [Real.dist_eq] at hn
      have h_abs := abs_lt.mp hn
      linarith
    have h_αh_upper_ev : ∀ᶠ n in atTop, α n * h (alg.x n) ξ < αbar * h xbar ξ + η0 :=
      h_αh_upper_bound ξ η0 hη0pos
    have h_eps_ev : ∀ᶠ n in atTop, ε n < η0 := h_eps_small η0 hη0pos
    have h_all : ∀ᶠ n in atTop,
        f xbar - η0 < f (alg.x (n+1)) ∧
        β_inf * c xbar ybar - η0 < β n * c (alg.x (n+1)) (alg.y n) ∧
        (f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
         f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) + ε n) ∧
        α n * h (alg.x n) ξ < αbar * h xbar ξ + η0 ∧
        f ξ + β n * c ξ (alg.y n) < f ξ + β_inf * c ξ ybar + η0 ∧
        ε n < η0 := by
      filter_upwards [h_f_ev, h_βc_ev, h_αh_upper_ev, hRHS_partial_ev, h_eps_ev] with
        n hf hβc hαh_upper hRHSpart hεsmall
      exact ⟨hf, hβc, alg.step_x n ξ, hαh_upper, hRHSpart, hεsmall⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hf, hβc, hstep, hαh_upper, hRHSpart, hεsmall⟩
    have hLHS_simple_lower : f xbar + β_inf * c xbar ybar - 2 * η0 <
        f (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) := by
      nlinarith
    have hLHS_le_RHS : f (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
        f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) + ε n := by
      have h_nonneg_term : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) := h_αh_nonneg n
      linarith
    have hRHS_upper : f ξ + α n * h (alg.x n) ξ + β n * c ξ (alg.y n) + ε n <
        f ξ + α_val * h xbar ξ + β_inf * c ξ ybar + 3 * η0 := by
      have h_α_term : α n * h (alg.x n) ξ ≤ α_val * h xbar ξ + η0 := by
        have h_nonneg_h : 0 ≤ h xbar ξ := hh_nonneg _ _
        have : αbar * h xbar ξ ≤ α_val * h xbar ξ :=
          mul_le_mul_of_nonneg_right hα_ge h_nonneg_h
        linarith
      nlinarith
    have h_final : f xbar + β_inf * c xbar ybar <
        f ξ + α_val * h xbar ξ + β_inf * c ξ ybar + η := by
      nlinarith
    linarith

  have h_yine : ∀ (η0 : Y), g ybar + μ_inf * c xbar ybar + ν_val * k ybar ybar ≤
      g η0 + μ_inf * c xbar η0 + ν_val * k ybar η0 := by
    intro η0
    have h_target : g ybar + μ_inf * c xbar ybar + ν_val * k ybar ybar =
        g ybar + μ_inf * c xbar ybar := by
      simp [h_diag_k ybar]
    rw [h_target]
    refine le_of_forall_pos_lt_add ?_
    intro η hη
    set η1 := η / 6 with hη1
    have hη1pos : η1 > 0 := by linarith
    have h_g_ev : ∀ᶠ n in atTop, g ybar - η1 < g (alg.y (n+1)) :=
      h_gy_lower η1 hη1pos
    have h_μc_ev : ∀ᶠ n in atTop, μ_inf * c xbar ybar - η1 < μ n * c (alg.x (n+1)) (alg.y (n+1)) :=
      h_prod_ev_lower hη1pos hμ_nonneg (fun n => hc_nonneg _ _) hμ h_cbar_nonneg h_c2_lower
    have h_νk_nonneg (n : ℕ) : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) :=
      mul_nonneg (hν_nonneg n) (hk_nonneg _ _)
    have hRHS_partial_ev : ∀ᶠ n in atTop,
        g η0 + μ n * c (alg.x (n+1)) η0 < g η0 + μ_inf * c xbar η0 + η1 := by
      have ht := hRHS_y_partial η0
      have hball : Metric.ball (g η0 + μ_inf * c xbar η0 : ℝ) η1 ∈ 𝓝 (g η0 + μ_inf * c xbar η0 : ℝ) :=
        Metric.ball_mem_nhds _ hη1pos
      filter_upwards [ht.eventually hball] with n hn
      rw [Real.dist_eq] at hn
      have h_abs := abs_lt.mp hn
      linarith
    have h_νk_upper_ev : ∀ᶠ n in atTop, ν n * k (alg.y n) η0 < νbar * k ybar η0 + η1 :=
      h_νk_upper_bound η0 η1 hη1pos
    have h_eps_ev : ∀ᶠ n in atTop, ε n < η1 := h_eps_small η1 hη1pos
    have h_all : ∀ᶠ n in atTop,
        g ybar - η1 < g (alg.y (n+1)) ∧
        μ_inf * c xbar ybar - η1 < μ n * c (alg.x (n+1)) (alg.y (n+1)) ∧
        (g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) ≤
         g η0 + μ n * c (alg.x (n+1)) η0 + ν n * k (alg.y n) η0 + ε n) ∧
        ν n * k (alg.y n) η0 < νbar * k ybar η0 + η1 ∧
        g η0 + μ n * c (alg.x (n+1)) η0 < g η0 + μ_inf * c xbar η0 + η1 ∧
        ε n < η1 := by
      filter_upwards [h_g_ev, h_μc_ev, h_νk_upper_ev, hRHS_partial_ev, h_eps_ev] with
        n hg hμc hνk_upper hRHSpart hεsmall
      exact ⟨hg, hμc, alg.step_y n η0, hνk_upper, hRHSpart, hεsmall⟩
    obtain ⟨n, hn⟩ := Filter.Eventually.exists h_all
    rcases hn with ⟨hg, hμc, hstep, hνk_upper, hRHSpart, hεsmall⟩
    have hLHS_simple_lower : g ybar + μ_inf * c xbar ybar - 2 * η1 <
        g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) := by
      nlinarith
    have hLHS_le_RHS : g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) ≤
        g η0 + μ n * c (alg.x (n+1)) η0 + ν n * k (alg.y n) η0 + ε n := by
      have h_nonneg_term : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) := h_νk_nonneg n
      linarith
    have hRHS_upper : g η0 + μ n * c (alg.x (n+1)) η0 + ν n * k (alg.y n) η0 + ε n <
        g η0 + ν_val * k ybar η0 + μ_inf * c xbar η0 + 3 * η1 := by
      have h_ν_term : ν n * k (alg.y n) η0 ≤ ν_val * k ybar η0 + η1 := by
        have h_nonneg_k : 0 ≤ k ybar η0 := hk_nonneg _ _
        have : νbar * k ybar η0 ≤ ν_val * k ybar η0 :=
          mul_le_mul_of_nonneg_right hν_ge h_nonneg_k
        linarith
      nlinarith
    have h_final : g ybar + μ_inf * c xbar ybar <
        g η0 + ν_val * k ybar η0 + μ_inf * c xbar η0 + η := by
      nlinarith
    nlinarith

  refine ⟨?_, ?_⟩
  · intro ξ
    simpa [add_comm, add_left_comm, add_assoc] using h_xine ξ
  · intro η
    simpa [add_comm, add_left_comm, add_assoc] using h_yine η

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
    (IsINE f g h k c (limsup α atTop) β_inf μ_inf (limsup ν atTop) xbar ybar) := by
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
