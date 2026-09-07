import Mathlib

/-!
# Theorem 2.4: Convergence with Equal Nonincreasing Parameters

When β_n = μ_n and both are nonincreasing, the energy sequence is nonincreasing
and the cost-weighted sum converges.

Depends on: algo_1 (CA2), lem_1 (Lemma 2.3).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set
open Filter
open scoped Topology BigOperators

/-- CA2 algorithm (duplicated for self-containment). -/
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

/-- Assumptions H21-H24. -/
structure H21toH24 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) : Prop where
  f_bdd_below : ∃ Mf : ℝ, ∀ x : X, f x ≥ Mf
  g_bdd_below : ∃ Mg : ℝ, ∀ y : Y, g y ≥ Mg
  h_nonneg : ∀ x ξ : X, h x ξ ≥ 0
  k_nonneg : ∀ y η : Y, k y η ≥ 0
  c_nonneg : ∀ x : X, ∀ y : Y, c x y ≥ 0
  h_diag_zero : ∀ x : X, h x x = 0
  k_diag_zero : ∀ y : Y, k y y = 0
  beta_pos : ∀ n : ℕ, β n > 0
  mu_pos : ∀ n : ℕ, μ n > 0
  alpha_nonneg : ∀ n : ℕ, α n ≥ 0
  nu_nonneg : ∀ n : ℕ, ν n ≥ 0

/-- Theorem 2.4(a): When β_n ≡ μ_n is nonincreasing, the quantity
E_n = f(x_n) + g(y_n) + β_n c(x_n, y_n) is nonincreasing and has a limit. -/
theorem theorem_2_4_a {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β β ν)
    (hyp : H21toH24 X Y f g h k c α β β ν)
    (hbeta_nonincreasing : ∀ n : ℕ, β (n+1) ≤ β n) (n m : ℕ) (hmn : n ≤ m) :
    f (alg.x m) + g (alg.y m) + β m * c (alg.x m) (alg.y m) ≤
    f (alg.x n) + g (alg.y n) + β n * c (alg.x n) (alg.y n) := by
  set E := fun (i : ℕ) => f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) with hE
  -- Prove E (i+1) ≤ E i for any i
  have hstep : ∀ i : ℕ, E (i+1) ≤ E i := by
    intro i
    -- From CA2 step_x with ξ = x_i, using h(x_i, x_i) = 0
    have hx := alg.step_x i (alg.x i)
    have hx_simp : f (alg.x (i+1)) + α i * h (alg.x i) (alg.x (i+1)) + β i * c (alg.x (i+1)) (alg.y i) ≤
        f (alg.x i) + β i * c (alg.x i) (alg.y i) := by
      simpa [hyp.h_diag_zero (alg.x i)] using hx
    -- From CA2 step_y with η = y_i, using k(y_i, y_i) = 0
    have hy := alg.step_y i (alg.y i)
    have hy_simp : g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        g (alg.y i) + β i * c (alg.x (i+1)) (alg.y i) := by
      simpa [hyp.k_diag_zero (alg.y i)] using hy
    -- Add the two simplified inequalities; cancel the common term β_i*c(x_{i+1}, y_i)
    have hadd := add_le_add hx_simp hy_simp
    have hmain : f (alg.x (i+1)) + g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) +
        α i * h (alg.x i) (alg.x (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) := by
      linarith
    -- β_i is nonincreasing and c ≥ 0, so β_{i+1}*c ≤ β_i*c
    have hbeta_c : β (i+1) * c (alg.x (i+1)) (alg.y (i+1)) ≤
        β i * c (alg.x (i+1)) (alg.y (i+1)) :=
      mul_le_mul_of_nonneg_right (hbeta_nonincreasing i) (hyp.c_nonneg _ _)
    -- Nonnegativity of α*h and ν*k terms
    have h_ah_nonneg : 0 ≤ α i * h (alg.x i) (alg.x (i+1)) :=
      mul_nonneg (hyp.alpha_nonneg i) (hyp.h_nonneg _ _)
    have h_nk_nonneg : 0 ≤ ν i * k (alg.y i) (alg.y (i+1)) :=
      mul_nonneg (hyp.nu_nonneg i) (hyp.k_nonneg _ _)
    -- Chain: E(i+1) ≤ E(i+1) with β_i*c ≤ ... + αh+νk ≤ E(i)
    unfold E
    nlinarith
  -- Extend to arbitrary m ≥ n by induction
  refine Nat.le_induction (le_refl (E n)) (fun k _ hk => ?_) m hmn
  exact le_trans (hstep k) hk

/-- Theorem 2.4(b): The sum of cost-weighted terms converges:
Σ_{n=0}^∞ [α_n h(x_n, x_{n+1}) + ν_n k(y_n, y_{n+1})] < ∞. -/
theorem theorem_2_4_b {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β β ν)
    (hyp : H21toH24 X Y f g h k c α β β ν)
    (hbeta_nonincreasing : ∀ n : ℕ, β (n+1) ≤ β n) :
    ∃ S : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (α n * h (alg.x n) (alg.x (n+1)) + ν n * k (alg.y n) (alg.y (n+1))))) atTop (𝓝 S) := by
  set E := fun (i : ℕ) => f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) with hE
  set term := fun (n : ℕ) => α n * h (alg.x n) (alg.x (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) with hterm
  set S_seq := fun (N : ℕ) => (∑ n ∈ Finset.range N, term n) with hS_seq
  -- Key inequality (from dividing Lemma 2.3 by β_n ≡ μ_n):
  -- E(i+1) + α_i*h + ν_i*k ≤ E(i)  with β_i on the LHS,
  -- then replace β_i by β_{i+1} using nonincrease. Final form: E(i+1) + term i ≤ E(i)
  have hone_step : ∀ i : ℕ, E (i+1) + term i ≤ E i := by
    intro i
    -- Step x with ξ = x_i, simplify h(x_i, x_i) = 0
    have hx := alg.step_x i (alg.x i)
    have hx_simp : f (alg.x (i+1)) + α i * h (alg.x i) (alg.x (i+1)) + β i * c (alg.x (i+1)) (alg.y i) ≤
        f (alg.x i) + β i * c (alg.x i) (alg.y i) := by
      simpa [hyp.h_diag_zero (alg.x i)] using hx
    -- Step y with η = y_i, simplify k(y_i, y_i) = 0
    have hy := alg.step_y i (alg.y i)
    have hy_simp : g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        g (alg.y i) + β i * c (alg.x (i+1)) (alg.y i) := by
      simpa [hyp.k_diag_zero (alg.y i)] using hy
    -- Add the two and cancel the common β_i*c(x_{i+1}, y_i) term
    have hadd := add_le_add hx_simp hy_simp
    have hmain : f (alg.x (i+1)) + g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) +
        α i * h (alg.x i) (alg.x (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) := by
      linarith
    -- Since β is nonincreasing and c ≥ 0: β_{i+1}*c ≤ β_i*c
    have hbeta_c : β (i+1) * c (alg.x (i+1)) (alg.y (i+1)) ≤
        β i * c (alg.x (i+1)) (alg.y (i+1)) :=
      mul_le_mul_of_nonneg_right (hbeta_nonincreasing i) (hyp.c_nonneg _ _)
    -- Now combine: E(i+1) = f+g+β_{i+1}*c ≤ f+g+β_i*c, then add nonneg terms, use hmain
    unfold E term
    nlinarith
  -- Each term is nonnegative, so partial sums form a monotone sequence
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ term n := by
    intro n
    unfold term
    have h1 : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) :=
      mul_nonneg (hyp.alpha_nonneg n) (hyp.h_nonneg _ _)
    have h2 : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) :=
      mul_nonneg (hyp.nu_nonneg n) (hyp.k_nonneg _ _)
    nlinarith
  have hS_succ : ∀ N : ℕ, S_seq N ≤ S_seq (N+1) := by
    intro N
    unfold S_seq
    rw [Finset.sum_range_succ]
    have h : 0 ≤ term N := hterm_nonneg N
    nlinarith
  have hS_mono : Monotone S_seq :=
    monotone_nat_of_le_succ hS_succ
  -- E is bounded below by Mf + Mg (since f, g bounded below, β>0, c≥0)
  rcases hyp.f_bdd_below with ⟨Mf, hMf⟩
  rcases hyp.g_bdd_below with ⟨Mg, hMg⟩
  have hE_lower : ∀ i : ℕ, Mf + Mg ≤ E i := by
    intro i
    unfold E
    have hf : Mf ≤ f (alg.x i) := hMf (alg.x i)
    have hg : Mg ≤ g (alg.y i) := hMg (alg.y i)
    have hc_nonneg : 0 ≤ c (alg.x i) (alg.y i) := hyp.c_nonneg _ _
    have hbeta_pos : 0 < β i := hyp.beta_pos i
    nlinarith
  -- Telescoping sum: S_seq(N) = Σ_{i=0}^{N-1} term(i) ≤ E(0) - E(N)
  have hsum_bound : ∀ N : ℕ, S_seq N ≤ E 0 - E N := by
    intro N
    induction' N with N ih
    · unfold S_seq; simp
    · unfold S_seq
      rw [Finset.sum_range_succ]
      have hterm_bound : term N ≤ E N - E (N+1) := by
        linarith [hone_step N]
      nlinarith
  have hS_upper : ∀ N : ℕ, S_seq N ≤ E 0 - (Mf + Mg) := by
    intro N
    have h1 : S_seq N ≤ E 0 - E N := hsum_bound N
    have h2 : Mf + Mg ≤ E N := hE_lower N
    linarith
  -- Bounded monotone sequence in ℝ converges to its supremum
  have h_bdd : BddAbove (Set.range S_seq) := by
    refine ⟨E 0 - (Mf + Mg), ?_⟩
    rintro y ⟨N, rfl⟩
    exact hS_upper N
  refine ⟨⨆ n, S_seq n, tendsto_atTop_ciSup hS_mono h_bdd⟩
