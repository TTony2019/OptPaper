import Mathlib

/-!
# Lemma 4.2: INE(0,β,μ,0) = argmin L_{β,μ}

Under the quadratic-cost Hilbert setting (H41-H45), the inertial Nash equilibria
INE(0,β,μ,0) coincide with the minimizers of L_{β,μ}(ξ,η) = μ f(ξ) + β g(η) + βμ‖ξ-η‖²/2.

Depends on: def_1 (IsINE), ext_def_1 (proximalOperator), ext_def_2 (IsFirmlyNonexpansive).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set
open scoped InnerProductSpace

/-- Inertial Nash Equilibrium (duplicated for self-containment). -/
def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

/-- The subdifferential of a convex function. -/
def subgradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (x : H) : Set H :=
  {u : H | ∀ y : H, f y ≥ f x + inner ℝ u (y - x)}

/-- Assumptions H41-H45: Quadratic cost on Hilbert space. -/
structure H41toH45 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → ℝ) (β μ : ℝ) : Prop where
  h41 : True -- H = X = Y is a Hilbert space (already captured by type)
  h42_f_conv : ConvexOn ℝ (Set.univ : Set H) f
  h42_g_conv : ConvexOn ℝ (Set.univ : Set H) g
  h42_f_lsc : LowerSemicontinuous f
  h42_g_lsc : LowerSemicontinuous g
  h42_f_bdd_below : ∃ Mf : ℝ, ∀ x : H, f x ≥ Mf
  h42_g_bdd_below : ∃ Mg : ℝ, ∀ y : H, g y ≥ Mg
  h43 : True -- quadratic costs: h(ξ,η)=k(ξ,η)=c(ξ,η)=‖ξ-η‖²/2
  beta_pos : β > 0
  mu_pos : μ > 0

/-- The Lagrangian L_{β,μ}(ξ,η) = μ f(ξ) + β g(η) + (βμ/2)‖ξ-η‖². -/
noncomputable def L_beta_mu {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → ℝ) (β μ : ℝ) (ξ η : H) : ℝ :=
  μ * f ξ + β * g η + (β * μ / 2) * ‖ξ - η‖ ^ 2

/-- If f is convex and xbar minimizes f + (β/2)‖· - ybar‖², then
f(z) ≥ f(xbar) + ⟨β(ybar-xbar), z-xbar⟩.  This is the key subgradient
inequality derived via perturbation and convexity. -/
private lemma subgrad_of_convex_min {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → ℝ} (hf : ConvexOn ℝ (Set.univ : Set H) f) {xbar ybar : H} {β : ℝ} (hβpos : β > 0)
    (hmin : ∀ ξ : H, f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤ f ξ + β * (‖ξ - ybar‖ ^ 2 / 2))
    (z : H) : f z ≥ f xbar + inner ℝ (β • (ybar - xbar)) (z - xbar) := by
  by_cases hz : z = xbar
  · subst z; simp
  · have hznorm_sq_pos : ‖z - xbar‖ ^ 2 > 0 := by
      have hznz : ‖z - xbar‖ ≠ 0 :=
        mt norm_eq_zero.mp (sub_ne_zero.mpr hz)
      positivity
    apply le_of_forall_pos_le_add
    intro ε hεpos
    -- Choose t ∈ (0,1) such that (β*t/2)‖z-xbar‖² ≤ ε
    have hden_pos : β * ‖z - xbar‖ ^ 2 > 0 := by nlinarith
    set t : ℝ := min (1/2) (2 * ε / (β * ‖z - xbar‖ ^ 2)) with ht_def
    have htpos : 0 < t := by
      refine lt_min_iff.mpr ⟨by norm_num, div_pos (by linarith) hden_pos⟩
    have htlt1 : t < 1 := by
      calc
        t ≤ 1/2 := min_le_left _ _
        _ < 1 := by norm_num
    have ht_nonneg : 0 ≤ t := by linarith
    -- Bound the t-error term: (β*t/2)*‖z-xbar‖² ≤ ε
    have hznorm_ne_zero : ‖z - xbar‖ ≠ 0 := by
      intro hzero
      have : ‖z - xbar‖ ^ 2 = 0 := by simp [hzero]
      linarith
    have ht_bound : (β * t / 2) * ‖z - xbar‖ ^ 2 ≤ ε := by
      have htle : t ≤ 2 * ε / (β * ‖z - xbar‖ ^ 2) := min_le_right _ _
      calc
        (β * t / 2) * ‖z - xbar‖ ^ 2 = t * (β * ‖z - xbar‖ ^ 2) / 2 := by ring
        _ ≤ (2 * ε / (β * ‖z - xbar‖ ^ 2)) * (β * ‖z - xbar‖ ^ 2) / 2 := by nlinarith
        _ = (2 * ε) / 2 := by
          field_simp [hβpos.ne', hznorm_ne_zero]
        _ = ε := by norm_num
    set zt := (1 - t) • xbar + t • z with hzt_def
    -- Convexity: f(zt) ≤ (1-t)f(xbar) + t f(z)
    have h_conv : f zt ≤ (1 - t) * f xbar + t * f z := by
      have h := hf.2 (mem_univ xbar) (mem_univ z) (by linarith) ht_nonneg
        (by ring : (1 - t) + t = 1)
      simpa [hzt_def] using h
    -- Optimality: xbar minimizes f + (β/2)‖·-ybar‖²
    have h_opt : f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤ f zt + β * (‖zt - ybar‖ ^ 2 / 2) :=
      hmin zt
    -- Expand: zt - ybar = (xbar - ybar) + t•(z - xbar)
    have h_zt_diff : zt - ybar = (xbar - ybar) + t • (z - xbar) := by
      dsimp [zt]
      calc
        ((1 - t) • xbar + t • z) - ybar = (xbar - t • xbar + t • z) - ybar := by
          simp [sub_smul]
        _ = (xbar - ybar) + t • z - t • xbar := by abel
        _ = (xbar - ybar) + (t • z - t • xbar) := by abel
        _ = (xbar - ybar) + t • (z - xbar) := by rw [smul_sub]
    have h_zt_norm_sq : ‖zt - ybar‖ ^ 2 = ‖xbar - ybar‖ ^ 2 +
        2 * t * inner ℝ (xbar - ybar) (z - xbar) + t ^ 2 * ‖z - xbar‖ ^ 2 := by
      rw [h_zt_diff]
      calc
        ‖(xbar - ybar) + t • (z - xbar)‖ ^ 2
            = ‖xbar - ybar‖ ^ 2 + 2 * inner ℝ (xbar - ybar) (t • (z - xbar))
              + ‖t • (z - xbar)‖ ^ 2 := norm_add_sq_real _ _
        _ = ‖xbar - ybar‖ ^ 2 + 2 * inner ℝ (xbar - ybar) (t • (z - xbar))
              + (t ^ 2 * ‖z - xbar‖ ^ 2) := by
          have h_ns : ‖t • (z - xbar)‖ ^ 2 = t ^ 2 * ‖z - xbar‖ ^ 2 := by
            simp [norm_smul, abs_of_pos htpos, mul_pow]
          rw [h_ns]
        _ = ‖xbar - ybar‖ ^ 2 + 2 * t * inner ℝ (xbar - ybar) (z - xbar)
              + t ^ 2 * ‖z - xbar‖ ^ 2 := by
          simp [inner_smul_right]
          ring
    -- Derive: f(z) - f(xbar) ≥ ⟨β•(ybar-xbar), z-xbar⟩ - (βt/2)‖z-xbar‖²
    have hineq : f z - f xbar ≥ inner ℝ (β • (ybar - xbar)) (z - xbar) -
        (β * t / 2) * ‖z - xbar‖ ^ 2 := by
      have h_opt_rearr : f zt - f xbar ≥ (β / 2) * (‖xbar - ybar‖ ^ 2 - ‖zt - ybar‖ ^ 2) := by
        linarith
      have h_conv_rearr : f zt - f xbar ≤ t * (f z - f xbar) := by
        linarith
      have h_combined : t * (f z - f xbar) ≥ (β / 2) * (‖xbar - ybar‖ ^ 2 - ‖zt - ybar‖ ^ 2) := by
        linarith
      rw [h_zt_norm_sq] at h_combined
      -- Simplify ‖xbar-ybar‖² - (‖xbar-ybar‖² + 2t⟨x-y,z-x⟩ + t²‖z-x‖²)
      -- = -2t⟨x-y,z-x⟩ - t²‖z-x‖²
      have h_simp : ‖xbar - ybar‖ ^ 2 -
          (‖xbar - ybar‖ ^ 2 + 2 * t * inner ℝ (xbar - ybar) (z - xbar) + t ^ 2 * ‖z - xbar‖ ^ 2)
          = -2 * t * inner ℝ (xbar - ybar) (z - xbar) - t ^ 2 * ‖z - xbar‖ ^ 2 := by ring
      rw [h_simp] at h_combined
      -- Swap: ⟨xbar-ybar, z-xbar⟩ = -⟨ybar-xbar, z-xbar⟩
      have h_inner_swap : inner ℝ (xbar - ybar) (z - xbar) = -inner ℝ (ybar - xbar) (z - xbar) := by
        calc
          inner ℝ (xbar - ybar) (z - xbar)
              = inner ℝ xbar (z - xbar) - inner ℝ ybar (z - xbar) := by rw [inner_sub_left]
          _ = -(inner ℝ ybar (z - xbar) - inner ℝ xbar (z - xbar)) := by ring
          _ = -inner ℝ (ybar - xbar) (z - xbar) := by rw [inner_sub_left]
      rw [h_inner_swap] at h_combined
      -- h_combined: t(fz-fx) ≥ (β/2)(-2t*(-⟨y-x,z-x⟩) - t²‖z-x‖²)
      -- = t * (β*inner(y-x,z-x) - (βt/2)‖z-x‖²)
      have h_simp2 : (β / 2) * (-2 * t * (-inner ℝ (ybar - xbar) (z - xbar)) - t ^ 2 * ‖z - xbar‖ ^ 2) =
          t * (β * inner ℝ (ybar - xbar) (z - xbar) - (β * t / 2) * ‖z - xbar‖ ^ 2) := by ring
      rw [h_simp2] at h_combined
      -- h_combined: t*(fz-fx) ≥ t*(β*inner(y-x,z-x) - (βt/2)‖z-x‖²)
      -- Cancel t > 0
      have h_cancel : f z - f xbar ≥ β * inner ℝ (ybar - xbar) (z - xbar) -
          (β * t / 2) * ‖z - xbar‖ ^ 2 :=
        le_of_mul_le_mul_left h_combined htpos
      simpa [inner_smul_left] using h_cancel
    -- Since (βt/2)‖z-xbar‖² ≤ ε, we have f(z) ≥ f(xbar) + inner(β•(y-x), z-x) - ε
    have h_final : f z ≥ f xbar + inner ℝ (β • (ybar - xbar)) (z - xbar) - ε := by
      linarith
    linarith

/-- Lemma 4.2: INE(0,β,μ,0) = argmin L_{β,μ}. -/
theorem lemma_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} (hyp : H41toH45 H f g β μ) (xbar ybar : H) :
    IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar ↔
    (∀ ξ η : H, L_beta_mu f g β μ xbar ybar ≤ L_beta_mu f g β μ ξ η) := by
  have hβpos : β > 0 := hyp.beta_pos
  have hμpos : μ > 0 := hyp.mu_pos
  constructor
  · -- Direction (→) : INE → minimizer of L
    rintro ⟨hx_opt, hy_opt⟩ ξ η
    -- Simplify hx_opt and hy_opt
    have hx_simp : ∀ ξ' : H, f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤
        f ξ' + β * (‖ξ' - ybar‖ ^ 2 / 2) := by
      intro ξ'
      simpa using hx_opt ξ'
    have hy_simp : ∀ η' : H, g ybar + μ * (‖xbar - ybar‖ ^ 2 / 2) ≤
        g η' + μ * (‖xbar - η'‖ ^ 2 / 2) := by
      intro η'
      simpa using hy_opt η'
    -- Swap norm order for subgrad_of_convex_min
    have hy_simp' : ∀ η' : H, g ybar + μ * (‖ybar - xbar‖ ^ 2 / 2) ≤
        g η' + μ * (‖η' - xbar‖ ^ 2 / 2) := by
      intro η'
      simpa [norm_sub_rev] using hy_simp η'
    -- Subgradient inequalities
    have hf_sub : f ξ ≥ f xbar + inner ℝ (β • (ybar - xbar)) (ξ - xbar) :=
      subgrad_of_convex_min hyp.h42_f_conv hβpos hx_simp ξ
    have hg_sub : g η ≥ g ybar + inner ℝ (μ • (xbar - ybar)) (η - ybar) :=
      subgrad_of_convex_min hyp.h42_g_conv hμpos hy_simp' η
    set p := ξ - xbar with hp_def
    set q := η - ybar with hq_def
    set d := xbar - ybar with hd_def
    -- Combine the subgradient inequalities
    have hsum : μ * f ξ + β * g η ≥ μ * f xbar + β * g ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) := by
      have h1 : μ * f ξ ≥ μ * f xbar + μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) := by nlinarith
      have h2 : β * g η ≥ β * g ybar + β * inner ℝ (μ • (xbar - ybar)) (η - ybar) := by nlinarith
      have h_inner1 : μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) =
          (β * μ) * inner ℝ (ybar - xbar) p := by
        rw [inner_smul_left]
        simp [hp_def]
        ring
      have h_inner2 : β * inner ℝ (μ • (xbar - ybar)) (η - ybar) =
          (β * μ) * inner ℝ d q := by
        rw [inner_smul_left]
        simp [hd_def, hq_def]
        ring
      nlinarith
    -- Expand ‖ξ-η‖²
    have h_decomp : ‖ξ - η‖ ^ 2 = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 +
        2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
      calc
        ‖ξ - η‖ ^ 2 = ‖(p + d) - q‖ ^ 2 := by
          dsimp [p, d, q]
          abel
        _ = ‖p + d‖ ^ 2 - 2 * inner ℝ (p + d) q + ‖q‖ ^ 2 :=
          norm_sub_sq_real (p + d) q
        _ = (‖p‖ ^ 2 + 2 * inner ℝ p d + ‖d‖ ^ 2) - 2 * (inner ℝ p q + inner ℝ d q) + ‖q‖ ^ 2 := by
          rw [norm_add_sq_real p d, inner_add_left]
        _ = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
          rw [real_inner_comm p d]
          ring
    -- L inequality with norm differences
    have hLpre : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
        (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
      dsimp [L_beta_mu]
      nlinarith
    -- Norm difference = the expansion from h_decomp
    have h_norm_diff : ‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2 =
        ‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
      rw [h_decomp]
      nlinarith
    -- Substitute into hLpre
    have hLmid : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
        (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
      calc
        L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
            (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
            (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := hLpre
        _ = L_beta_mu f g β μ xbar ybar +
            (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
            (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
          rw [h_norm_diff]
    -- Simplify: inner(ybar-xbar, p) = -inner(d, p)
    have h_inner_yp : inner ℝ (ybar - xbar) p = -inner ℝ d p := by
      calc
        inner ℝ (ybar - xbar) p = inner ℝ (-(xbar - ybar)) p := by simp
        _ = -inner ℝ (xbar - ybar) p := by rw [inner_neg_left]
        _ = -inner ℝ d p := by simp [hd_def]
    rw [h_inner_yp] at hLmid
    -- The cross + norm terms simplify to (βμ/2)*‖p-q‖²
    have h_key : (β * μ) * (-inner ℝ d p + inner ℝ d q) +
        (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) =
        (β * μ / 2) * ‖p - q‖ ^ 2 := by
      calc
        (β * μ) * (-inner ℝ d p + inner ℝ d q) +
            (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q)
            = (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 - 2 * inner ℝ p q) := by
          ring
        _ = (β * μ / 2) * ‖p - q‖ ^ 2 := by
          rw [norm_sub_sq_real p q]
          ring
    -- Final simplification
    have hLfinal : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ / 2) * ‖p - q‖ ^ 2 := by
      linarith
    have h_nonneg : (β * μ / 2) * ‖p - q‖ ^ 2 ≥ 0 := by
      have h_coeff : 0 ≤ β * μ / 2 := by nlinarith
      nlinarith [sq_nonneg ‖p - q‖]
    nlinarith
  · -- Direction (←) : minimizer of L → INE
    intro hmin
    constructor
    · intro ξ
      have h := hmin ξ ybar
      dsimp [L_beta_mu] at h
      have h_simp : f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤ f ξ + β * (‖ξ - ybar‖ ^ 2 / 2) := by
        nlinarith
      simpa
    · intro η
      have h := hmin xbar η
      dsimp [L_beta_mu] at h
      have h_simp : g ybar + μ * (‖xbar - ybar‖ ^ 2 / 2) ≤ g η + μ * (‖xbar - η‖ ^ 2 / 2) := by
        nlinarith
      simpa
