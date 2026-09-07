import Mathlib

open Set Filter Topology
open scoped RealInnerProductSpace

/-!
# Proposition 4.5: Asymptotic Behavior

Under H41-H47, the sequence (x_n, y_n) from (CA²) satisfies:
(i) y_n - x_n → y - x, x_{n+1} - x_n → 0, y_{n+1} - y_n → 0 in norm;
(ii) ‖x_{n+1} - x‖ and ‖y_{n+1} - y‖ converge for any INE (x, y).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

/-- The Cognitive Alternating Algorithm (CA²) on abstract spaces `X` and `Y`.
    (Self-contained; duplicates algo_1 for compilation independence.) -/
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

/-- An Inertial Nash Equilibrium INE(α, β, μ, ν) on abstract spaces X, Y.
    (Self-contained; duplicates def_1 for compilation independence.) -/
def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

/-- Assumptions H41-H46 for the quadratic Hilbert-space case. -/
structure H41toH46 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → ℝ) (β μ : ℝ) where
  f_conv : ConvexOn ℝ (Set.univ : Set H) f
  g_conv : ConvexOn ℝ (Set.univ : Set H) g
  f_lsc : LowerSemicontinuous f
  g_lsc : LowerSemicontinuous g
  f_bdd_below : ∃ Mf : ℝ, ∀ x : H, f x ≥ Mf
  g_bdd_below : ∃ Mg : ℝ, ∀ y : H, g y ≥ Mg
  beta_pos : β > 0
  mu_pos : μ > 0
  ine_nonempty : ∃ (x y : H),
    IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y

/-- The positive part of a real number: a⁺ = max(a, 0). -/
def positivePart (a : ℝ) : ℝ := max a 0

/-- H47: The positive variations of α_n and ν_n are summable.
    Consequently α_n and ν_n converge. -/
def H47 (α ν : ℕ → ℝ) : Prop :=
  Summable (fun n => positivePart (α (n+1) - α n)) ∧
  Summable (fun n => positivePart (ν (n+1) - ν n))

set_option maxHeartbeats 2000000

/-!
## Lemma 4.3 inequalities (private, from `lem_3.lean`)

These are proved in `lem_3.lean` using firm nonexpansiveness of resolvent operators
and subgradient inequalities from convex minimization.
-/

/--
Subgradient inequality from convexity + quadratic minimization.
If f is convex and p minimizes ξ ↦ f(ξ) + (α/2)·‖u-ξ‖² + (β/2)·‖ξ-v‖²,
then f(z) ≥ f(p) + ⟪α·(u-p) + β·(v-p), z-p⟫ for all z.
-/
private lemma subgrad_of_min_quadratic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → ℝ} (hf : ConvexOn ℝ (Set.univ : Set H) f)
    (p u v : H) (α β : ℝ)
    (hmin : ∀ ξ : H, f p + (α / 2) * ‖u - p‖ ^ 2 + (β / 2) * ‖p - v‖ ^ 2 ≤
                     f ξ + (α / 2) * ‖u - ξ‖ ^ 2 + (β / 2) * ‖ξ - v‖ ^ 2)
    (z : H) : f z ≥ f p + inner ℝ (α • (u - p) + β • (v - p)) (z - p) := by
  by_cases hz : z = p
  · subst z; simp
  · have hznorm_sq_pos : ‖z - p‖ ^ 2 > 0 := by
      have hznz : ‖z - p‖ ≠ 0 := mt norm_eq_zero.mp (sub_ne_zero.mpr hz)
      positivity
    set σ := α + β
    by_cases hσpos : σ > 0
    · apply le_of_forall_pos_le_add; intro ε hεpos
      have hden_pos : σ * ‖z - p‖ ^ 2 > 0 := by nlinarith
      set t : ℝ := min (1/2) (2 * ε / (σ * ‖z - p‖ ^ 2))
      have htpos : 0 < t := by
        refine lt_min_iff.mpr ⟨by norm_num, div_pos (by linarith) hden_pos⟩
      have ht_nonneg : 0 ≤ t := by linarith
      set zt := p + t • (z - p)
      have hznorm_ne_zero : ‖z - p‖ ≠ 0 := by
        intro hzero
        have hsq : ‖z - p‖ ^ 2 = 0 := by simpa [hzero]
        nlinarith
      -- bound: (σ*t/2)*‖z-p‖² ≤ ε
      have ht_bound : (σ * t / 2) * ‖z - p‖ ^ 2 ≤ ε := by
        have htle : t ≤ 2 * ε / (σ * ‖z - p‖ ^ 2) := min_le_right _ _
        calc
          (σ * t / 2) * ‖z - p‖ ^ 2 = t * (σ * ‖z - p‖ ^ 2) / 2 := by ring
          _ ≤ (2 * ε / (σ * ‖z - p‖ ^ 2)) * (σ * ‖z - p‖ ^ 2) / 2 := by nlinarith
          _ = (2 * ε) / 2 := by field_simp [hσpos.ne', hznorm_ne_zero]
          _ = ε := by norm_num
      -- identify zt as a convex combination: zt = (1-t)•p + t•z
      have ht_le_half : t ≤ 1/2 := min_le_left _ _
      have h_one_minus_t_nonneg : 0 ≤ 1 - t := by linarith
      have hzt_conv : zt = (1 - t) • p + t • z := by
        dsimp [zt]
        calc
          p + t • (z - p) = p + (t • z - t • p) := by rw [smul_sub]
          _ = (p - t • p) + t • z := by abel
          _ = ((1 : ℝ) • p - t • p) + t • z := by simp
          _ = (1 - t) • p + t • z := by rw [sub_smul]
      -- convexity: f(zt) ≤ (1-t)f(p) + t f(z)
      have h_conv : f zt ≤ (1 - t) * f p + t * f z := by
        have h := hf.2 (mem_univ p) (mem_univ z) h_one_minus_t_nonneg ht_nonneg
          (by ring : (1 - t) + t = 1)
        simpa [hzt_conv, smul_eq_mul] using h
      -- optimality at p
      have h_opt : f p + (α / 2) * ‖u - p‖ ^ 2 + (β / 2) * ‖p - v‖ ^ 2 ≤
                  f zt + (α / 2) * ‖u - zt‖ ^ 2 + (β / 2) * ‖zt - v‖ ^ 2 := hmin zt
      -- expand ‖u - zt‖² and ‖zt - v‖²
      have h_u_zt : ‖u - zt‖ ^ 2 = ‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by abel
        rw [this]
        rw [norm_sub_sq_real]
        simp [inner_smul_right, norm_smul, abs_of_pos htpos]
        ring
      have h_zt_v : ‖zt - v‖ ^ 2 = ‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : (p + t • (z - p)) - v = (p - v) + t • (z - p) := by abel
        rw [this]
        rw [norm_add_sq_real]
        simp [inner_smul_right, norm_smul, abs_of_pos htpos]
        ring
      -- algebraic combination: α/2·(‖u-p‖² - ‖u-zt‖²) + β/2·(‖p-v‖² - ‖zt-v‖²) = ...
      have h_quad_diff : (α / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (β / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) =
          t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        rw [h_u_zt, h_zt_v]
        have htemp1 : (‖u - p‖ ^ 2 - (‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2)) =
            2 * t * inner ℝ (u - p) (z - p) - t ^ 2 * ‖z - p‖ ^ 2 := by ring
        have htemp2 : (‖p - v‖ ^ 2 - (‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2)) =
            -(2 * t * inner ℝ (p - v) (z - p)) - t ^ 2 * ‖z - p‖ ^ 2 := by ring
        rw [htemp1, htemp2]
        have hcalc : (α / 2) * (2 * t * inner ℝ (u - p) (z - p) - t ^ 2 * ‖z - p‖ ^ 2) +
            (β / 2) * (-(2 * t * inner ℝ (p - v) (z - p)) - t ^ 2 * ‖z - p‖ ^ 2) =
            t * (α * inner ℝ (u - p) (z - p) - β * inner ℝ (p - v) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
          ring
        rw [hcalc]
        calc
          t * (α * inner ℝ (u - p) (z - p) - β * inner ℝ (p - v) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2
              = t * (inner ℝ (α • (u - p)) (z - p) - inner ℝ (β • (p - v)) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            simp [inner_smul_left]
          _ = t * (inner ℝ (α • (u - p)) (z - p) + inner ℝ (β • (v - p)) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            have : inner ℝ (β • (p - v)) (z - p) = -inner ℝ (β • (v - p)) (z - p) := by
              calc
                inner ℝ (β • (p - v)) (z - p) = β * inner ℝ (p - v) (z - p) := by simp [inner_smul_left]
                _ = β * (-inner ℝ (v - p) (z - p)) := by
                  have hpq : p - v = -(v - p) := by abel
                  rw [hpq, inner_neg_left]
                _ = -inner ℝ (β • (v - p)) (z - p) := by simp [inner_smul_left]
            rw [this]
            ring
          _ = t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            rw [inner_add_left]
      -- combine everything
      have h_rearr : f zt - f p ≥ (α / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (β / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) := by linarith
      have h_conv_rearr : f zt - f p ≤ t * (f z - f p) := by linarith
      have h_combined : t * (f z - f p) ≥ t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by linarith
      have h_divided : f z - f p ≥ inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ * t / 2) * ‖z - p‖ ^ 2 := by
        have htemp : t * (f z - f p) ≥ t * (inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ * t / 2) * ‖z - p‖ ^ 2) := by nlinarith
        exact (le_of_mul_le_mul_left htemp htpos)
      have h_final : f z ≥ f p + inner ℝ (α • (u - p) + β • (v - p)) (z - p) - ε := by nlinarith
      linarith
    · -- σ ≤ 0: the correction term is nonnegative, so we get a direct inequality
      have hσ_nonpos : σ ≤ 0 := by linarith
      set t : ℝ := 1/2
      have htpos : 0 < t := by norm_num
      have ht_nonneg : 0 ≤ t := by linarith
      set zt := p + t • (z - p)
      have h_one_minus_t_nonneg' : 0 ≤ 1 - t := by dsimp [t]; norm_num
      have hzt_conv : zt = (1 - t) • p + t • z := by
        dsimp [zt]
        calc
          p + t • (z - p) = p + (t • z - t • p) := by rw [smul_sub]
          _ = (p - t • p) + t • z := by abel
          _ = ((1 : ℝ) • p - t • p) + t • z := by simp
          _ = (1 - t) • p + t • z := by rw [sub_smul]
      have h_conv : f zt ≤ (1 - t) * f p + t * f z := by
        have h := hf.2 (mem_univ p) (mem_univ z) h_one_minus_t_nonneg' ht_nonneg
          (by ring : (1 - t) + t = 1)
        simpa [hzt_conv, smul_eq_mul] using h
      have h_opt : f p + (α / 2) * ‖u - p‖ ^ 2 + (β / 2) * ‖p - v‖ ^ 2 ≤
                  f zt + (α / 2) * ‖u - zt‖ ^ 2 + (β / 2) * ‖zt - v‖ ^ 2 := hmin zt
      have h_u_zt : ‖u - zt‖ ^ 2 = ‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by abel
        rw [this, norm_sub_sq_real]
        simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_zt_v : ‖zt - v‖ ^ 2 = ‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : (p + t • (z - p)) - v = (p - v) + t • (z - p) := by abel
        rw [this, norm_add_sq_real]
        simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_quad_diff : (α / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (β / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) =
          t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        rw [h_u_zt, h_zt_v]
        have htemp1 : (‖u - p‖ ^ 2 - (‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2)) =
            2 * t * inner ℝ (u - p) (z - p) - t ^ 2 * ‖z - p‖ ^ 2 := by ring
        have htemp2 : (‖p - v‖ ^ 2 - (‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2)) =
            -(2 * t * inner ℝ (p - v) (z - p)) - t ^ 2 * ‖z - p‖ ^ 2 := by ring
        rw [htemp1, htemp2]
        have hcalc : (α / 2) * (2 * t * inner ℝ (u - p) (z - p) - t ^ 2 * ‖z - p‖ ^ 2) +
            (β / 2) * (-(2 * t * inner ℝ (p - v) (z - p)) - t ^ 2 * ‖z - p‖ ^ 2) =
            t * (α * inner ℝ (u - p) (z - p) - β * inner ℝ (p - v) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
          ring
        rw [hcalc]
        calc
          t * (α * inner ℝ (u - p) (z - p) - β * inner ℝ (p - v) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2
              = t * (inner ℝ (α • (u - p)) (z - p) - inner ℝ (β • (p - v)) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            simp [inner_smul_left]
          _ = t * (inner ℝ (α • (u - p)) (z - p) + inner ℝ (β • (v - p)) (z - p)) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            have : inner ℝ (β • (p - v)) (z - p) = -inner ℝ (β • (v - p)) (z - p) := by
              calc
                inner ℝ (β • (p - v)) (z - p) = β * inner ℝ (p - v) (z - p) := by simp [inner_smul_left]
                _ = β * (-inner ℝ (v - p) (z - p)) := by
                  have hpq : p - v = -(v - p) := by abel
                  rw [hpq, inner_neg_left]
                _ = -inner ℝ (β • (v - p)) (z - p) := by simp [inner_smul_left]
            rw [this]
            ring
          _ = t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
            rw [inner_add_left]
      have h_rearr : f zt - f p ≥ (α / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (β / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) := by linarith
      have h_conv_rearr : f zt - f p ≤ t * (f z - f p) := by linarith
      have h_mid : (α / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (β / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) ≤ t * (f z - f p) :=
        le_trans h_rearr h_conv_rearr
      rw [h_quad_diff] at h_mid
      -- h_mid: t*inner - (σ/2)*t²*‖z-p‖² ≤ t*(fz-fp)
      have h_ineq : t * (f z - f p) ≥ t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := h_mid
      -- Since σ ≤ 0, -(σ/2)*t²*‖z-p‖² ≥ 0, so t*(fz-fp) ≥ t*inner
      have h_nonneg_correction : 0 ≤ -(σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        have : σ / 2 ≤ 0 := by linarith
        nlinarith [sq_nonneg (t * ‖z - p‖)]
      have h_direct : t * (f z - f p) ≥ t * inner ℝ (α • (u - p) + β • (v - p)) (z - p) := by nlinarith
      -- Cancel t > 0: fz - fp ≥ inner, so fz ≥ fp + inner
      have h_result : f z - f p ≥ inner ℝ (α • (u - p) + β • (v - p)) (z - p) :=
        le_of_mul_le_mul_left h_direct htpos
      linarith

/--
Extract the x-minimization from INE(0,β,μ,0):
`f(x) + (β/2)·‖x-y‖² ≤ f(ξ) + (β/2)·‖ξ-y‖²` for all ξ.
-/
private lemma ine_x_min {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} (x y : H)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (ξ : H) :
    f x + (β / 2) * ‖x - y‖ ^ 2 ≤ f ξ + (β / 2) * ‖ξ - y‖ ^ 2 := by
  rcases hine with ⟨hine_f, _⟩
  have h := hine_f ξ
  have h_eq : (fun (ξ η : H) => ‖ξ - η‖ ^ 2 / 2) = fun ξ η => (1/2 : ℝ) * ‖ξ - η‖ ^ 2 := by
    ext u v; ring
  rw [h_eq] at h
  nlinarith

/--
Extract the y-minimization from INE(0,β,μ,0):
`g(y) + (μ/2)·‖x-y‖² ≤ g(η) + (μ/2)·‖x-η‖²` for all η.
-/
private lemma ine_y_min {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} (x y : H)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (η : H) :
    g y + (μ / 2) * ‖x - y‖ ^ 2 ≤ g η + (μ / 2) * ‖x - η‖ ^ 2 := by
  rcases hine with ⟨_, hine_g⟩
  have h := hine_g η
  simpa [mul_div_assoc, div_mul_eq_mul_div] using h

private lemma lemma_4_3_a {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (n : ℕ) :
    ‖alg.x (n+1) - x‖ ^ 2 ≤
    (1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
      α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 -
      β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) := by
  set xn1 := alg.x (n+1)
  set xn := alg.x n
  set yn := alg.y n
  set γ := α n + β
  have hβpos : β > 0 := hyp.beta_pos
  have hα_nonneg_n : α n ≥ 0 := hα_nonneg n
  have hγpos : γ > 0 := by linarith
  -- Step 1: x_{n+1} minimizes f(ξ) + (α_n/2)·‖xn-ξ‖² + (β/2)·‖ξ-yn‖²
  have hmin_xn1 : ∀ ξ : H, f xn1 + ((α n) / 2) * ‖xn - xn1‖ ^ 2 + (β / 2) * ‖xn1 - yn‖ ^ 2 ≤
      f ξ + ((α n) / 2) * ‖xn - ξ‖ ^ 2 + (β / 2) * ‖ξ - yn‖ ^ 2 := by
    intro ξ
    have hstep := alg.step_x n ξ
    nlinarith
  have hsubgrad_xn1 : ∀ z : H, f z ≥ f xn1 + inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (z - xn1) :=
    subgrad_of_min_quadratic hyp.f_conv xn1 xn yn (α n) β hmin_xn1
  -- Step 2: x minimizes f(ξ) + β/2·‖ξ-y‖² (from INE)
  have hmin_x : ∀ ξ : H, f x + ((0 : ℝ) / 2) * ‖x - x‖ ^ 2 + (β / 2) * ‖x - y‖ ^ 2 ≤
      f ξ + ((0 : ℝ) / 2) * ‖x - ξ‖ ^ 2 + (β / 2) * ‖ξ - y‖ ^ 2 := by
    intro ξ
    have h := ine_x_min x y hine ξ
    simp; nlinarith
  have hsubgrad_x : ∀ z : H, f z ≥ f x + inner ℝ ((0 : ℝ) • (x - x) + β • (y - x)) (z - x) :=
    subgrad_of_min_quadratic hyp.f_conv x x y 0 β hmin_x
  have hsubgrad_x_simp : ∀ z : H, f z ≥ f x + β * inner ℝ (y - x) (z - x) := by
    intro z; have h := hsubgrad_x z; simpa [inner_smul_left] using h
  -- Step 3: Combine to get firm nonexpansiveness
  have h1 : f x ≥ f xn1 + inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (x - xn1) := hsubgrad_xn1 x
  have h2 : f xn1 ≥ f x + β * inner ℝ (y - x) (xn1 - x) := hsubgrad_x_simp xn1
  -- Eliminate f:
  have hkey : α n * inner ℝ (xn - xn1) (x - xn1) + β * inner ℝ (yn - xn1) (x - xn1) - β * inner ℝ (y - x) (x - xn1) ≤ 0 := by
    have hfx_upper : f x - f xn1 ≤ β * inner ℝ (y - x) (x - xn1) := by
      have htemp : f xn1 - f x ≥ β * inner ℝ (y - x) (xn1 - x) := by linarith
      have : inner ℝ (y - x) (xn1 - x) = -inner ℝ (y - x) (x - xn1) := by
        have hx_xn1 : x - xn1 = -(xn1 - x) := by abel
        rw [hx_xn1, inner_neg_right, neg_neg]
      rw [this] at htemp
      linarith
    have hfx_lower : inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (x - xn1) ≤ f x - f xn1 := by linarith
    have h_expand : inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (x - xn1) =
        α n * inner ℝ (xn - xn1) (x - xn1) + β * inner ℝ (yn - xn1) (x - xn1) := by
      simp [inner_add_left, inner_smul_left]
    rw [h_expand] at hfx_lower
    linarith
  -- Expand inner products in terms of ‖xn1-x‖²
  have hx_inner : inner ℝ (xn - xn1) (x - xn1) = -inner ℝ (xn - x) (xn1 - x) + ‖xn1 - x‖ ^ 2 := by
    calc
      inner ℝ (xn - xn1) (x - xn1) = -inner ℝ (xn - xn1) (xn1 - x) := by
        have hx_xn1' : x - xn1 = -(xn1 - x) := by abel
        rw [hx_xn1', inner_neg_right]
      _ = -inner ℝ ((xn - x) - (xn1 - x)) (xn1 - x) := by abel
      _ = -(inner ℝ (xn - x) (xn1 - x) - inner ℝ (xn1 - x) (xn1 - x)) := by rw [inner_sub_left]
      _ = -inner ℝ (xn - x) (xn1 - x) + ‖xn1 - x‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
        ring
  have hy_inner : inner ℝ (yn - xn1) (x - xn1) = inner ℝ (y - x) (x - xn1) - inner ℝ (yn - y) (xn1 - x) + ‖xn1 - x‖ ^ 2 := by
    have hsum : yn - xn1 = (yn - y) + (y - x) + (x - xn1) := by abel
    rw [hsum]
    calc
      inner ℝ ((yn - y) + (y - x) + (x - xn1)) (x - xn1) =
          inner ℝ (yn - y) (x - xn1) + inner ℝ (y - x) (x - xn1) + inner ℝ (x - xn1) (x - xn1) := by
        rw [inner_add_left, inner_add_left]
      _ = inner ℝ (yn - y) (x - xn1) + inner ℝ (y - x) (x - xn1) + ‖x - xn1‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      _ = -inner ℝ (yn - y) (xn1 - x) + inner ℝ (y - x) (x - xn1) + ‖x - xn1‖ ^ 2 := by
        have : x - xn1 = -(xn1 - x) := by abel
        rw [this, inner_neg_right]
      _ = inner ℝ (y - x) (x - xn1) - inner ℝ (yn - y) (xn1 - x) + ‖x - xn1‖ ^ 2 := by ring
      _ = inner ℝ (y - x) (x - xn1) - inner ℝ (yn - y) (xn1 - x) + ‖xn1 - x‖ ^ 2 := by simp [norm_sub_rev]
  rw [hx_inner, hy_inner] at hkey
  -- hkey now simplifies: β*⟨y-x, x-xn1⟩ terms cancel
  have h_firm : γ * ‖xn1 - x‖ ^ 2 ≤ (α n) * inner ℝ (xn1 - x) (xn - x) + β * inner ℝ (xn1 - x) (yn - y) := by
    -- After canceling, we get: -αn*⟨xn-x, xn1-x⟩ - β*⟨yn-y, xn1-x⟩ + γ*‖xn1-x‖² ≤ 0
    have htemp : -α n * inner ℝ (xn - x) (xn1 - x) - β * inner ℝ (yn - y) (xn1 - x) + γ * ‖xn1 - x‖ ^ 2 ≤ 0 := by
      nlinarith
    have htemp2 : γ * ‖xn1 - x‖ ^ 2 ≤ α n * inner ℝ (xn - x) (xn1 - x) + β * inner ℝ (yn - y) (xn1 - x) := by nlinarith
    simpa [real_inner_comm (xn1 - x) (xn - x), real_inner_comm (xn1 - x) (yn - y)] using htemp2
  -- Step 4: Expand inner products using 2⟨u,v⟩ = ‖u‖² + ‖v‖² - ‖u-v‖²
  have h_inner_ident : ∀ (u v : H), inner ℝ u v = (1/2 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2) := by
    intro u v
    have := norm_sub_sq_real u v
    linarith
  have h_inner1 : inner ℝ (xn1 - x) (xn - x) = (1/2 : ℝ) * (‖xn1 - x‖ ^ 2 + ‖xn - x‖ ^ 2 - ‖xn1 - xn‖ ^ 2) := by
    have : (xn1 - x) - (xn - x) = xn1 - xn := by abel
    rw [h_inner_ident (xn1 - x) (xn - x), this]
  have h_inner2 : inner ℝ (xn1 - x) (yn - y) = (1/2 : ℝ) * (‖xn1 - x‖ ^ 2 + ‖yn - y‖ ^ 2 - ‖yn - xn1 - y + x‖ ^ 2) := by
    have hsub : (xn1 - x) - (yn - y) = xn1 - yn - x + y := by abel
    rw [h_inner_ident (xn1 - x) (yn - y), hsub]
    have hnorm_eq : ‖xn1 - yn - x + y‖ ^ 2 = ‖yn - xn1 - y + x‖ ^ 2 := by
      have : xn1 - yn - x + y = -(yn - xn1 - y + x) := by abel
      rw [this, norm_neg]
    rw [hnorm_eq]
  rw [h_inner1, h_inner2] at h_firm
  -- Rearrange: move (γ/2)*‖xn1-x‖² to LHS, multiply by 2
  have h_rearr : γ * ‖xn1 - x‖ ^ 2 ≤
      (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
    nlinarith
  -- Divide by γ > 0
  set A := α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2
  have h_div : ‖xn1 - x‖ ^ 2 ≤ A / γ := by
    calc
      ‖xn1 - x‖ ^ 2 = (γ * ‖xn1 - x‖ ^ 2) / γ := by field_simp [hγpos.ne']
      _ ≤ A / γ := (div_le_div_of_nonneg_right h_rearr (by linarith))
  simpa [A, div_eq_inv_mul, γ, xn1, xn, yn] using h_div

private lemma lemma_4_3_b {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (n : ℕ) :
    ‖alg.y (n+1) - y‖ ^ 2 ≤
    (1 / ((μ + ν n) * (α n + β))) * (μ * α n * ‖alg.x n - x‖ ^ 2 +
      (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
      μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 -
      ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
      μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
      μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) := by
  set yn1 := alg.y (n+1)
  set xn1 := alg.x (n+1)
  set yn := alg.y n
  set xn := alg.x n
  set γ := ν n + μ
  set lam := α n + β
  have hμpos : μ > 0 := hyp.mu_pos
  have hβpos : β > 0 := hyp.beta_pos
  have hν_nonneg_n : ν n ≥ 0 := hν_nonneg n
  have hα_nonneg_n : α n ≥ 0 := hα_nonneg n
  have hγpos : γ > 0 := by linarith
  have hlampos : lam > 0 := by linarith
  -- Step 1: y_{n+1} minimizes g(η) + (μ/2)·‖x_{n+1}-η‖² + (ν_n/2)·‖y_n-η‖²
  have hmin_yn1 : ∀ η : H, g yn1 + (μ / 2) * ‖xn1 - yn1‖ ^ 2 + (ν n / 2) * ‖yn - yn1‖ ^ 2 ≤
      g η + (μ / 2) * ‖xn1 - η‖ ^ 2 + (ν n / 2) * ‖yn - η‖ ^ 2 := by
    intro η
    have hstep := alg.step_y n η
    nlinarith
  -- rewrite hmin_yn1 to match subgrad_of_min_quadratic's expected form
  have hmin_yn1' : ∀ ξ : H, g yn1 + (μ / 2) * ‖xn1 - yn1‖ ^ 2 + ((ν n) / 2) * ‖yn1 - yn‖ ^ 2 ≤
      g ξ + (μ / 2) * ‖xn1 - ξ‖ ^ 2 + ((ν n) / 2) * ‖ξ - yn‖ ^ 2 := by
    intro ξ
    have h := hmin_yn1 ξ
    simpa [norm_sub_rev] using h
  have hsubgrad_yn1 : ∀ z : H, g z ≥ g yn1 + inner ℝ (μ • (xn1 - yn1) + (ν n) • (yn - yn1)) (z - yn1) :=
    subgrad_of_min_quadratic hyp.g_conv yn1 xn1 yn μ (ν n) hmin_yn1'
  -- Step 2: y minimizes g(η) + (μ/2)·‖x-η‖² (from INE)
  have hmin_y : ∀ η : H, g y + ((0 : ℝ) / 2) * ‖y - y‖ ^ 2 + (μ / 2) * ‖y - x‖ ^ 2 ≤
      g η + ((0 : ℝ) / 2) * ‖y - η‖ ^ 2 + (μ / 2) * ‖η - x‖ ^ 2 := by
    intro η
    have h := ine_y_min x y hine η
    have h0y : ((0 : ℝ) / 2) * ‖y - y‖ ^ 2 = 0 := by simp
    have h0η : ((0 : ℝ) / 2) * ‖y - η‖ ^ 2 = 0 := by simp
    simpa [norm_sub_rev, h0y, h0η, add_zero, zero_add] using h
  have hsubgrad_y : ∀ z : H, g z ≥ g y + inner ℝ ((0 : ℝ) • (y - y) + μ • (x - y)) (z - y) :=
    subgrad_of_min_quadratic hyp.g_conv y y x 0 μ hmin_y
  have hsubgrad_y_simp : ∀ z : H, g z ≥ g y + μ * inner ℝ (x - y) (z - y) := by
    intro z; have h := hsubgrad_y z; simpa [inner_smul_left] using h
  -- Step 3: Combine to get firm nonexpansiveness
  have h1 : g y ≥ g yn1 + inner ℝ (μ • (xn1 - yn1) + (ν n) • (yn - yn1)) (y - yn1) := hsubgrad_yn1 y
  have h2 : g yn1 ≥ g y + μ * inner ℝ (x - y) (yn1 - y) := hsubgrad_y_simp yn1
  -- Eliminate g:
  have hkey : μ * inner ℝ (xn1 - yn1) (y - yn1) + (ν n) * inner ℝ (yn - yn1) (y - yn1) -
      μ * inner ℝ (x - y) (y - yn1) ≤ 0 := by
    have hgy_upper : g y - g yn1 ≤ μ * inner ℝ (x - y) (y - yn1) := by
      have htemp : g yn1 - g y ≥ μ * inner ℝ (x - y) (yn1 - y) := by linarith
      have : inner ℝ (x - y) (yn1 - y) = -inner ℝ (x - y) (y - yn1) := by
        have hsub : yn1 - y = -(y - yn1) := by abel
        rw [hsub, inner_neg_right]
      rw [this] at htemp
      linarith
    have hgy_lower : inner ℝ (μ • (xn1 - yn1) + (ν n) • (yn - yn1)) (y - yn1) ≤ g y - g yn1 := by linarith
    have h_expand : inner ℝ (μ • (xn1 - yn1) + (ν n) • (yn - yn1)) (y - yn1) =
        μ * inner ℝ (xn1 - yn1) (y - yn1) + (ν n) * inner ℝ (yn - yn1) (y - yn1) := by
      simp [inner_add_left, inner_smul_left]
    rw [h_expand] at hgy_lower
    linarith
  -- Expand inner products in terms of ‖yn1-y‖²
  have hx_inner : inner ℝ (xn1 - yn1) (y - yn1) =
      -inner ℝ (xn1 - x) (yn1 - y) - inner ℝ (x - y) (yn1 - y) + ‖yn1 - y‖ ^ 2 := by
    have hsum : xn1 - yn1 = (xn1 - x) + (x - y) - (yn1 - y) := by abel
    rw [hsum]
    calc
      inner ℝ ((xn1 - x) + (x - y) - (yn1 - y)) (y - yn1) =
          inner ℝ ((xn1 - x) + (x - y) - (yn1 - y)) (-(yn1 - y)) := by simp
      _ = -inner ℝ ((xn1 - x) + (x - y) - (yn1 - y)) (yn1 - y) := by rw [inner_neg_right]
      _ = -(inner ℝ (xn1 - x) (yn1 - y) + inner ℝ (x - y) (yn1 - y) - inner ℝ (yn1 - y) (yn1 - y)) := by
        rw [inner_sub_left, inner_add_left]
      _ = -inner ℝ (xn1 - x) (yn1 - y) - inner ℝ (x - y) (yn1 - y) + inner ℝ (yn1 - y) (yn1 - y) := by ring
      _ = -inner ℝ (xn1 - x) (yn1 - y) - inner ℝ (x - y) (yn1 - y) + ‖yn1 - y‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
  have hy_inner : inner ℝ (yn - yn1) (y - yn1) = -inner ℝ (yn - y) (yn1 - y) + ‖yn1 - y‖ ^ 2 := by
    calc
      inner ℝ (yn - yn1) (y - yn1) = inner ℝ (yn - yn1) (-(yn1 - y)) := by simp
      _ = -inner ℝ (yn - yn1) (yn1 - y) := by rw [inner_neg_right]
      _ = -inner ℝ ((yn - y) - (yn1 - y)) (yn1 - y) := by abel
      _ = -(inner ℝ (yn - y) (yn1 - y) - inner ℝ (yn1 - y) (yn1 - y)) := by rw [inner_sub_left]
      _ = -inner ℝ (yn - y) (yn1 - y) + inner ℝ (yn1 - y) (yn1 - y) := by ring
      _ = -inner ℝ (yn - y) (yn1 - y) + ‖yn1 - y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  rw [hx_inner, hy_inner] at hkey
  -- rewrite inner ℝ (x - y) (y - yn1) = -inner ℝ (x - y) (yn1 - y) for cancellation
  have h_inner_sign : inner ℝ (x - y) (y - yn1) = -inner ℝ (x - y) (yn1 - y) := by
    have : y - yn1 = -(yn1 - y) := by abel
    rw [this, inner_neg_right]
  rw [h_inner_sign] at hkey
  -- hkey simplifies: the μ*⟨x-y, yn1-y⟩ terms cancel
  have h_firm : γ * ‖yn1 - y‖ ^ 2 ≤ μ * inner ℝ (yn1 - y) (xn1 - x) + (ν n) * inner ℝ (yn1 - y) (yn - y) := by
    -- After canceling, we get: -μ*⟨xn1-x, yn1-y⟩ - ν_n*⟨yn-y, yn1-y⟩ + γ*‖yn1-y‖² ≤ 0
    have htemp : -μ * inner ℝ (xn1 - x) (yn1 - y) - (ν n) * inner ℝ (yn - y) (yn1 - y) + γ * ‖yn1 - y‖ ^ 2 ≤ 0 := by
      nlinarith
    have htemp2 : γ * ‖yn1 - y‖ ^ 2 ≤ μ * inner ℝ (xn1 - x) (yn1 - y) + (ν n) * inner ℝ (yn - y) (yn1 - y) := by
      nlinarith
    simpa [real_inner_comm (yn1 - y) (xn1 - x), real_inner_comm (yn1 - y) (yn - y)] using htemp2
  -- Step 4: Expand inner products using 2⟨u,v⟩ = ‖u‖² + ‖v‖² - ‖u-v‖²
  have h_inner_ident : ∀ (u v : H), inner ℝ u v = (1/2 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2) := by
    intro u v
    have := norm_sub_sq_real u v
    linarith
  have h_inner1 : inner ℝ (yn1 - y) (xn1 - x) = (1/2 : ℝ) * (‖yn1 - y‖ ^ 2 + ‖xn1 - x‖ ^ 2 - ‖yn1 - xn1 - y + x‖ ^ 2) := by
    have : (yn1 - y) - (xn1 - x) = yn1 - xn1 - y + x := by abel
    rw [h_inner_ident (yn1 - y) (xn1 - x), this]
  have h_inner2 : inner ℝ (yn1 - y) (yn - y) = (1/2 : ℝ) * (‖yn1 - y‖ ^ 2 + ‖yn - y‖ ^ 2 - ‖yn1 - yn‖ ^ 2) := by
    have : (yn1 - y) - (yn - y) = yn1 - yn := by abel
    rw [h_inner_ident (yn1 - y) (yn - y), this]
  rw [h_inner1, h_inner2] at h_firm
  -- Rearrange: multiply by 2 and move terms → intermediate y-bound
  have h_intermediate : ‖yn1 - y‖ ^ 2 ≤
      (1 / γ) * (μ * ‖xn1 - x‖ ^ 2 + (ν n) * ‖yn - y‖ ^ 2 -
        μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) := by
    have h_ineq : γ * ‖yn1 - y‖ ^ 2 ≤
        μ * (‖xn1 - x‖ ^ 2 - ‖yn1 - xn1 - y + x‖ ^ 2) + (ν n) * (‖yn - y‖ ^ 2 - ‖yn1 - yn‖ ^ 2) := by
      nlinarith
    have h_comb : ‖yn1 - y‖ ^ 2 ≤
        (μ * (‖xn1 - x‖ ^ 2 - ‖yn1 - xn1 - y + x‖ ^ 2) + (ν n) * (‖yn - y‖ ^ 2 - ‖yn1 - yn‖ ^ 2)) / γ := by
      calc
        ‖yn1 - y‖ ^ 2 = (γ * ‖yn1 - y‖ ^ 2) / γ := by field_simp [hγpos.ne']
        _ ≤ (μ * (‖xn1 - x‖ ^ 2 - ‖yn1 - xn1 - y + x‖ ^ 2) + (ν n) * (‖yn - y‖ ^ 2 - ‖yn1 - yn‖ ^ 2)) / γ :=
          (div_le_div_of_nonneg_right h_ineq (by linarith))
    have h_eq : (μ * (‖xn1 - x‖ ^ 2 - ‖yn1 - xn1 - y + x‖ ^ 2) + (ν n) * (‖yn - y‖ ^ 2 - ‖yn1 - yn‖ ^ 2)) / γ =
        (1 / γ) * (μ * ‖xn1 - x‖ ^ 2 + (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) := by
      field_simp [hγpos.ne']
      ring
    rw [h_eq] at h_comb
    exact h_comb
  -- Step 5: Substitute the bound for ‖xn1-x‖² from lemma_4_3_a
  have hx_bound : ‖xn1 - x‖ ^ 2 ≤
      (1 / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
    have := lemma_4_3_a hyp x y hα_nonneg hν_nonneg alg hine n
    simpa [xn1, xn, yn, lam] using this
  -- Multiply the x-bound by μ, combine with intermediate y-bound
  have h_combined : μ * ‖xn1 - x‖ ^ 2 ≤
      (μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
    have h_mul : μ * ‖xn1 - x‖ ^ 2 ≤
        μ * ((1 / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hx_bound (by linarith)
    refine le_trans h_mul ?_
    have h_eq : μ * ((1 / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) =
        (μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
      ring
    rw [h_eq]
  have h_step1 : ‖yn1 - y‖ ^ 2 ≤
      (1 / γ) * ((μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) +
        (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) := by
    have hpos : 0 < 1 / γ := by positivity
    have h_upper : (1 / γ) * (μ * ‖xn1 - x‖ ^ 2 + (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) ≤
        (1 / γ) * ((μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) +
          (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) := by
      have h_inner : μ * ‖xn1 - x‖ ^ 2 + (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2 ≤
          (μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) +
          (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left h_inner (by positivity)
    linarith
  -- Step 6: Combine denominators: (1/γ) * (μ/lam) = μ / (γ*lam)
  have h_simplify : (1 / γ) * ((μ / lam) * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) +
      (ν n) * ‖yn - y‖ ^ 2 - μ * ‖yn1 - xn1 - y + x‖ ^ 2 - (ν n) * ‖yn1 - yn‖ ^ 2) =
      (1 / (γ * lam)) * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + (ν n) * lam) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - (ν n) * lam * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * lam * ‖yn1 - xn1 - y + x‖ ^ 2) := by
    field_simp [hγpos.ne', hlampos.ne']
    ring
  rw [h_simplify] at h_step1
  -- Step 7: Clean up using the set definitions
  dsimp [γ, lam, yn1, xn1, yn, xn] at h_step1 ⊢
  have hden_pos : (μ + ν n) * (α n + β) > 0 := by positivity
  have hden_pos' : (ν n + μ) * (α n + β) > 0 := by positivity
  -- Clear denominators (positive, so direction preserved)
  field_simp [hden_pos.ne', hden_pos'.ne'] at h_step1 ⊢
  nlinarith

/-- Lemma 4.3(c): Multiply (a) by α_n·μ, (b) by β·(μ+ν_n), add, and simplify.
    This is purely algebraic from (a)+(b). -/
private lemma lemma_4_3_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (n : ℕ) :
    α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
    α n * μ * ‖alg.x n - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y n - y‖ ^ 2 -
    α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 -
    β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
    β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
    β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
  have ha := lemma_4_3_a hyp x y hα_nonneg hν_nonneg alg hine n
  have hb := lemma_4_3_b hyp x y hα_nonneg hν_nonneg alg hine n
  have hμpos : μ > 0 := hyp.mu_pos
  have hβpos : β > 0 := hyp.beta_pos
  have hαn_nonneg : α n ≥ 0 := hα_nonneg n
  have hνn_nonneg : ν n ≥ 0 := hν_nonneg n
  have h_den_pos : α n + β > 0 := by nlinarith
  -- Multiply (a) by α_n·μ ≥ 0
  have ha_mul : α n * μ * ‖alg.x (n+1) - x‖ ^ 2 ≤
      ((α n * μ) / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
        α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ α n * μ := mul_nonneg hαn_nonneg (by linarith)
    have h_mul := mul_le_mul_of_nonneg_left ha h_nonneg
    -- Rewrite from ha: αn*μ * ((1/(αn+β)) * ...) = (αn*μ/(αn+β)) * ...
    have h_eq : α n * μ * ((1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
        α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2)) =
        ((α n * μ) / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
          α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) := by
      ring
    rw [h_eq] at h_mul
    exact h_mul
  -- Multiply (b) by β·(μ+ν_n) ≥ 0.  Note: β·(μ+ν_n)/((μ+ν_n)(α_n+β)) = β/(α_n+β)
  have hb_mul : β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      (β / (α n + β)) * (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
        μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
        μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
        μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ β * (μ + ν n) := mul_nonneg (by linarith) (by nlinarith)
    have h_mul := mul_le_mul_of_nonneg_left hb h_nonneg
    have h_eq : β * (μ + ν n) * ((1 / ((μ + ν n) * (α n + β))) *
        (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
          μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
          μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
          μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2)) =
        (β / (α n + β)) * (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
          μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
          μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
          μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) := by
      have h_den_b_ne_zero : (μ + ν n) * (α n + β) ≠ 0 := by nlinarith
      field_simp [h_den_b_ne_zero]; try ring
    rw [h_eq] at h_mul
    exact h_mul
  -- Add the two multiplied inequalities
  have h_sum : α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      ((α n * μ) / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
        α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) +
      (β / (α n + β)) * (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
        μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
        μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
        μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) := by nlinarith
  -- The RHS simplifies algebraically to the target RHS
  have h_simplify : ((α n * μ) / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
      α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) +
    (β / (α n + β)) * (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
      μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
      μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
      μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) =
    α n * μ * ‖alg.x n - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y n - y‖ ^ 2 -
    α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 -
    β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
    β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
    β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
    have h_den_ne_zero : α n + β ≠ 0 := by nlinarith
    field_simp [h_den_ne_zero]
    ring
  rw [h_simplify] at h_sum
  exact h_sum

/-- Proposition 4.5: Asymptotic convergence properties of the CA² algorithm
    in the quadratic Hilbert-space case.

The proof uses Lemma 4.3(c) and a telescoping argument with correction terms C_n
from H47 to show A_n converges and B_n → 0, from which both claims follow.

See the paper (Attouch, Redont, Soubeyran 2007) for the full proof.
-/
theorem proposition_4_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (h41toh46 : H41toH46 H f g β μ)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (h47 : H47 α ν)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (x y : H) (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
                   (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) :
    ((Tendsto (fun n => alg.y n - alg.x n) atTop (𝓝 (y - x))) ∧
     (Tendsto (fun n => alg.x (n+1) - alg.x n) atTop (𝓝 (0 : H))) ∧
     (Tendsto (fun n => alg.y (n+1) - alg.y n) atTop (𝓝 (0 : H)))) ∧
    ((∃ lx : ℝ, Tendsto (fun n => ‖alg.x (n+1) - x‖) atTop (𝓝 lx)) ∧
     (∃ ly : ℝ, Tendsto (fun n => ‖alg.y (n+1) - y‖) atTop (𝓝 ly))) :=
by
  have hβpos : β > 0 := h41toh46.beta_pos
  have hμpos : μ > 0 := h41toh46.mu_pos
  rcases h47 with ⟨h_summable_alpha, h_summable_nu⟩
  -- Step 0: Boundedness. From Lemma 4.3(a)+(b), dropping nonnegative subtracted terms,
  -- we get a nonincreasing max bound. Let M be the initial max.
  set M : ℝ := max (‖alg.x 0 - x‖ ^ 2) (‖alg.y 0 - y‖ ^ 2) with hM_def
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]
    have hx0 : 0 ≤ ‖alg.x 0 - x‖ ^ 2 := pow_two_nonneg _
    have hy0 : 0 ≤ ‖alg.y 0 - y‖ ^ 2 := pow_two_nonneg _
    exact le_max_iff.mpr (Or.inl hx0)
  -- Lemma: convex combination a·p + b·q ≤ max(a,b) when p+q=1, p,q ≥ 0
  have h_conv_bound : ∀ (a b p q : ℝ), 0 ≤ p → 0 ≤ q → p + q = 1 → p * a + q * b ≤ max a b := by
    intro a b p q hp hq hsum
    by_cases h : a ≤ b
    · have h1 : p * a + q * b ≤ p * b + q * b := by nlinarith
      have h2 : p * b + q * b = b := by
        calc
          p * b + q * b = (p + q) * b := by ring
          _ = 1 * b := by rw [hsum]
          _ = b := by simp
      have h3 : b ≤ max a b := le_max_right _ _
      linarith
    · have h' : b ≤ a := by linarith
      have h1 : p * a + q * b ≤ p * a + q * a := by nlinarith
      have h2 : p * a + q * a = a := by
        calc
          p * a + q * a = (p + q) * a := by ring
          _ = 1 * a := by rw [hsum]
          _ = a := by simp
      have h3 : a ≤ max a b := le_max_left _ _
      linarith
  -- Show: ∀ n, max(‖x_{n+1}-x‖², ‖y_{n+1}-y‖²) ≤ max(‖x_n-x‖², ‖y_n-y‖²)
  have h_max_nonincr : ∀ n : ℕ, max (‖alg.x (n+1) - x‖ ^ 2) (‖alg.y (n+1) - y‖ ^ 2) ≤
      max (‖alg.x n - x‖ ^ 2) (‖alg.y n - y‖ ^ 2) := by
    intro n
    have ha := lemma_4_3_a h41toh46 x y hα_nonneg hν_nonneg alg hine n
    have hb := lemma_4_3_b h41toh46 x y hα_nonneg hν_nonneg alg hine n
    have hden_pos : α n + β > 0 := by linarith [hα_nonneg n]
    have hp_nonneg : 0 ≤ α n / (α n + β) := div_nonneg (hα_nonneg n) (by linarith)
    have hq_nonneg : 0 ≤ β / (α n + β) := div_nonneg (by linarith) (by linarith)
    have hpq_sum : α n / (α n + β) + β / (α n + β) = 1 := by field_simp [hden_pos.ne']
    -- From (a): drop nonnegative subtracted terms
    have hx_bound : ‖alg.x (n+1) - x‖ ^ 2 ≤
        (α n / (α n + β)) * ‖alg.x n - x‖ ^ 2 + (β / (α n + β)) * ‖alg.y n - y‖ ^ 2 := by
      have htemp : 0 ≤ α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 + β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 := by
        have h1 : 0 ≤ α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 := mul_nonneg (hα_nonneg n) (sq_nonneg _)
        have h2 : 0 ≤ β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
        exact add_nonneg h1 h2
      have ha' : ‖alg.x (n+1) - x‖ ^ 2 ≤
          (1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2) := by
        have hfactor_nonneg : 0 ≤ 1 / (α n + β) := div_nonneg (by norm_num) (by linarith)
        have h_drop : (1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2 -
            α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) ≤
            (1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left ?_ hfactor_nonneg
          linarith
        linarith
      have h_eq : (1 / (α n + β)) * (α n * ‖alg.x n - x‖ ^ 2 + β * ‖alg.y n - y‖ ^ 2) =
          (α n / (α n + β)) * ‖alg.x n - x‖ ^ 2 + (β / (α n + β)) * ‖alg.y n - y‖ ^ 2 := by ring
      rw [h_eq] at ha'
      exact ha'
    have hx_bound_max : ‖alg.x (n+1) - x‖ ^ 2 ≤ max (‖alg.x n - x‖ ^ 2) (‖alg.y n - y‖ ^ 2) :=
      le_trans hx_bound (h_conv_bound _ _ _ _ hp_nonneg hq_nonneg hpq_sum)
    -- From (b): drop nonnegative subtracted terms similarly
    have hden_b_pos : (μ + ν n) * (α n + β) > 0 := by
      have h1 : μ + ν n > 0 := by linarith [hν_nonneg n]
      have h2 : α n + β > 0 := by linarith [hα_nonneg n]
      exact mul_pos h1 h2
    have hp'_nonneg : 0 ≤ (μ * α n) / ((μ + ν n) * (α n + β)) :=
      div_nonneg (mul_nonneg (by linarith) (hα_nonneg n)) (by linarith)
    have hq'_nonneg : 0 ≤ (μ * β + ν n * (α n + β)) / ((μ + ν n) * (α n + β)) :=
      div_nonneg (add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (hν_nonneg n) (by linarith))) (by linarith)
    have hp'q'_sum : (μ * α n) / ((μ + ν n) * (α n + β)) + (μ * β + ν n * (α n + β)) / ((μ + ν n) * (α n + β)) = 1 := by
      rw [← add_div]
      have hden_pos : (μ + ν n) * (α n + β) > 0 := by positivity
      exact (div_eq_one_iff_eq hden_pos.ne').mpr (by ring)
    have hy_bound : ‖alg.y (n+1) - y‖ ^ 2 ≤
        ((μ * α n) / ((μ + ν n) * (α n + β))) * ‖alg.x n - x‖ ^ 2 +
        ((μ * β + ν n * (α n + β)) / ((μ + ν n) * (α n + β))) * ‖alg.y n - y‖ ^ 2 := by
      have htemp : 0 ≤ μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 +
          ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 +
          μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 +
          μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
        repeat' apply add_nonneg
        · exact mul_nonneg (mul_nonneg (by linarith) (hα_nonneg n)) (sq_nonneg _)
        · exact mul_nonneg (mul_nonneg (hν_nonneg n) (by linarith)) (sq_nonneg _)
        · exact mul_nonneg (mul_pos hμpos hβpos).le (sq_nonneg _)
        · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
      have hfactor_nonneg' : 0 ≤ 1 / ((μ + ν n) * (α n + β)) :=
        div_nonneg (by norm_num) (by linarith)
      have hb' : ‖alg.y (n+1) - y‖ ^ 2 ≤
          (1 / ((μ + ν n) * (α n + β))) * (μ * α n * ‖alg.x n - x‖ ^ 2 +
          (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2) := by
        have h_drop : (1 / ((μ + ν n) * (α n + β))) *
            (μ * α n * ‖alg.x n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2 -
            μ * α n * ‖alg.x (n+1) - alg.x n‖ ^ 2 - ν n * (α n + β) * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
            μ * β * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
            μ * (α n + β) * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) ≤
            (1 / ((μ + ν n) * (α n + β))) * (μ * α n * ‖alg.x n - x‖ ^ 2 +
            (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left ?_ hfactor_nonneg'
          linarith
        linarith
      have h_eq : (1 / ((μ + ν n) * (α n + β))) * (μ * α n * ‖alg.x n - x‖ ^ 2 +
          (μ * β + ν n * (α n + β)) * ‖alg.y n - y‖ ^ 2) =
          ((μ * α n) / ((μ + ν n) * (α n + β))) * ‖alg.x n - x‖ ^ 2 +
          ((μ * β + ν n * (α n + β)) / ((μ + ν n) * (α n + β))) * ‖alg.y n - y‖ ^ 2 := by ring
      rw [h_eq] at hb'
      exact hb'
    have hy_bound_max : ‖alg.y (n+1) - y‖ ^ 2 ≤ max (‖alg.x n - x‖ ^ 2) (‖alg.y n - y‖ ^ 2) :=
      le_trans hy_bound (h_conv_bound _ _ _ _ hp'_nonneg hq'_nonneg hp'q'_sum)
    exact max_le hx_bound_max hy_bound_max
  -- By induction, max is bounded by M for all n
  have h_bounded : ∀ n : ℕ, max (‖alg.x n - x‖ ^ 2) (‖alg.y n - y‖ ^ 2) ≤ M := by
    intro n
    induction' n with k ih
    · rw [hM_def]
    · exact le_trans (h_max_nonincr k) ih
  have hx_sq_bdd : ∀ n : ℕ, ‖alg.x n - x‖ ^ 2 ≤ M := by
    intro n; exact le_trans (le_max_left _ _) (h_bounded n)
  have hy_sq_bdd : ∀ n : ℕ, ‖alg.y n - y‖ ^ 2 ≤ M := by
    intro n; exact le_trans (le_max_right _ _) (h_bounded n)
  have hx_sq_bdd_succ : ∀ n : ℕ, ‖alg.x (n+1) - x‖ ^ 2 ≤ M := by
    intro n; exact hx_sq_bdd (n+1)
  have hy_sq_bdd_succ : ∀ n : ℕ, ‖alg.y (n+1) - y‖ ^ 2 ≤ M := by
    intro n; exact hy_sq_bdd (n+1)
  -- Step 1: Define A_n, B_n
  set A : ℕ → ℝ := fun n => α n * μ * ‖alg.x n - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y n - y‖ ^ 2 with hA_def
  set B : ℕ → ℝ := fun n => α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 + β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 +
      β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 + β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2
      with hB_def
  have hB_nonneg : ∀ n, 0 ≤ B n := by
    intro n; rw [hB_def]; repeat' apply add_nonneg
    · exact mul_nonneg (mul_nonneg (hα_nonneg n) (by linarith)) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg (by linarith) (hν_nonneg n)) (sq_nonneg _)
    · exact mul_nonneg (mul_pos hβpos hμpos).le (sq_nonneg _)
    · exact mul_nonneg (mul_pos hβpos hμpos).le (sq_nonneg _)
  -- Lemma 4.3(c) gives: B_n ≤ A_n - (α_n·μ·‖x_{n+1}-x‖² + β(μ+ν_n)·‖y_{n+1}-y‖²)
  have h_lemma_c_ineq : ∀ n : ℕ, B n ≤ A n - (α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2) := by
    intro n
    have hc := lemma_4_3_c h41toh46 x y hα_nonneg hν_nonneg alg hine n
    rw [hA_def, hB_def]
    linarith
  -- Step 2: Algebraic identity linking the brace to A_{n+1}
  -- A_{n+1} - μ(α_{n+1}-α_n)·‖x_{n+1}-x‖² - β(ν_{n+1}-ν_n)·‖y_{n+1}-y‖²
  --   = α_n·μ·‖x_{n+1}-x‖² + β(μ+ν_n)·‖y_{n+1}-y‖²
  have h_brace_identity : ∀ n : ℕ, α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 =
      A (n+1) - μ * (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 -
      β * (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 := by
    intro n
    rw [hA_def]
    ring
  -- Substituting the identity: B_n ≤ A_n - A_{n+1} + μ(α_{n+1}-α_n)·‖x_{n+1}-x‖² + β(ν_{n+1}-ν_n)·‖y_{n+1}-y‖²
  have h_telescope_ineq : ∀ n : ℕ, B n ≤ A n - A (n+1) +
      μ * (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 +
      β * (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 := by
    intro n
    have hbase := h_lemma_c_ineq n
    rw [h_brace_identity n] at hbase
    linarith
  -- Since (a-b) ≤ (a-b)⁺ and ‖x_{n+1}-x‖² ≤ M, we bound the error term:
  -- μ(α_{n+1}-α_n)·‖x_{n+1}-x‖² ≤ μ·(α_{n+1}-α_n)⁺·M
  have h_pos_part_bound : ∀ (a b u : ℝ), u ≥ 0 → (a - b) * u ≤ positivePart (a - b) * u := by
    intro a b u hu
    have hle : a - b ≤ positivePart (a - b) := by
      dsimp [positivePart]
      have : a - b ≤ max (a - b) 0 := le_max_left _ _
      exact this
    nlinarith
  have h_pos_part_nonneg : ∀ a : ℝ, 0 ≤ positivePart a := by
    intro a; dsimp [positivePart]; exact le_max_right _ _
  have h_correction_bound : ∀ n : ℕ,
      μ * (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 +
      β * (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
      (μ * positivePart (α (n+1) - α n) + β * positivePart (ν (n+1) - ν n)) * M := by
    intro n
    have hx_sq : ‖alg.x (n+1) - x‖ ^ 2 ≤ M := hx_sq_bdd_succ n
    have hy_sq : ‖alg.y (n+1) - y‖ ^ 2 ≤ M := hy_sq_bdd_succ n
    have h_nonneg_x : 0 ≤ ‖alg.x (n+1) - x‖ ^ 2 := pow_two_nonneg _
    have h_nonneg_y : 0 ≤ ‖alg.y (n+1) - y‖ ^ 2 := pow_two_nonneg _
    have hα_bound : μ * (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 ≤
        μ * positivePart (α (n+1) - α n) * M := by
      have h_nonneg_pp_α : 0 ≤ positivePart (α (n+1) - α n) := h_pos_part_nonneg _
      have h1 : (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 ≤
          positivePart (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 :=
        h_pos_part_bound (α (n+1)) (α n) (‖alg.x (n+1) - x‖ ^ 2) h_nonneg_x
      have h2 : positivePart (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 ≤
          positivePart (α (n+1) - α n) * M :=
        mul_le_mul_of_nonneg_left hx_sq h_nonneg_pp_α
      calc
        μ * (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 = μ * ((α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2) := by ring
        _ ≤ μ * (positivePart (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = μ * positivePart (α (n+1) - α n) * ‖alg.x (n+1) - x‖ ^ 2 := by ring
        _ ≤ μ * positivePart (α (n+1) - α n) * M :=
          mul_le_mul_of_nonneg_left hx_sq (mul_nonneg (by linarith) h_nonneg_pp_α)
    have hν_bound : β * (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
        β * positivePart (ν (n+1) - ν n) * M := by
      have h_nonneg_pp_ν : 0 ≤ positivePart (ν (n+1) - ν n) := h_pos_part_nonneg _
      have h1 : (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
          positivePart (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 :=
        h_pos_part_bound (ν (n+1)) (ν n) (‖alg.y (n+1) - y‖ ^ 2) h_nonneg_y
      have h2 : positivePart (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
          positivePart (ν (n+1) - ν n) * M :=
        mul_le_mul_of_nonneg_left hy_sq h_nonneg_pp_ν
      calc
        β * (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 = β * ((ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2) := by ring
        _ ≤ β * (positivePart (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = β * positivePart (ν (n+1) - ν n) * ‖alg.y (n+1) - y‖ ^ 2 := by ring
        _ ≤ β * positivePart (ν (n+1) - ν n) * M :=
          mul_le_mul_of_nonneg_left hy_sq (mul_nonneg (by linarith) h_nonneg_pp_ν)
    linarith
  -- Define C_n for n≥1: C_n = [μ(α_n-α_{n-1})⁺ + β(ν_n-ν_{n-1})⁺]·M
  -- Then C_{n+1} = [μ(α_{n+1}-α_n)⁺ + β(ν_{n+1}-ν_n)⁺]·M
  set C : ℕ → ℝ := fun n =>
    match n with
    | 0 => 0
    | n+1 => (μ * positivePart (α (n+1) - α n) + β * positivePart (ν (n+1) - ν n)) * M
    with hC_def
  have hC_nonneg : ∀ n, 0 ≤ C n := by
    intro n
    rcases n with (rfl | n)
    · rfl
    · rw [hC_def]
      have h_nonneg_pp_α_n : 0 ≤ positivePart (α (n+1) - α n) := h_pos_part_nonneg _
      have h_nonneg_pp_ν_n : 0 ≤ positivePart (ν (n+1) - ν n) := h_pos_part_nonneg _
      apply mul_nonneg
      · nlinarith
      · exact hM_nonneg
  have hC_succ : ∀ n : ℕ, C (n+1) = (μ * positivePart (α (n+1) - α n) + β * positivePart (ν (n+1) - ν n)) * M := by
    intro n; rfl
  -- Key inequality: B_n ≤ A_n - A_{n+1} + C_{n+1}
  have h_key_ineq : ∀ n : ℕ, B n ≤ A n - A (n+1) + C (n+1) := by
    intro n
    rw [hC_succ n]
    have h1 := h_telescope_ineq n
    have h2 := h_correction_bound n
    linarith
  -- Rearrange: 0 ≤ B_n ≤ (A_n - Σ_{k=0}^{n-1} C_{k+1}) - (A_{n+1} - Σ_{k=0}^n C_{k+1})
  -- Define D_n = A_n - Σ_{k=0}^{n-1} C_{k+1} (for n≥0, empty sum = 0)
  set D : ℕ → ℝ := fun n => A n - (Finset.sum (Finset.range n) fun k => C (k+1)) with hD_def
  have hD_nonincr : ∀ n, D (n+1) ≤ D n := by
    intro n
    dsimp [D]
    have hsum_n1 : (Finset.sum (Finset.range (n+1)) fun k => C (k+1)) =
        (Finset.sum (Finset.range n) fun k => C (k+1)) + C (n+1) := by
      rw [Finset.sum_range_succ]
    rw [hsum_n1]
    have h := h_key_ineq n
    have hB : 0 ≤ B n := hB_nonneg n
    linarith
  -- Show Σ_{k} C_{k+1} converges (from H47)
  have h_summable_C : Summable fun n : ℕ => C (n+1) := by
    have h_summable_alpha' : Summable fun n : ℕ => μ * positivePart (α (n+1) - α n) * M := by
      have h1 : Summable (fun n : ℕ => positivePart (α (n+1) - α n) * M) :=
        h_summable_alpha.mul_right M
      have h2 : Summable (fun n : ℕ => μ * (positivePart (α (n+1) - α n) * M)) :=
        h1.mul_left μ
      simpa [mul_assoc] using h2
    have h_summable_nu' : Summable fun n : ℕ => β * positivePart (ν (n+1) - ν n) * M := by
      have h1 : Summable (fun n : ℕ => positivePart (ν (n+1) - ν n) * M) :=
        h_summable_nu.mul_right M
      have h2 : Summable (fun n : ℕ => β * (positivePart (ν (n+1) - ν n) * M)) :=
        h1.mul_left β
      simpa [mul_assoc] using h2
    have hsum : Summable (fun n : ℕ => (μ * positivePart (α (n+1) - α n) + β * positivePart (ν (n+1) - ν n)) * M) := by
      have h_eq : (fun n : ℕ => (μ * positivePart (α (n+1) - α n) + β * positivePart (ν (n+1) - ν n)) * M) =
                 (fun n => μ * positivePart (α (n+1) - α n) * M) +
                 (fun n => β * positivePart (ν (n+1) - ν n) * M) := by
        ext n; simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
      rw [h_eq]
      exact Summable.add h_summable_alpha' h_summable_nu'
    simpa [hC_def] using hsum
  rcases h_summable_C with ⟨SC, hSC⟩
  -- hSC : HasSum (fun n : ℕ => C (n+1)) SC
  -- Hence partial sums of C_{k+1} tend to SC and partial sums ≤ SC (since terms ≥ 0)
  -- Use H47 directly to get bounds: extract the total sums from Summable
  have h_summable_alpha_save := h_summable_alpha
  have h_summable_nu_save := h_summable_nu
  obtain ⟨Sα, hSα⟩ := h_summable_alpha
  obtain ⟨Sν, hSν⟩ := h_summable_nu
  -- hSα : HasSum (fun n => positivePart (α (n+1) - α n)) Sα
  -- hSν : HasSum (fun n => positivePart (ν (n+1) - ν n)) Sν
  -- Total sum of C_{k+1}: SC = (μ * Sα + β * Sν) * M
  set SC : ℝ := (μ * Sα + β * Sν) * M with hSC_def
  have hSC_nonneg : 0 ≤ SC := by
    rw [hSC_def]
    have hSα_nonneg : 0 ≤ Sα := by
      rw [← hSα.tsum_eq]
      exact tsum_nonneg (fun n => h_pos_part_nonneg (α (n+1) - α n))
    have hSν_nonneg : 0 ≤ Sν := by
      rw [← hSν.tsum_eq]
      exact tsum_nonneg (fun n => h_pos_part_nonneg (ν (n+1) - ν n))
    have h_nonneg_sum : 0 ≤ μ * Sα + β * Sν := by nlinarith
    nlinarith
  -- Partial sums of C_{k+1} ≤ SC (since all terms nonnegative)
  have h_partial_C_le_SC : ∀ n, (Finset.sum (Finset.range n) fun k => C (k+1)) ≤ SC := by
    intro n
    calc
      (Finset.sum (Finset.range n) fun k => C (k+1))
          = (Finset.sum (Finset.range n) fun k =>
              (μ * positivePart (α (k+1) - α k) + β * positivePart (ν (k+1) - ν k)) * M) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        simp [C, hC_def]
      _ = M * (μ * (Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k)) +
               β * (Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k))) := by
        calc
          (Finset.sum (Finset.range n) fun k => (μ * positivePart (α (k+1) - α k) + β * positivePart (ν (k+1) - ν k)) * M)
            = (Finset.sum (Finset.range n) fun k => (μ * positivePart (α (k+1) - α k) * M + β * positivePart (ν (k+1) - ν k) * M)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
          _ = (Finset.sum (Finset.range n) fun k => μ * positivePart (α (k+1) - α k) * M) +
              (Finset.sum (Finset.range n) fun k => β * positivePart (ν (k+1) - ν k) * M) := by
            simp [Finset.sum_add_distrib]
          _ = (μ * M) * (Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k)) +
              (β * M) * (Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k)) := by
            simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
          _ = M * (μ * (Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k)) +
                   β * (Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k))) := by ring
      _ ≤ M * (μ * Sα + β * Sν) := by
        apply mul_le_mul_of_nonneg_left ?_ hM_nonneg
        have hSα_partial : (Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k)) ≤ Sα := by
          have h := h_summable_alpha_save.sum_le_tsum (Finset.range n) (fun k _ => h_pos_part_nonneg _)
          rwa [hSα.tsum_eq] at h
        have hSν_partial : (Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k)) ≤ Sν := by
          have h := h_summable_nu_save.sum_le_tsum (Finset.range n) (fun k _ => h_pos_part_nonneg _)
          rwa [hSν.tsum_eq] at h
        nlinarith
      _ = SC := by rw [hSC_def]; ring
  -- D_n = A_n - Σ_{k=0}^{n-1} C_{k+1} is decreasing and bounded below → converges
  have hD_bdd_below : ∀ n, D n ≥ -(SC) := by
    intro n
    dsimp [D]
    have hA_nonneg : 0 ≤ A n := by
      rw [hA_def]
      apply add_nonneg
      · exact mul_nonneg (mul_nonneg (hα_nonneg n) (by linarith)) (sq_nonneg _)
      · apply mul_nonneg (mul_nonneg (by linarith) (by nlinarith [hν_nonneg n])) (sq_nonneg _)
    linarith [h_partial_C_le_SC n, hA_nonneg]
  -- Antitone D → converges by monotone convergence theorem
  have hD_antitone : Antitone D := antitone_nat_of_succ_le hD_nonincr
  have hD_bdd_below_range : BddBelow (Set.range D) := by
    refine ⟨-(SC), ?_⟩
    rintro y ⟨n, rfl⟩
    exact hD_bdd_below n
  have hD_tendsto : Tendsto D atTop (𝓝 (⨅ n, D n)) :=
    tendsto_atTop_ciInf hD_antitone hD_bdd_below_range
  set LD := ⨅ n, D n with hLD_def
  -- We also need the convergence of partial sums of C_{k+1} to SC
  have hC_partial_tendsto : Tendsto (fun n : ℕ => Finset.sum (Finset.range n) fun k => C (k+1)) atTop (𝓝 SC) := by
    -- This follows from convergence of the positive part series
    -- Since C_{k+1} = (μ*(α_{k+1}-α_k)⁺ + β*(ν_{k+1}-ν_k)⁺)·M
    -- and both positive part series converge, their linear combination converges
    have hSα_tendsto : Tendsto (fun n : ℕ => Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k))
        atTop (𝓝 Sα) := hSα.tendsto_sum_nat
    have hSν_tendsto : Tendsto (fun n : ℕ => Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k))
        atTop (𝓝 Sν) := hSν.tendsto_sum_nat
    have h_sum_tendsto : Tendsto
        (fun n : ℕ => μ * (Finset.sum (Finset.range n) fun k => positivePart (α (k+1) - α k)) +
                      β * (Finset.sum (Finset.range n) fun k => positivePart (ν (k+1) - ν k)))
        atTop (𝓝 (μ * Sα + β * Sν)) := by
      exact Tendsto.add (Tendsto.const_mul μ hSα_tendsto) (Tendsto.const_mul β hSν_tendsto)
    have h_mul_tendsto : Tendsto (fun n : ℕ => M * (μ * (Finset.sum (Finset.range n) fun k =>
        positivePart (α (k+1) - α k)) + β * (Finset.sum (Finset.range n) fun k =>
        positivePart (ν (k+1) - ν k)))) atTop (𝓝 (M * (μ * Sα + β * Sν))) :=
      Tendsto.const_mul M h_sum_tendsto
    -- Rewrite using the definition of C: C(k+1) = (μ*pp_α + β*pp_ν)*M
    have h_mul_tendsto' : Tendsto (fun n : ℕ => Finset.sum (Finset.range n) fun k => C (k+1))
        atTop (𝓝 SC) := by
      have h_eq : (fun n : ℕ => Finset.sum (Finset.range n) fun k => C (k+1)) =
                 (fun n : ℕ => M * (μ * (Finset.sum (Finset.range n) fun k =>
                   positivePart (α (k+1) - α k)) + β * (Finset.sum (Finset.range n) fun k =>
                   positivePart (ν (k+1) - ν k)))) := by
        ext n
        simp [C, Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
      rw [h_eq, hSC_def]
      simpa [mul_comm] using h_mul_tendsto
    exact h_mul_tendsto'
  -- A_n = D_n + Σ_{k<n} C_{k+1} → LD + SC
  have hA_tendsto : Tendsto A atTop (𝓝 (LD + SC)) := by
    have hA_eq : A = fun n => D n + (Finset.sum (Finset.range n) fun k => C (k+1)) := by
      ext n; dsimp [D]; ring
    rw [hA_eq]
    exact Tendsto.add hD_tendsto hC_partial_tendsto
  -- B_n → 0 via squeeze: 0 ≤ B_n ≤ D_n - D_{n+1} → 0
  have h_diff_D_tendsto_zero : Tendsto (fun n => D n - D (n+1)) atTop (𝓝 0) := by
    have hD_succ_tendsto : Tendsto (fun n => D (n+1)) atTop (𝓝 LD) := by
      have : (fun n => D (n+1)) = D ∘ (fun n => n+1) := rfl
      rw [this]
      exact hD_tendsto.comp (tendsto_add_atTop_nat 1)
    have h := Tendsto.sub hD_tendsto hD_succ_tendsto
    simpa using h
  have hB_tendsto_zero : Tendsto B atTop (𝓝 0) := by
    refine squeeze_zero (fun n => hB_nonneg n) (fun n => ?_) h_diff_D_tendsto_zero
    have h_eq : D n - D (n+1) = A n - A (n+1) + C (n+1) := by
      dsimp [D]
      rw [Finset.sum_range_succ]
      ring
    rw [h_eq]
    exact h_key_ineq n
  -- Step 4: From B_n → 0, extract convergence of individual terms
  -- Since β>0, μ>0, the terms with coefficient β·μ → 0
  have hbeta_mu_pos : β * μ > 0 := mul_pos hβpos hμpos
  have h_term3_tendsto_sq : Tendsto (fun n => ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) atTop (𝓝 0) := by
    have h_nonneg : ∀ n, 0 ≤ β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 := by
      intro n; positivity
    have h_le : ∀ n, β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 ≤ B n := by
      intro n; rw [hB_def]
      have h1 : 0 ≤ α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 :=
        mul_nonneg (mul_nonneg (hα_nonneg n) (by linarith)) (sq_nonneg _)
      have h2 : 0 ≤ β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) (hν_nonneg n)) (sq_nonneg _)
      have h4 : 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
        positivity
      nlinarith
    have h_sq_scaled_tendsto : Tendsto (fun n => β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le hB_tendsto_zero
    -- Cancel β·μ > 0
    have h_div : (fun n => ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) =
        (fun n => (β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2) / (β * μ)) := by
      ext n; field_simp [hbeta_mu_pos.ne']
    rw [h_div]
    have h_temp := h_sq_scaled_tendsto.div_const (β * μ)
    simpa [zero_div] using h_temp
  have h_term4_tendsto_sq : Tendsto (fun n => ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) atTop (𝓝 0) := by
    have h_nonneg : ∀ n, 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
      intro n; positivity
    have h_le : ∀ n, β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 ≤ B n := by
      intro n; rw [hB_def]
      have h1 : 0 ≤ α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 :=
        mul_nonneg (mul_nonneg (hα_nonneg n) (by linarith)) (sq_nonneg _)
      have h2 : 0 ≤ β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) (hν_nonneg n)) (sq_nonneg _)
      have h4 : 0 ≤ β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2 := by
        positivity
      nlinarith
    have h_sq_scaled_tendsto : Tendsto (fun n => β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero h_nonneg h_le hB_tendsto_zero
    have h_div : (fun n => ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) =
        (fun n => (β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2) / (β * μ)) := by
      ext n; field_simp [hbeta_mu_pos.ne']
    rw [h_div]
    have h_temp := h_sq_scaled_tendsto.div_const (β * μ)
    simpa [zero_div] using h_temp
  -- From ‖·‖² → 0, derive ‖·‖ → 0 using continuity of sqrt at 0
  have h_norm_sq_imp_norm {a : ℕ → H} (h_sq : Tendsto (fun n => ‖a n‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
      Tendsto (fun n => ‖a n‖) atTop (𝓝 (0 : ℝ)) := by
    have h_sqrt_cont : ContinuousAt Real.sqrt (0 : ℝ) :=
      Real.continuous_sqrt.continuousAt
    have h_sqrt_tendsto : Tendsto (fun n => Real.sqrt (‖a n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      h_sqrt_cont.tendsto.comp h_sq
    have h_sqrt_zero : Real.sqrt (0 : ℝ) = 0 := by norm_num
    rw [h_sqrt_zero] at h_sqrt_tendsto
    have h_eq : (fun n => Real.sqrt (‖a n‖ ^ 2)) = (fun n => ‖a n‖) := by
      ext n; simp [Real.sqrt_sq (norm_nonneg _)]
    rw [h_eq] at h_sqrt_tendsto
    exact h_sqrt_tendsto
  have h_term3_tendsto : Tendsto (fun n => ‖alg.y n - alg.x (n+1) - y + x‖) atTop (𝓝 0) :=
    h_norm_sq_imp_norm h_term3_tendsto_sq
  have h_term4_tendsto : Tendsto (fun n => ‖alg.y (n+1) - alg.x (n+1) - y + x‖) atTop (𝓝 0) :=
    h_norm_sq_imp_norm h_term4_tendsto_sq
  -- Part (i): From the norm convergences to vector convergences
  -- Use the fact that dist(a, 0) = ‖a‖ in a normed group
  have h_term3_vec_tendsto : Tendsto (fun n => alg.y n - alg.x (n+1) - (y - x)) atTop (𝓝 (0 : H)) := by
    rw [Metric.tendsto_nhds]
    rw [Metric.tendsto_nhds] at h_term3_tendsto
    intro ε hε
    have h_event := h_term3_tendsto ε hε
    refine h_event.mono fun n hn => ?_
    simpa [dist_eq_norm, sub_add] using hn
  have h_term4_vec_tendsto : Tendsto (fun n => alg.y (n+1) - alg.x (n+1) - (y - x)) atTop (𝓝 (0 : H)) := by
    rw [Metric.tendsto_nhds]
    rw [Metric.tendsto_nhds] at h_term4_tendsto
    intro ε hε
    have h_event := h_term4_tendsto ε hε
    refine h_event.mono fun n hn => ?_
    simpa [dist_eq_norm, sub_add] using hn
  -- Shifted h_term3: y_{n+1} - x_{n+2} → y - x (for the x-difference argument)
  have h_term3_shift_vec : Tendsto (fun n => alg.y (n+1) - alg.x (n+2) - (y - x)) atTop (𝓝 (0 : H)) := by
    have : (fun n => alg.y (n+1) - alg.x (n+2) - (y - x)) =
           (fun n => alg.y n - alg.x (n+1) - (y - x)) ∘ (fun n => n+1) := by
      ext n; simp
    rw [this]
    exact h_term3_vec_tendsto.comp (tendsto_add_atTop_nat 1)
  -- x_{n+2} - x_{n+1} = (y_{n+1} - x_{n+1}) - (y_{n+1} - x_{n+2}) → 0
  have h_xdiff_succ : Tendsto (fun n => alg.x (n+2) - alg.x (n+1)) atTop (𝓝 (0 : H)) := by
    have h_eq : (fun n => alg.x (n+2) - alg.x (n+1)) =
               (fun n => (alg.y (n+1) - alg.x (n+1) - (y - x)) -
                         (alg.y (n+1) - alg.x (n+2) - (y - x))) := by
      ext n; abel
    rw [h_eq]
    simpa [sub_self] using Tendsto.sub h_term4_vec_tendsto h_term3_shift_vec
  -- With the index shift, x_{n+1} - x_n → 0
  have h_xdiff_tendsto : Tendsto (fun n => alg.x (n+1) - alg.x n) atTop (𝓝 (0 : H)) := by
    -- h_xdiff_succ: alg.x(n+2) - alg.x(n+1) → 0, which is the same sequence shifted by 1
    set g := fun n : ℕ => alg.x (n+1) - alg.x n with hg
    have h_comp : (fun n => alg.x (n+2) - alg.x (n+1)) = g ∘ (fun n : ℕ => n+1) := by
      ext n; simp [g]
    rw [h_comp] at h_xdiff_succ
    -- Now h_xdiff_succ: Tendsto (g ∘ (n ↦ n+1)) atTop (𝓝 0)
    -- Use map_add_atTop_eq_nat: map (n ↦ n+1) atTop = atTop
    have h_map_succ : Filter.map (fun n : ℕ => n+1) Filter.atTop = Filter.atTop :=
      map_add_atTop_eq_nat 1
    rw [← Filter.tendsto_map'_iff, h_map_succ] at h_xdiff_succ
    rw [hg]
    exact h_xdiff_succ
  -- y_{n+1} - y_n = (y_{n+1} - x_{n+1}) - (y_n - x_{n+1}) → 0
  have h_ydiff_tendsto : Tendsto (fun n => alg.y (n+1) - alg.y n) atTop (𝓝 (0 : H)) := by
    have h_eq : (fun n => alg.y (n+1) - alg.y n) =
               (fun n => (alg.y (n+1) - alg.x (n+1) - (y - x)) -
                         (alg.y n - alg.x (n+1) - (y - x))) := by
      ext n; abel
    rw [h_eq]
    simpa [sub_self] using Tendsto.sub h_term4_vec_tendsto h_term3_vec_tendsto
  -- y_n - x_n → y - x: from y_n - x_n = (y_n - x_{n+1}) + (x_{n+1} - x_n)
  have h_yn_xn_tendsto : Tendsto (fun n => alg.y n - alg.x n) atTop (𝓝 (y - x)) := by
    have h_eq : (fun n => alg.y n - alg.x n) =
               (fun n => (alg.y n - alg.x (n+1) - (y - x)) + (y - x) + (alg.x (n+1) - alg.x n)) := by
      ext n; abel
    rw [h_eq]
    have h1 := Tendsto.add h_term3_vec_tendsto (tendsto_const_nhds (x := y - x))
    simpa [sub_add_cancel] using Tendsto.add h1 h_xdiff_tendsto
  -- Part (ii): Convergence of norms
  -- The paper writes x_n - x = (y_n - y) - (y_n - x_n - y + x) in the expression for A_n,
  -- yielding A_n = c_n·‖y_n - y‖² + correction terms with c_n = α_n·μ + β·(μ + ν_n).
  -- From H47 + nonnegativity, α_n, ν_n converge, giving c_n → limit > 0.
  -- Since A_n converges and correction terms → 0, we get ‖y_n - y‖² → limit, then ‖x_n - x‖.
  -- Part (ii): Convergence of norms (proof continues below)
  have h_conv_alpha : ∃ α_lim : ℝ, Tendsto α atTop (𝓝 α_lim) := by
    set f := fun n : ℕ => α (n+1) - α n with hf
    have hf_posPart_nonneg : ∀ n, 0 ≤ positivePart (f n) := fun n => h_pos_part_nonneg (f n)
    -- Upper bound for partial sums of positivePart(-f_n) using telescoping identity
    have h_negPart_bdd : ∀ n : ℕ, (Finset.sum (Finset.range n) fun k => positivePart (-f k)) ≤ α 0 + Sα := by
      intro n
      have h_telescope : (Finset.sum (Finset.range n) fun k => f k) = α n - α 0 := by
        rw [hf, Finset.sum_range_sub (fun n => α n)]
      have h_decomp : ∀ x : ℝ, x = positivePart x - positivePart (-x) := by
        intro x; unfold positivePart; by_cases hx : 0 ≤ x
        · have hneg_nonpos : -x ≤ 0 := by linarith
          simp [max_eq_left hx, max_eq_right hneg_nonpos]
        · have hx' : x ≤ 0 := by linarith
          have hneg_nonneg : 0 ≤ -x := by linarith
          simp [max_eq_right hx', max_eq_left hneg_nonneg]
      have h_eq_sum : (Finset.sum (Finset.range n) fun k => f k) =
          (Finset.sum (Finset.range n) fun k => positivePart (f k)) -
          (Finset.sum (Finset.range n) fun k => positivePart (-f k)) := by
        calc
          (Finset.sum (Finset.range n) fun k => f k)
              = (Finset.sum (Finset.range n) fun k => positivePart (f k) - positivePart (-f k)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact h_decomp (f k)
          _ = (Finset.sum (Finset.range n) fun k => positivePart (f k)) -
              (Finset.sum (Finset.range n) fun k => positivePart (-f k)) := by
            simp [Finset.sum_sub_distrib]
      have h_posPart_sum_le_Sα : (Finset.sum (Finset.range n) fun k => positivePart (f k)) ≤ Sα := by
        have h := h_summable_alpha_save.sum_le_tsum (Finset.range n) (fun k _ => hf_posPart_nonneg k)
        rwa [hSα.tsum_eq] at h
      rw [h_eq_sum] at h_telescope
      have h_nonneg_α_n : 0 ≤ α n := hα_nonneg n
      nlinarith
    have h_negPart_nonneg : ∀ n, 0 ≤ positivePart (-f n) := fun n => h_pos_part_nonneg _
    -- Summable of negative part via bounded partial sums
    have h_summable_negPart : Summable (fun n => positivePart (-f n)) :=
      summable_of_sum_range_le h_negPart_nonneg h_negPart_bdd
    -- Therefore f_n = f_n^+ - f_n^- is summable
    have hf_summable : Summable f := by
      have h_eq : f = fun n => positivePart (f n) - positivePart (-f n) := by
        ext n; unfold positivePart; by_cases hx : 0 ≤ f n
        · simp [hx]
        · have hx' : f n ≤ 0 := by linarith
          have hpos : 0 ≤ -f n := by linarith
          simp [hx, hx', hpos]
      rw [h_eq]
      exact Summable.sub h_summable_alpha_save h_summable_negPart
    -- α_n = α_0 + ∑_{k=0}^{n-1} f_k → α_0 + ∑' f_k
    set α_lim := α 0 + (∑' n, f n) with hα_lim_def
    refine ⟨α_lim, ?_⟩
    have hα_eq : α = fun n => α 0 + (Finset.sum (Finset.range n) fun k => f k) := by
      ext n
      rw [hf, Finset.sum_range_sub (fun n => α n)]
      ring
    rw [hα_lim_def, hα_eq]
    simpa [add_comm] using (hf_summable.hasSum.tendsto_sum_nat).add (tendsto_const_nhds (x := α 0))
  -- Same argument for ν_n
  have h_conv_nu : ∃ ν_lim : ℝ, Tendsto ν atTop (𝓝 ν_lim) := by
    set f := fun n : ℕ => ν (n+1) - ν n with hf
    have hf_posPart_nonneg : ∀ n, 0 ≤ positivePart (f n) := fun n => h_pos_part_nonneg (f n)
    have h_negPart_bdd : ∀ n : ℕ, (Finset.sum (Finset.range n) fun k => positivePart (-f k)) ≤ ν 0 + Sν := by
      intro n
      have h_telescope : (Finset.sum (Finset.range n) fun k => f k) = ν n - ν 0 := by
        rw [hf, Finset.sum_range_sub (fun n => ν n)]
      have h_decomp : ∀ x : ℝ, x = positivePart x - positivePart (-x) := by
        intro x; unfold positivePart; by_cases hx : 0 ≤ x
        · have hneg_nonpos : -x ≤ 0 := by linarith
          simp [max_eq_left hx, max_eq_right hneg_nonpos]
        · have hx' : x ≤ 0 := by linarith
          have hneg_nonneg : 0 ≤ -x := by linarith
          simp [max_eq_right hx', max_eq_left hneg_nonneg]
      have h_eq_sum : (Finset.sum (Finset.range n) fun k => f k) =
          (Finset.sum (Finset.range n) fun k => positivePart (f k)) -
          (Finset.sum (Finset.range n) fun k => positivePart (-f k)) := by
        calc
          (Finset.sum (Finset.range n) fun k => f k)
              = (Finset.sum (Finset.range n) fun k => positivePart (f k) - positivePart (-f k)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact h_decomp (f k)
          _ = (Finset.sum (Finset.range n) fun k => positivePart (f k)) -
              (Finset.sum (Finset.range n) fun k => positivePart (-f k)) := by
            simp [Finset.sum_sub_distrib]
      have h_posPart_sum_le_Sν : (Finset.sum (Finset.range n) fun k => positivePart (f k)) ≤ Sν := by
        have h := h_summable_nu_save.sum_le_tsum (Finset.range n) (fun k _ => hf_posPart_nonneg k)
        rwa [hSν.tsum_eq] at h
      rw [h_eq_sum] at h_telescope
      have h_nonneg_ν_n : 0 ≤ ν n := hν_nonneg n
      nlinarith
    have h_negPart_nonneg : ∀ n, 0 ≤ positivePart (-f n) := fun n => h_pos_part_nonneg _
    have h_summable_negPart : Summable (fun n => positivePart (-f n)) :=
      summable_of_sum_range_le h_negPart_nonneg h_negPart_bdd
    have hf_summable : Summable f := by
      have h_eq : f = fun n => positivePart (f n) - positivePart (-f n) := by
        ext n; unfold positivePart; by_cases hx : 0 ≤ f n
        · simp [hx]
        · have hx' : f n ≤ 0 := by linarith
          have hpos : 0 ≤ -f n := by linarith
          simp [hx, hx', hpos]
      rw [h_eq]
      exact Summable.sub h_summable_nu_save h_summable_negPart
    set ν_lim := ν 0 + (∑' n, f n) with hν_lim_def
    refine ⟨ν_lim, ?_⟩
    have hν_eq : ν = fun n => ν 0 + (Finset.sum (Finset.range n) fun k => f k) := by
      ext n
      rw [hf, Finset.sum_range_sub (fun n => ν n)]
      ring
    rw [hν_lim_def, hν_eq]
    simpa [add_comm] using (hf_summable.hasSum.tendsto_sum_nat).add (tendsto_const_nhds (x := ν 0))
  rcases h_conv_alpha with ⟨α_lim, hα_tendsto⟩
  rcases h_conv_nu with ⟨ν_lim, hν_tendsto⟩
  have h_alpha_lim_nonneg : 0 ≤ α_lim :=
    ge_of_tendsto hα_tendsto (Filter.eventually_atTop.mpr ⟨0, fun n _ => hα_nonneg n⟩)
  have h_nu_lim_nonneg : 0 ≤ ν_lim :=
    ge_of_tendsto hν_tendsto (Filter.eventually_atTop.mpr ⟨0, fun n _ => hν_nonneg n⟩)
  -- Coefficient c_n = α_n·μ + β·(μ + ν_n) → c_lim > 0
  set c : ℕ → ℝ := fun n => α n * μ + β * (μ + ν n) with hc_def
  set c_lim : ℝ := α_lim * μ + β * (μ + ν_lim) with hc_lim_def
  have hc_lim_pos : c_lim > 0 := by
    rw [hc_lim_def]
    have h1 : 0 ≤ α_lim * μ := mul_nonneg h_alpha_lim_nonneg (by linarith)
    have h2 : 0 < β * (μ + ν_lim) := by
      positivity
    nlinarith
  have hc_tendsto : Tendsto c atTop (𝓝 c_lim) := by
    dsimp [c, c_lim]
    have h1 : Tendsto (fun n => α n * μ) atTop (𝓝 (α_lim * μ)) :=
      Tendsto.mul_const μ hα_tendsto
    have h2 : Tendsto (fun n => β * (μ + ν n)) atTop (𝓝 (β * (μ + ν_lim))) := by
      have h_temp : Tendsto (fun n => μ + ν n) atTop (𝓝 (μ + ν_lim)) := by
        simpa [add_comm] using (tendsto_const_nhds (x := μ)).add hν_tendsto
      simpa [mul_add, add_comm] using Tendsto.const_mul β h_temp
    simpa [add_assoc] using Tendsto.add h1 h2
  -- Algebraic identity for A_n: expand ‖x_n - x‖² using x_n - x = (y_n - y) - (y_n - x_n - (y - x))
  have hA_identity : ∀ n, A n = c n * ‖alg.y n - y‖ ^ 2
      - 2 * α n * μ * inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))
      + α n * μ * ‖alg.y n - alg.x n - (y - x)‖ ^ 2 := by
    intro n
    dsimp [A, c]
    have hx_eq : alg.x n - x = (alg.y n - y) - (alg.y n - alg.x n - (y - x)) := by abel
    rw [hx_eq]
    have h_norm_expand : ‖(alg.y n - y) - (alg.y n - alg.x n - (y - x))‖ ^ 2 =
        ‖alg.y n - y‖ ^ 2 - 2 * inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))
        + ‖alg.y n - alg.x n - (y - x)‖ ^ 2 := by
      rw [norm_sub_sq_real]
    rw [h_norm_expand]
    ring
  -- The correction term r_n → 0 (using part (i) results)
  have h_yn_xn_diff_tendsto : Tendsto (fun n => alg.y n - alg.x n - (y - x)) atTop (𝓝 (0 : H)) := by
    have hyx : 𝓝 (y - x) = 𝓝 (y - x) := rfl
    simpa [sub_sub] using Tendsto.sub h_yn_xn_tendsto (tendsto_const_nhds (x := y - x))
  -- For the correction terms, we need ‖y_n-x_n-(y-x)‖ → 0
  -- This follows from the vector tending to 0 + continuity of norm
  have h_norm_yn_xn_diff_tendsto : Tendsto (fun n => ‖alg.y n - alg.x n - (y - x)‖)
      atTop (𝓝 (0 : ℝ)) := by
    have : (fun n => ‖alg.y n - alg.x n - (y - x)‖) = norm ∘ (fun n => alg.y n - alg.x n - (y - x)) := rfl
    rw [this]
    simpa [norm_zero] using continuous_norm.continuousAt.tendsto.comp h_yn_xn_diff_tendsto
  have h_norm_sq_yn_xn_diff_tendsto : Tendsto (fun n => ‖alg.y n - alg.x n - (y - x)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa [sq] using
      (Tendsto.mul h_norm_yn_xn_diff_tendsto h_norm_yn_xn_diff_tendsto : Tendsto (fun n => ‖_‖ * ‖_‖) atTop _)
  -- Cauchy-Schwarz gives |inner| ≤ ‖y_n-y‖ * ‖y_n-x_n-(y-x)‖
  -- Bound ‖y_n-y‖ ≤ √M (since ‖y_n-y‖² ≤ M)
  have hy_bound_sqrt : ∀ n, ‖alg.y n - y‖ ≤ Real.sqrt M := by
    intro n
    have hsq := hy_sq_bdd n
    have h_nonneg : 0 ≤ ‖alg.y n - y‖ := norm_nonneg _
    calc
      ‖alg.y n - y‖ = Real.sqrt (‖alg.y n - y‖ ^ 2) := by rw [Real.sqrt_sq h_nonneg]
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hsq
  have h_inner_raw_tendsto : Tendsto (fun n => inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x)))
      atTop (𝓝 (0 : ℝ)) := by
    have h_bound : ∀ n, ‖inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))‖ ≤
        Real.sqrt M * ‖alg.y n - alg.x n - (y - x)‖ := by
      intro n
      calc
        ‖inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))‖ ≤
            ‖alg.y n - y‖ * ‖alg.y n - alg.x n - (y - x)‖ :=
          norm_inner_le_norm (alg.y n - y) (alg.y n - alg.x n - (y - x))
        _ ≤ Real.sqrt M * ‖alg.y n - alg.x n - (y - x)‖ :=
          mul_le_mul_of_nonneg_right (hy_bound_sqrt n) (norm_nonneg _)
    have h_norm_tendsto : Tendsto (fun n => ‖inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))‖)
        atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero (fun n => norm_nonneg _) h_bound
      simpa [mul_zero] using Tendsto.const_mul (Real.sqrt M) h_norm_yn_xn_diff_tendsto
    -- For ℝ, |x| → 0 iff x → 0, and ‖x‖ = |x|
    have h_abs_tendsto : Tendsto (fun n => |inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))|)
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Real.norm_eq_abs] using h_norm_tendsto
    -- The metric on ℝ uses |·|, and ‖inner‖ = |inner|
    -- So ‖inner‖ → 0 implies inner → 0 (same metric condition)
    have h_metric := (Metric.tendsto_nhds (α := ℝ)).mp h_norm_tendsto
    apply (Metric.tendsto_nhds (α := ℝ)).mpr
    intro ε hε
    have h := h_metric ε hε
    refine h.mono fun n hn => ?_
    simpa [Real.dist_eq, Real.norm_eq_abs, sub_zero] using hn
  -- α_n * μ has finite limit, so 2*α_n*μ*inner → 0
  have h_inner_tendsto : Tendsto (fun n => 2 * α n * μ * inner ℝ (alg.y n - y)
      (alg.y n - alg.x n - (y - x))) atTop (𝓝 (0 : ℝ)) := by
    have h_alpha_mu_tendsto : Tendsto (fun n => α n * μ) atTop (𝓝 (α_lim * μ)) :=
      Tendsto.mul_const μ hα_tendsto
    have h_two_alpha_mu_tendsto : Tendsto (fun n => 2 * α n * μ) atTop (𝓝 (2 * α_lim * μ)) := by
      simpa [mul_assoc] using ((hα_tendsto.const_mul 2).mul_const μ)
    have h_prod := Tendsto.mul h_two_alpha_mu_tendsto h_inner_raw_tendsto
    simpa [mul_zero] using h_prod
  have h_norm_sq_tendsto : Tendsto (fun n => α n * μ * ‖alg.y n - alg.x n - (y - x)‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have h_alpha_mu_tendsto : Tendsto (fun n => α n * μ) atTop (𝓝 (α_lim * μ)) :=
      Tendsto.mul_const μ hα_tendsto
    have h_prod := Tendsto.mul h_alpha_mu_tendsto h_norm_sq_yn_xn_diff_tendsto
    simpa [mul_zero] using h_prod
  -- Now c_n·‖y_n - y‖² = A_n + correction → L_A (where correction → 0)
  set r : ℕ → ℝ := fun n =>
    -2 * α n * μ * inner ℝ (alg.y n - y) (alg.y n - alg.x n - (y - x))
    + α n * μ * ‖alg.y n - alg.x n - (y - x)‖ ^ 2 with hr_def
  have hr_tendsto : Tendsto r atTop (𝓝 (0 : ℝ)) := by
    rw [hr_def]
    have h1 : Tendsto (fun n => -2 * α n * μ * inner ℝ (alg.y n - y)
        (alg.y n - alg.x n - (y - x))) atTop (𝓝 (-0 : ℝ)) := by
      simpa using h_inner_tendsto.neg
    have h2 : Tendsto (fun n => α n * μ * ‖alg.y n - alg.x n - (y - x)‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
      h_norm_sq_tendsto
    simpa using h1.add h2
  have h_cn_norm_sq_tendsto : Tendsto (fun n => c n * ‖alg.y n - y‖ ^ 2) atTop (𝓝 (LD + SC)) := by
    have hA_minus_r : (fun n => A n - r n) = fun n => c n * ‖alg.y n - y‖ ^ 2 := by
      ext n; rw [hA_identity n, hr_def]; ring
    have hA_sub_tendsto : Tendsto (fun n => A n - r n) atTop (𝓝 (LD + SC - 0)) :=
      Tendsto.sub hA_tendsto hr_tendsto
    simp at hA_sub_tendsto
    rw [hA_minus_r] at hA_sub_tendsto
    exact hA_sub_tendsto
  -- Key algebraic lemma: if a_n·b_n → L and a_n → a > 0, then b_n → L/a
  have h_div_tendsto : Tendsto (fun n => ‖alg.y n - y‖ ^ 2) atTop (𝓝 ((LD + SC) / c_lim)) := by
    -- Since c_n → c_lim > 0, eventually c_n > 0
    have h_open : IsOpen {x : ℝ | x > 0} := by exact isOpen_Ioi
    have h_event_pos : ∀ᶠ n in atTop, c n > 0 :=
      hc_tendsto.eventually (h_open.mem_nhds hc_lim_pos)
    -- For large n, write ‖y_n - y‖² = (c_n·‖y_n - y‖²) / c_n, then both numerator and denominator converge
    have h_div_eq : (fun n => ‖alg.y n - y‖ ^ 2) =ᶠ[atTop]
        (fun n => (c n * ‖alg.y n - y‖ ^ 2) / c n) := by
      filter_upwards [h_event_pos] with n hn
      field_simp [hn.ne']
    -- Rewrite using eventually equality
    have h_div_tendsto' : Tendsto (fun n => (c n * ‖alg.y n - y‖ ^ 2) / c n) atTop (𝓝 ((LD + SC) / c_lim)) :=
      Tendsto.div h_cn_norm_sq_tendsto hc_tendsto (by
        intro hzero
        have : c_lim = 0 := hzero
        linarith [hc_lim_pos])
    -- h_div_tendsto': (c*norm_sq)/c → limit
    -- h_div_eq.symm: (c*norm_sq)/c =ᶠ[atTop] norm_sq
    -- Manually transfer the limit using the eventually equality
    have heq : (fun n => (c n * ‖alg.y n - y‖ ^ 2) / c n) =ᶠ[atTop] (fun n => ‖alg.y n - y‖ ^ 2) := h_div_eq.symm
    rw [Metric.tendsto_nhds] at h_div_tendsto' ⊢
    intro ε hε
    have h := h_div_tendsto' ε hε
    refine h.congr ?_
    filter_upwards [heq] with n hn
    simp [hn]
  -- ‖y_n - y‖ → √(lim ‖y_n - y‖²) by continuity of sqrt
  set Ly_sq := (LD + SC) / c_lim with hLy_sq_def
  have hLy_sq_nonneg : 0 ≤ Ly_sq := by
    rw [hLy_sq_def]
    refine div_nonneg ?_ (by linarith)
    -- LD + SC ≥ 0: A_n ≥ 0 and A_n = D_n + sum of C_k → LD + SC, so LD + SC ≥ 0
    have hA_nonneg : ∀ n, 0 ≤ A n := by
      intro n; rw [hA_def]; apply add_nonneg
      · exact mul_nonneg (mul_nonneg (hα_nonneg n) (by linarith)) (sq_nonneg _)
      · exact mul_nonneg (mul_nonneg (by linarith) (by nlinarith [hν_nonneg n])) (sq_nonneg _)
    have hA_tendsto_val : Tendsto A atTop (𝓝 (LD + SC)) := hA_tendsto
    exact ge_of_tendsto hA_tendsto_val (Filter.eventually_atTop.mpr ⟨0, fun n _ => hA_nonneg n⟩)
  have h_ynorm_tendsto : Tendsto (fun n => ‖alg.y n - y‖) atTop (𝓝 (Real.sqrt Ly_sq)) := by
    have h_eq : (fun n => ‖alg.y n - y‖) = (fun n => Real.sqrt (‖alg.y n - y‖ ^ 2)) := by
      ext n; simp [Real.sqrt_sq (norm_nonneg _)]
    rw [h_eq, hLy_sq_def]
    exact (Real.continuous_sqrt.continuousAt.tendsto).comp h_div_tendsto
  have h_ynorm_succ_tendsto : ∃ Ly : ℝ, Tendsto (fun n => ‖alg.y (n+1) - y‖) atTop (𝓝 Ly) := by
    refine ⟨Real.sqrt Ly_sq, ?_⟩
    have : (fun n => ‖alg.y (n+1) - y‖) = (fun n => ‖alg.y n - y‖) ∘ (fun n => n+1) := by
      ext n; simp
    rw [this]
    exact h_ynorm_tendsto.comp (tendsto_add_atTop_nat 1)
  -- ‖x_n - x‖ → via triangle identity: x_n - x = (y_n - y) - (y_n - x_n - (y - x))
  -- ‖x_n - x‖ → √(Ly_sq): use |‖x_n-x‖ - ‖y_n-y‖| ≤ ‖(x_n-x) - (y_n-y)‖ = ‖y_n-x_n-(y-x)‖ → 0
  have h_xnorm_tendsto : Tendsto (fun n => ‖alg.x n - x‖) atTop (𝓝 (Real.sqrt Ly_sq)) := by
    -- First, ‖(x_n - x) - (y_n - y)‖ = ‖y_n - x_n - (y - x)‖ → 0
    have h_vec_diff_tendsto : Tendsto (fun n => (alg.x n - x) - (alg.y n - y)) atTop (𝓝 (0 : H)) := by
      have h_eq' : (fun n => (alg.x n - x) - (alg.y n - y)) = fun n => -((alg.y n - alg.x n) - (y - x)) := by
        ext n; abel
      rw [h_eq']
      simpa [sub_sub, add_comm, add_left_comm] using h_yn_xn_diff_tendsto.neg
    have h_norm_vec_diff_tendsto : Tendsto (fun n => ‖(alg.x n - x) - (alg.y n - y)‖) atTop
        (𝓝 (0 : ℝ)) := by
      have : (fun n => ‖(alg.x n - x) - (alg.y n - y)‖) = norm ∘ (fun n => (alg.x n - x) - (alg.y n - y)) := rfl
      rw [this]
      simpa [norm_zero] using continuous_norm.continuousAt.tendsto.comp h_vec_diff_tendsto
    -- |‖x_n-x‖ - ‖y_n-y‖| ≤ ‖(x_n-x) - (y_n-y)‖ → 0
    have h_abs_bound : ∀ n, |‖alg.x n - x‖ - ‖alg.y n - y‖| ≤ ‖(alg.x n - x) - (alg.y n - y)‖ := by
      intro n; exact abs_norm_sub_norm_le _ _
    have h_abs_tendsto_zero : Tendsto (fun n => |‖alg.x n - x‖ - ‖alg.y n - y‖|) atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun n => abs_nonneg _) h_abs_bound h_norm_vec_diff_tendsto
    -- |a_n| → 0 implies a_n → 0 (tendsto_zero_iff_abs_tendsto_zero)
    have h_diff_tendsto_zero : Tendsto (fun n => ‖alg.x n - x‖ - ‖alg.y n - y‖) atTop (𝓝 (0 : ℝ)) :=
      ((tendsto_zero_iff_abs_tendsto_zero _).mpr h_abs_tendsto_zero)
    -- ‖x_n - x‖ = (‖x_n-x‖ - ‖y_n-y‖) + ‖y_n-y‖ → 0 + √(Ly_sq)
    have h_eq_add : (fun n => ‖alg.x n - x‖) = fun n =>
        (‖alg.x n - x‖ - ‖alg.y n - y‖) + ‖alg.y n - y‖ := by
      ext n; ring
    rw [h_eq_add]
    simpa [zero_add] using Tendsto.add h_diff_tendsto_zero h_ynorm_tendsto
  have h_xnorm_succ_tendsto : ∃ Lx : ℝ, Tendsto (fun n => ‖alg.x (n+1) - x‖) atTop (𝓝 Lx) := by
    refine ⟨Real.sqrt Ly_sq, ?_⟩
    have : (fun n => ‖alg.x (n+1) - x‖) = (fun n => ‖alg.x n - x‖) ∘ (fun n => n+1) := by
      ext n; simp
    rw [this]
    exact h_xnorm_tendsto.comp (tendsto_add_atTop_nat 1)
  exact ⟨⟨h_yn_xn_tendsto, h_xdiff_tendsto, h_ydiff_tendsto⟩, ⟨h_xnorm_succ_tendsto, h_ynorm_succ_tendsto⟩⟩
