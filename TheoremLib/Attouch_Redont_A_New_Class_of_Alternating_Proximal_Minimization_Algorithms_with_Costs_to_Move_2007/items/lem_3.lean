import Mathlib

/-!
# Lemma 4.3: Quadratic-Case Estimates

Under H41-H46 (quadratic costs on Hilbert space, INE nonempty), the sequence (x_n, y_n)
from (CA²) satisfies three key inequalities involving firm nonexpansiveness of resolvents.

Note: Paper hypothesis H44 (α_n ≥ 0, ν_n ≥ 0) is required for positivity of denominators
α_n + β and μ + ν_n; these are included as explicit hypotheses in each lemma.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set
open scoped RealInnerProductSpace

/-- CA2 algorithm (duplicated for self-containment; see algo_1). -/
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

/-- Inertial Nash Equilibrium (duplicated for self-containment; see def_1). -/
def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

/-- Firmly nonexpansive (duplicated for self-containment; see ext_def_2). -/
def IsFirmlyNonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) : Prop :=
  ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y)

/-- Assumptions H41-H46 (quadratic costs, INE nonempty). -/
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
    {f g : H → ℝ} {β μ ν : ℝ} (x y : H) (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ ν x y) (ξ : H) :
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

set_option maxHeartbeats 2000000

/--
Lemma 4.3(a): First norm inequality.
Uses firm nonexpansiveness of resolvent T_f^n via subgradient method.
Note: α_n ≥ 0, ν_n ≥ 0 (paper hypothesis H44) are required for positivity of denominator α_n + β.
-/
theorem lemma_4_3_a {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

/--
Lemma 4.3(b): Second norm inequality.
Uses firm nonexpansiveness of resolvent T_g^n and the bound from part (a).
Note: α_n ≥ 0, ν_n ≥ 0 (paper hypothesis H44) are required for positivity of denominators.
-/
theorem lemma_4_3_b {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

/--
Lemma 4.3(c): Combined inequality derived from (a) and (b).
Multiply (a) by α_n·μ and (b) by β(μ+ν_n), then add. The negative terms give
a Lyapunov-type decrease.
-/
theorem lemma_4_3_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
  set xn1 := alg.x (n+1)
  set xn := alg.x n
  set yn1 := alg.y (n+1)
  set yn := alg.y n
  have hβpos : β > 0 := hyp.beta_pos
  have hμpos : μ > 0 := hyp.mu_pos
  have hα_nonneg_n : α n ≥ 0 := hα_nonneg n
  have hν_nonneg_n : ν n ≥ 0 := hν_nonneg n
  have h_adenom_pos : α n + β > 0 := by linarith
  have ha := lemma_4_3_a hyp x y hα_nonneg hν_nonneg alg hine n
  have hb := lemma_4_3_b hyp x y hα_nonneg hν_nonneg alg hine n
  -- Clear denominators: multiply ha by (α_n+β), multiply hb by (μ+ν_n)(α_n+β)
  have ha_mul : (α n + β) * ‖xn1 - x‖ ^ 2 ≤
      α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2 := by
    calc
      (α n + β) * ‖xn1 - x‖ ^ 2 ≤ (α n + β) * ((1 / (α n + β)) *
        (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left ha (by linarith)
      _ = α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2 := by
        field_simp [h_adenom_pos.ne']
  have hb_mul : (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2 ≤
      μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
      μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
      μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2 := by
    have hbden_pos : (μ + ν n) * (α n + β) > 0 := by positivity
    calc
      (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2 ≤
          (μ + ν n) * (α n + β) * ((1 / ((μ + ν n) * (α n + β))) *
            (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
             μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
             μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
          μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
          μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2 := by
        field_simp [hbden_pos.ne']
  -- Now multiply ha_mul by α_n·μ, and hb_mul by β
  have h1 : α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2 ≤
      α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ α n * μ := by nlinarith
    have htemp := mul_le_mul_of_nonneg_left ha_mul h_nonneg
    simpa [mul_assoc] using htemp
  have h2 : β * ((μ + ν n) * (α n + β)) * ‖yn1 - y‖ ^ 2 ≤
      β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ β := by linarith
    have htemp := mul_le_mul_of_nonneg_left hb_mul h_nonneg
    simpa [mul_assoc] using htemp
  -- Add h1 and h2
  have h_add : (α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2) + (β * (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2) ≤
      (α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) +
      (β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) := by
    nlinarith
  -- Factor (α_n+β) from both sides using ring
  have h_lhs_expand : (α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2) + (β * (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2) =
      (α n + β) * (α n * μ * ‖xn1 - x‖ ^ 2 + β * (μ + ν n) * ‖yn1 - y‖ ^ 2) := by ring
  have h_rhs_expand : (α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) +
      (β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) =
      (α n + β) * (α n * μ * ‖xn - x‖ ^ 2 + β * (μ + ν n) * ‖yn - y‖ ^ 2 -
        α n * μ * ‖xn1 - xn‖ ^ 2 - β * ν n * ‖yn1 - yn‖ ^ 2 -
        β * μ * ‖yn - xn1 - y + x‖ ^ 2 - β * μ * ‖yn1 - xn1 - y + x‖ ^ 2) := by ring
  rw [h_lhs_expand, h_rhs_expand] at h_add
  -- Cancel (α_n+β) > 0: h_add has form c * LHS' ≤ c * RHS' with c = α_n+β > 0
  -- Use le_of_mul_le_mul_left: 0 < c → c*a ≤ c*b → a ≤ b
  exact le_of_mul_le_mul_left h_add h_adenom_pos
