import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_4
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7

open Set
open scoped RealInnerProductSpace

/-- Lemma 2.2: Optimality characterization of the proximal operator.

For any `y ∈ ℝⁿ`, one has that `z` is a proximal point (i.e., `z = p_L(y)`)
if and only if there exists `γ(y) ∈ ∂g(z)` (the subdifferential of `g`) such that
`∇f(y) + L(z - y) + γ(y) = 0`.

The forward direction (→) uses convexity of g (standing assumption in Problem P).
The backward direction (←) is algebraic:
given γ = -∇f(y) - L(z-y) ∈ ∂g(z), for any x, Q_L(x,y) - Q_L(z,y) = (L/2)‖x-z‖² ≥ 0. -/
theorem proxMap_optimality_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ} (hL : 0 < L) (hg_conv : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) g)
    (y z : EuclideanSpace ℝ (Fin n)) :
    IsProxPoint f g L y z ↔
    ∃ (γ : EuclideanSpace ℝ (Fin n)), γ ∈ subdifferential g z ∧
      gradient f y + L • (z - y) + γ = 0 := by
  constructor
  · intro h_prox
    have h_min (x : EuclideanSpace ℝ (Fin n)) :
        quadraticApprox f g L z y ≤ quadraticApprox f g L x y := h_prox (mem_univ x)
    set γ := -gradient f y - L • (z - y) with hγ_def
    set a := gradient f y + L • (z - y) with ha_def
    have hγ_subdiff : γ ∈ subdifferential g z := by
      intro w
      set D := g w - g z + ⟪a, w - z⟫ with hD_def
      set C := (L / 2) * ‖w - z‖ ^ 2 with hC_def
      have hC_nonneg : 0 ≤ C := by nlinarith [sq_nonneg ‖w - z‖]
      have h_core (t : ℝ) (ht_pos : 0 < t) (ht_le1 : t ≤ 1) : D + C * t ≥ 0 := by
        set x_t := z + t • (w - z) with hxt_def
        have hQ := h_min x_t
        dsimp [quadraticApprox] at hQ
        -- quadraticApprox def: f y + ⟨∇f y, x-y⟩ + ... (∇f FIRST, then x-y)
        -- Normalize to ⟨v, ∇f⟩ order via inner_comm
        -- hQ uses ⟨∇f y, v⟩ order; match it in h_nonneg
        have h_nonneg : 0 ≤ (⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫) +
            (L / 2) * (‖x_t - y‖ ^ 2 - ‖z - y‖ ^ 2) + (g x_t - g z) := by
          linarith
        -- Inner product: ⟨∇f, x_t-y⟩ - ⟨∇f, z-y⟩ = t·⟨∇f, w-z⟩
        have h_inner : ⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫ =
            t * ⟪gradient f y, w - z⟫ := by
          calc
            ⟪gradient f y, x_t - y⟫ - ⟪gradient f y, z - y⟫
                = ⟪gradient f y, (x_t - y) - (z - y)⟫ := by
                  rw [← inner_sub_right]
            _ = ⟪gradient f y, x_t - z⟫ := by abel
            _ = ⟪gradient f y, t • (w - z)⟫ := by dsimp [x_t]; abel
            _ = t * ⟪gradient f y, w - z⟫ := by rw [inner_smul_right]
        -- Norm difference
        have h_norm : ‖x_t - y‖ ^ 2 - ‖z - y‖ ^ 2 =
            2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2 := by
          dsimp [x_t]
          calc
            ‖(z + t • (w - z)) - y‖ ^ 2 - ‖z - y‖ ^ 2
                = ‖(z - y) + t • (w - z)‖ ^ 2 - ‖z - y‖ ^ 2 := by abel
            _ = (‖z - y‖ ^ 2 + 2 * ⟪z - y, t • (w - z)⟫ + ‖t • (w - z)‖ ^ 2) - ‖z - y‖ ^ 2 := by
              rw [norm_add_sq_real]
            _ = 2 * ⟪z - y, t • (w - z)⟫ + ‖t • (w - z)‖ ^ 2 := by ring
            _ = 2 * (t * ⟪z - y, w - z⟫) + ‖t • (w - z)‖ ^ 2 := by rw [inner_smul_right]
            _ = 2 * t * ⟪z - y, w - z⟫ + ‖t • (w - z)‖ ^ 2 := by ring
            _ = 2 * t * ⟪z - y, w - z⟫ + ((|t|) * ‖w - z‖) ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs]
            _ = 2 * t * ⟪z - y, w - z⟫ + (t * ‖w - z‖) ^ 2 := by rw [abs_of_pos ht_pos]
            _ = 2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2 := by ring
        rw [h_inner, h_norm] at h_nonneg
        -- h_nonneg: 0 ≤ t·⟨w-z,∇f⟩ + (L/2)(2t·⟨z-y,w-z⟩ + t²·‖w-z‖²) + g(x_t) - g(z)
        -- Expand the middle term
        have h_expand : (L / 2) * (2 * t * ⟪z - y, w - z⟫ + t ^ 2 * ‖w - z‖ ^ 2) =
            L * t * ⟪z - y, w - z⟫ + (L / 2) * t ^ 2 * ‖w - z‖ ^ 2 := by ring
        rw [h_expand] at h_nonneg
        -- Relate to a: t·⟨∇f, w-z⟩ + L·t·⟨z-y, w-z⟩ = t·⟨a, w-z⟩
        have ha_eq : t * ⟪gradient f y, w - z⟫ + L * t * ⟪z - y, w - z⟫ = t * ⟪a, w - z⟫ := by
          calc
            t * ⟪gradient f y, w - z⟫ + L * t * ⟪z - y, w - z⟫
                = t * (⟪gradient f y, w - z⟫ + L * ⟪z - y, w - z⟫) := by ring
            _ = t * (⟪gradient f y, w - z⟫ + ⟪L • (z - y), w - z⟫) := by
              rw [inner_smul_left]; simp
            _ = t * ⟪gradient f y + L • (z - y), w - z⟫ := by rw [inner_add_left]
            _ = t * ⟪a, w - z⟫ := rfl
        have h_nonneg' : 0 ≤ t * ⟪a, w - z⟫ + (L / 2) * t ^ 2 * ‖w - z‖ ^ 2 + (g x_t - g z) := by
          linarith
        -- Convexity: g(x_t) - g(z) ≤ t(g(w) - g(z))
        have h_conv : g x_t - g z ≤ t * (g w - g z) := by
          have h_xt_eq : x_t = (1 - t) • z + t • w := by
            dsimp [x_t]; simp [smul_sub, sub_smul]; abel
          rw [h_xt_eq]
          have h_ineq := hg_conv.2 (mem_univ z) (mem_univ w)
            (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ t) (by ring : (1 - t) + t = 1)
          have h_ineq' : g ((1 - t) • z + t • w) ≤ (1 - t) * g z + t * g w := by
            simpa [smul_eq_mul] using h_ineq
          linarith
        -- Combine: replace g(x_t)-g(z) with upper bound
        nlinarith
      -- Now: D + C·t ≥ 0 ∀ t ∈ (0,1]. Need D ≥ 0.
      by_cases hD_nonneg : 0 ≤ D
      · -- D ≥ 0 means g w - g z ≥ -⟨a, w-z⟩ = ⟨γ, w-z⟩
        have h_gamma_inner : ⟪γ, w - z⟫ = -⟪a, w - z⟫ := by
          dsimp [γ, a]
          calc
            ⟪-gradient f y - L • (z - y), w - z⟫
                = ⟪(-gradient f y) - L • (z - y), w - z⟫ := rfl
            _ = ⟪-gradient f y, w - z⟫ - ⟪L • (z - y), w - z⟫ := by rw [inner_sub_left]
            _ = -⟪gradient f y, w - z⟫ - L * ⟪z - y, w - z⟫ := by simp [inner_smul_left]
            _ = -(⟪gradient f y, w - z⟫ + L * ⟪z - y, w - z⟫) := by ring
            _ = -⟪gradient f y + L • (z - y), w - z⟫ := by
              simp [inner_add_left, inner_smul_left]
        rw [h_gamma_inner]; linarith
      · -- D < 0. Pick t small enough to get contradiction via h_core.
        by_cases hC_zero : C = 0
        · have h1 := h_core 1 (by norm_num) (by norm_num)
          rw [hC_zero] at h1; nlinarith
        · have hC_pos : 0 < C := by
            by_contra! h; apply hC_zero; linarith
          by_cases h_ratio : -D / (2 * C) ≤ 1
          · set t := -D / (2 * C) with ht_def
            have ht_pos : 0 < t := div_pos (by linarith) (by nlinarith)
            have ht_le1 : t ≤ 1 := h_ratio
            have h_core_t := h_core t ht_pos ht_le1
            have hCt_eq : C * t = -D / 2 := by
              dsimp [t]; field_simp [hC_pos.ne.symm]
            rw [hCt_eq] at h_core_t; nlinarith
          · have h_core_1 := h_core 1 (by norm_num) (by norm_num)
            -- From -D/(2C) > 1 and C > 0: -D > 2C, so D < -2C
            have h_pos_2C : 0 < 2 * C := by nlinarith
            have h_Div : -D / (2 * C) > 1 := by linarith
            have h_D_lt : D < -2 * C := by
              have h_mul : -D > 2 * C := by
                calc
                  -D = (-D / (2 * C)) * (2 * C) := by field_simp [h_pos_2C.ne.symm]
                  _ > 1 * (2 * C) := by nlinarith
                  _ = 2 * C := by ring
              linarith
            nlinarith
    exact ⟨γ, hγ_subdiff, by dsimp [a, γ]; abel⟩
  · -- Backward direction (←): purely algebraic
    rintro ⟨γ, hγ_subdiff, hγ_eq⟩
    have hγ_formula : γ = -gradient f y - L • (z - y) := by
      calc
        γ = (gradient f y + L • (z - y) + γ) - (gradient f y + L • (z - y)) := by abel
        _ = 0 - (gradient f y + L • (z - y)) := by rw [hγ_eq]
        _ = -gradient f y - L • (z - y) := by abel
    have h_subgrad (x : EuclideanSpace ℝ (Fin n)) :
        g z + ⟪-gradient f y - L • (z - y), x - z⟫ ≤ g x := by
      rw [← hγ_formula]; exact hγ_subdiff x
    intro x hx
    dsimp [quadraticApprox]
    have h_subgrad_x : g x - g z ≥ -⟪gradient f y + L • (z - y), x - z⟫ := by
      have h := h_subgrad x
      have h_neg_sum : -gradient f y - L • (z - y) = -(gradient f y + L • (z - y)) := by abel
      rw [h_neg_sum, inner_neg_left] at h; linarith
    have h_norm_diff : ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2 = ‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫ := by
      calc
        ‖x - y‖ ^ 2 - ‖z - y‖ ^ 2
            = ‖(x - z) + (z - y)‖ ^ 2 - ‖z - y‖ ^ 2 := by abel
        _ = (‖x - z‖ ^ 2 + 2 * inner ℝ (x - z) (z - y) + ‖z - y‖ ^ 2) - ‖z - y‖ ^ 2 := by
          rw [norm_add_sq_real]
        _ = ‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫ := by ring
    have h_diff_nonneg : 0 ≤ (⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x) -
        (⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) := by
      have h_inner_diff : ⟪gradient f y, x - y⟫ - ⟪gradient f y, z - y⟫ = ⟪gradient f y, x - z⟫ := by
        rw [← inner_sub_right]; abel
      have h_expr : (⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x) -
          (⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) =
          ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - y‖ ^ 2 - ‖z - y‖ ^ 2) + (g x - g z) := by nlinarith
      rw [h_expr, h_norm_diff]
      have h_lower : ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫) + (g x - g z) ≥
          (L / 2) * ‖x - z‖ ^ 2 := by
        calc
          ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫) + (g x - g z) ≥
              ⟪gradient f y, x - z⟫ + (L / 2) * (‖x - z‖ ^ 2 + 2 * ⟪x - z, z - y⟫)
              + (-⟪gradient f y + L • (z - y), x - z⟫) := by nlinarith
          _ = (L / 2) * ‖x - z‖ ^ 2 := by
            rw [inner_add_left]
            simp [inner_smul_left]
            rw [real_inner_comm (x - z) (z - y)]
            ring
      have h_nonneg_sq : 0 ≤ (L / 2) * ‖x - z‖ ^ 2 := by nlinarith [sq_nonneg ‖x - z‖]
      linarith
    linarith
