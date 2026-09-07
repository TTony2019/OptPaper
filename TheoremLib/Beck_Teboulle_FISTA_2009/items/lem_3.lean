import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_6
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_1
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_2

open scoped RealInnerProductSpace

/-- Lemma 2.3: Key inequality for gradient-step analysis.

Let `y ∈ ℝⁿ` and `L > 0` be such that `F(z) ≤ Q_L(z, y)` where `z` is a proximal point.
Then for any `x ∈ ℝⁿ`:
`F(x) - F(z) ≥ (L/2)‖z - y‖² + L⟨y - x, z - y⟩`.

This is the central inequality used in the convergence analysis of both ISTA and FISTA. -/
theorem key_inequality {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hP : ProblemP f g L) (y x z : EuclideanSpace ℝ (Fin n))
    (hz : IsProxPoint f g L y z)
    (hcond : compositeObjective f g z ≤ quadraticApprox f g L z y) :
    compositeObjective f g x - compositeObjective f g z ≥
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by
  have hLpos : 0 < L := hP.smooth_f.hL_pos
  -- Lemma 2.2: optimality condition → existence of subgradient γ
  have h_gamma : ∃ (γ : EuclideanSpace ℝ (Fin n)), γ ∈ subdifferential g z ∧
      gradient f y + L • (z - y) + γ = 0 :=
    ((proxMap_optimality_condition (f := f) (g := g) hLpos hP.convex_g y z).mp hz)
  rcases h_gamma with ⟨γ, hγ_subdiff, hγ_eq⟩
  -- Gradient inequality for convex C^1 f: f a ≥ f b + ⟨∇f b, a-b⟩
  -- Proof: restrict f to line a→b, use HasLineDerivAt + ConvexOn.le_slope_of_hasDerivAt
  have h_convex_f (a b : EuclideanSpace ℝ (Fin n)) :
      f a ≥ f b + ⟪gradient f b, a - b⟫ := by
    let h_ab := fun (t : ℝ) => f (b + t • (a - b))
    have h_conv_ab : ConvexOn ℝ (Set.univ : Set ℝ) h_ab := by
      refine ⟨convex_univ, λ p hp q hq c d hc hd hcd => ?_⟩
      dsimp [h_ab]
      have hkey : b + ((c * p + d * q) • (a - b)) =
          c • (b + p • (a - b)) + d • (b + q • (a - b)) := by
        calc
          b + ((c * p + d * q) • (a - b))
              = (c + d) • b + ((c * p + d * q) • (a - b)) := by simp [hcd]
          _ = (c • b + d • b) + ((c * p) • (a - b) + (d * q) • (a - b)) := by simp [add_smul]
          _ = c • b + d • b + (c * p) • (a - b) + (d * q) • (a - b) := by abel
          _ = c • b + (c * p) • (a - b) + (d • b + (d * q) • (a - b)) := by abel
          _ = c • (b + p • (a - b)) + d • (b + q • (a - b)) := by simp [smul_add, mul_smul]
      rw [hkey]
      have hpu : (b + p • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hpv : (b + q • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hineq := hP.convex_f.2 hpu hpv hc hd hcd
      simpa [smul_eq_mul] using hineq
    have h_diff_ab : Differentiable ℝ f :=
      hP.smooth_f.contDiff.differentiable (by decide)
    have h_diffAt_b : DifferentiableAt ℝ f b := h_diff_ab.differentiableAt
    have h_line : HasLineDerivAt ℝ f (lineDeriv ℝ f b (a - b)) b (a - b) :=
      h_diffAt_b.lineDifferentiableAt.hasLineDerivAt
    have h_line_deriv : lineDeriv ℝ f b (a - b) = ⟪gradient f b, a - b⟫ := by
      rw [h_diffAt_b.lineDeriv_eq_fderiv, inner_gradient_left h_diffAt_b]
    have h_deriv : HasDerivAt h_ab (⟪gradient f b, a - b⟫) 0 := by
      have h_line' : HasLineDerivAt ℝ f (⟪gradient f b, a - b⟫) b (a - b) := by
        simpa [h_line_deriv] using h_line
      dsimp [HasLineDerivAt] at h_line' ⊢
      exact h_line'
    have h_slope : ⟪gradient f b, a - b⟫ ≤ h_ab 1 - h_ab 0 := by
      have := ConvexOn.le_slope_of_hasDerivAt h_conv_ab (Set.mem_univ 0) (Set.mem_univ 1)
        (by norm_num : (0 : ℝ) < 1) h_deriv
      simpa [slope, div_one] using this
    have h0 : h_ab 0 = f b := by simp [h_ab]
    have h1 : h_ab 1 = f a := by simp [h_ab]
    rw [h0, h1] at h_slope
    linarith
  -- Subgradient inequality for g
  have h_subgrad_g (a : EuclideanSpace ℝ (Fin n)) : g a ≥ g z + ⟪γ, a - z⟫ :=
    hγ_subdiff a
  -- Expand definitions
  dsimp [compositeObjective, quadraticApprox] at hcond ⊢
  -- Combine f and g lower bounds
  have h_lower (a : EuclideanSpace ℝ (Fin n)) :
      f a + g a ≥ f y + ⟪gradient f y, a - y⟫ + g z + ⟪γ, a - z⟫ := by
    have hf := h_convex_f a y
    have hg := h_subgrad_g a
    linarith
  have h_Fx_lower := h_lower x
  -- Express γ from the optimality condition
  have hγ_expr : γ = -gradient f y - L • (z - y) := by
    calc
      γ = -(gradient f y + L • (z - y)) :=
        eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hγ_eq)
      _ = -gradient f y - L • (z - y) := by abel
  rw [hγ_expr] at h_Fx_lower
  -- Key algebraic identity: set a := z-y, b := x-z.
  set a := z - y with ha
  set b := x - z with hb
  have hyx_eq : y - x = -a - b := by dsimp [a, b]; abel
  have hx_minus_y : x - y = a + b := by dsimp [a, b]; abel
  -- Compute the main algebraic expression
  have h_algebra : (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
      (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) =
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by
    rw [hx_minus_y, ← ha, hyx_eq]
    simp [sub_eq_add_neg, inner_add_right, inner_add_left, inner_neg_left, inner_smul_left,
      real_inner_self_eq_norm_sq a, real_inner_comm b a]
    ring
  -- Assemble the final inequality
  have h_Fx_lower' : f x + g x ≥ f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫ := by
    simpa [ha, hb] using h_Fx_lower
  calc
    f x + g x - (f z + g z)
        ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) - (f z + g z) := by linarith
    _ ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
        (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) := by linarith
    _ = (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by rw [h_algebra]

/-- Generalized version of Lemma 2.3 where the stepsize `L` is independent of the
Lipschitz constant `Lf`. This is needed for FISTA where stepsizes may vary.

Assumptions:
- `hP : ProblemP f g Lf` — the standing assumptions on f (C¹˒¹ with constant `Lf`,
  convex) and g (continuous, convex)
- `hLpos : 0 < L` — positivity of the stepsize
- `hz : IsProxPoint f g L y z` — `z` minimizes `Q_L(·, y)`
- `hcond : F(z) ≤ Q_L(z, y)` — the descent condition (automatic when `L ≥ Lf`)

Conclusion: `F(x) - F(z) ≥ (L/2)‖z - y‖² + L⟨y - x, z - y⟩`. -/
theorem key_inequality' {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf L : ℝ}
    (hP : ProblemP f g Lf) (hLpos : 0 < L)
    (y x z : EuclideanSpace ℝ (Fin n))
    (hz : IsProxPoint f g L y z)
    (hcond : compositeObjective f g z ≤ quadraticApprox f g L z y) :
    compositeObjective f g x - compositeObjective f g z ≥
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by
  -- Lemma 2.2: optimality condition → existence of subgradient γ
  have h_gamma : ∃ (γ : EuclideanSpace ℝ (Fin n)), γ ∈ subdifferential g z ∧
      gradient f y + L • (z - y) + γ = 0 :=
    ((proxMap_optimality_condition (f := f) (g := g) hLpos hP.convex_g y z).mp hz)
  rcases h_gamma with ⟨γ, hγ_subdiff, hγ_eq⟩
  -- Gradient inequality for convex C^1 f: f a ≥ f b + ⟨∇f b, a-b⟩
  have h_convex_f (a b : EuclideanSpace ℝ (Fin n)) :
      f a ≥ f b + ⟪gradient f b, a - b⟫ := by
    let h_ab := fun (t : ℝ) => f (b + t • (a - b))
    have h_conv_ab : ConvexOn ℝ (Set.univ : Set ℝ) h_ab := by
      refine ⟨convex_univ, λ p hp q hq c d hc hd hcd => ?_⟩
      dsimp [h_ab]
      have hkey : b + ((c * p + d * q) • (a - b)) =
          c • (b + p • (a - b)) + d • (b + q • (a - b)) := by
        calc
          b + ((c * p + d * q) • (a - b))
              = (c + d) • b + ((c * p + d * q) • (a - b)) := by simp [hcd]
          _ = (c • b + d • b) + ((c * p) • (a - b) + (d * q) • (a - b)) := by simp [add_smul]
          _ = c • b + d • b + (c * p) • (a - b) + (d * q) • (a - b) := by abel
          _ = c • b + (c * p) • (a - b) + (d • b + (d * q) • (a - b)) := by abel
          _ = c • (b + p • (a - b)) + d • (b + q • (a - b)) := by simp [smul_add, mul_smul]
      rw [hkey]
      have hpu : (b + p • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hpv : (b + q • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hineq := hP.convex_f.2 hpu hpv hc hd hcd
      simpa [smul_eq_mul] using hineq
    have h_diff_ab : Differentiable ℝ f :=
      hP.smooth_f.contDiff.differentiable (by decide)
    have h_diffAt_b : DifferentiableAt ℝ f b := h_diff_ab.differentiableAt
    have h_line : HasLineDerivAt ℝ f (lineDeriv ℝ f b (a - b)) b (a - b) :=
      h_diffAt_b.lineDifferentiableAt.hasLineDerivAt
    have h_line_deriv : lineDeriv ℝ f b (a - b) = ⟪gradient f b, a - b⟫ := by
      rw [h_diffAt_b.lineDeriv_eq_fderiv, inner_gradient_left h_diffAt_b]
    have h_deriv : HasDerivAt h_ab (⟪gradient f b, a - b⟫) 0 := by
      have h_line' : HasLineDerivAt ℝ f (⟪gradient f b, a - b⟫) b (a - b) := by
        simpa [h_line_deriv] using h_line
      dsimp [HasLineDerivAt] at h_line' ⊢
      exact h_line'
    have h_slope : ⟪gradient f b, a - b⟫ ≤ h_ab 1 - h_ab 0 := by
      have := ConvexOn.le_slope_of_hasDerivAt h_conv_ab (Set.mem_univ 0) (Set.mem_univ 1)
        (by norm_num : (0 : ℝ) < 1) h_deriv
      simpa [slope, div_one] using this
    have h0 : h_ab 0 = f b := by simp [h_ab]
    have h1 : h_ab 1 = f a := by simp [h_ab]
    rw [h0, h1] at h_slope
    linarith
  -- Subgradient inequality for g
  have h_subgrad_g (a : EuclideanSpace ℝ (Fin n)) : g a ≥ g z + ⟪γ, a - z⟫ :=
    hγ_subdiff a
  -- Expand definitions
  dsimp [compositeObjective, quadraticApprox] at hcond ⊢
  -- Combine f and g lower bounds
  have h_lower (a : EuclideanSpace ℝ (Fin n)) :
      f a + g a ≥ f y + ⟪gradient f y, a - y⟫ + g z + ⟪γ, a - z⟫ := by
    have hf := h_convex_f a y
    have hg := h_subgrad_g a
    linarith
  have h_Fx_lower := h_lower x
  -- Express γ from the optimality condition
  have hγ_expr : γ = -gradient f y - L • (z - y) := by
    calc
      γ = -(gradient f y + L • (z - y)) :=
        eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hγ_eq)
      _ = -gradient f y - L • (z - y) := by abel
  rw [hγ_expr] at h_Fx_lower
  -- Key algebraic identity: set a := z-y, b := x-z.
  set a := z - y with ha
  set b := x - z with hb
  have hyx_eq : y - x = -a - b := by dsimp [a, b]; abel
  have hx_minus_y : x - y = a + b := by dsimp [a, b]; abel
  -- Compute the main algebraic expression
  have h_algebra : (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
      (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) =
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by
    rw [hx_minus_y, ← ha, hyx_eq]
    simp [sub_eq_add_neg, inner_add_right, inner_add_left, inner_neg_left, inner_smul_left,
      real_inner_self_eq_norm_sq a, real_inner_comm b a]
    ring
  -- Assemble the final inequality
  have h_Fx_lower' : f x + g x ≥ f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫ := by
    simpa [ha, hb] using h_Fx_lower
  calc
    f x + g x - (f z + g z)
        ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) - (f z + g z) := by linarith
    _ ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
        (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) := by linarith
    _ = (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by rw [h_algebra]
