import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1

open scoped InnerProductSpace

open ERealFunction

/-! `IsProximalPoint` (subgradient-form proximal optimality) is supplied canonically by
Foundation (`Foundation.Convex.Subdifferential`); recalled here for paper-local use. -/
recall IsProximalPoint

/-- `p` is a proximal point for an extended-real-valued objective. -/
def IsProximalPointEReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (lam : ℝ) (x p : H) : Prop :=
  ∃ (_hp : g p ≠ ⊤),
    x - p ∈ (fun u ↦ lam • u) '' subdifferential g p

/-- A chosen proximal mapping, specified by its optimality inclusion. -/
structure ProximalMapping {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (lam : ℝ) (hlam : 0 < lam) (hconvex : ConvexOn ℝ Set.univ g)
    (hlsc : LowerSemicontinuous g) where
  toFun : H → H
  optimality (x : H) : IsProximalPoint g lam x (toFun x)
  minimizes (x y : H) : g (toFun x) + ‖toFun x - x‖ ^ 2 / (2 * lam) ≤
    g y + ‖y - x‖ ^ 2 / (2 * lam)
  unique (x p : H) : IsProximalPoint g lam x p → p = toFun x

/-- A chosen proximal mapping for an extended-real-valued convex objective. -/
structure ERealProximalMapping {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (lam : ℝ) (hlam : 0 < lam) where
  toFun : H → H
  optimality (x : H) : IsProximalPointEReal g lam x (toFun x)
  unique (x p : H) : IsProximalPointEReal g lam x p → p = toFun x
