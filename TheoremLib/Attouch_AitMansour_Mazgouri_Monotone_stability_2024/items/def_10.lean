import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_8
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4

/-! Item `def_10`: Definition 7.5, the `ε`-approximate solution set `S^ε(μ)`.

  The paper declares, for `x ∈ C¹([0,T];H)`,

  `x ∈ ε-Fix(Γ_{A,u₀,v₀}) :⟺ ‖x - Γ_{A,u₀,v₀}(x)‖ ≤ ε` and
  `S^ε(A,u₀,v₀) := ε-Fix(Γ_{A,u₀,v₀})`,

  where `Γ_{A,u₀,v₀}(x)(t) = u₀ + t v₀ + ∫₀ᵗ (s-t)[γ ẋ(s) + A x(s)] ds` is the
  Volterra map recalled in `ext_def_4` (formula (26)).

  Two representational deviations, both stemming from the fact that the paper's
  formula for `Γ` uses `ẋ` while `Γ` is declared on the path space
  `C([0,T];H)`:

  * the map formalized here is the derivative-free *centered* form
    `centeredIntegralMap`, obtained from `Γ` by integrating the damping term by
    parts along paths with `y 0 = u₀` (`∫₀ᵗ (s-t) γ ẏ(s) ds = -γ ∫₀ᵗ (y s - u₀) ds`,
    which is the identity proved as `centered_solution_integral_identity` in
    `thm_8`).  On a genuine solution the two agree on `[0,T]`, which is the only
    place the fixed-point machinery of Theorems 7.1 and 7.8 uses it;
  * the path space is the set of *continuous* paths on `[0,T]` (the initial
    condition is built into the map), and the residual `‖y - Γ y‖` is taken
    pointwise on `[0,T]`; for a continuous `y` the residual is continuous as
    well, so this is equivalent to the paper's sup-norm reading — which is the
    form in which the consumers state their bounds (`thm_10`). -/

open Set MeasureTheory

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The derivative-free, centered Volterra form of the second-order Picard
  map.  On a differentiable path with `y 0 = u₀`, integration by parts turns
  the damping term in `integralMap` into the integral used here. -/
noncomputable def centeredIntegralMap {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (A : H → H) (γ : ℝ) (u₀ v₀ : H)
    (y : ℝ → H) (t : ℝ) : H :=
  u₀ + t • v₀ - γ • (∫ s in (0 : ℝ)..t, y s - u₀) +
    ∫ s in (0 : ℝ)..t, (s - t) • A (y s)

/-- Definition 7.5: the set `S^ε(μ) = S^ε(A_μ,u₀^μ,v₀^μ)` of
  `ε`-approximate solutions of `S(A_μ,u₀^μ,v₀^μ)`, i.e. the `ε`-fixed points of
  the Volterra map `Γ_{A_μ,u₀^μ,v₀^μ}`, on the paths that are continuous on
  `[0,T]` and whose residual
  `‖y t - Γ_{A_μ,u₀^μ,v₀^μ}(y)(t)‖` is at most `ε` for every `t ∈ [0,T]`.

  The paper's `x ∈ C¹([0,T];H)` and its sup-norm residual are discussed in the
  module docstring. -/
def def_10 {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : M → H → H) (γ : ℝ) (u₀ v₀ : M → H) (T ε : ℝ) (μ : M) : Set (ℝ → H) :=
  {y | ContinuousOn y (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖y t - centeredIntegralMap (A μ) γ (u₀ μ) (v₀ μ) y t‖ ≤ ε}

/-- The paper's notation `S^ε(μ)` for the set of `def_10`. -/
abbrev approxSolutions {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : M → H → H) (γ : ℝ) (u₀ v₀ : M → H) (T ε : ℝ) (μ : M) : Set (ℝ → H) :=
  def_10 A γ u₀ v₀ T ε μ

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
