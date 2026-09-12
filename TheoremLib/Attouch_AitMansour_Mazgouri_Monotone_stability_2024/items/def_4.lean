import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1

open scoped RealInnerProductSpace

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Condition `(C₁)` of Section 3: each `A μ` is `α_μ`-cocoercive on `H`
  (equivalently, `α_μ‖A_μ u - A_μ v‖² ≤ ⟨A_μ u - A_μ v, u - v⟩`), i.e.
  `A μ` is `1/α_μ`-Lipschitz and `1/α_μ`-cocoercive, with a modulus allowed to
  depend on the parameter `μ`. -/
def def_4_C₁ {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) : Prop :=
  ∀ μ ∈ V, ∃ α : ℝ, 0 < α ∧ ∀ u v : H,
    α * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v)

/-- Condition `(C₂)` of Section 3: the map `μ ↦ A_μ u` is Hölder continuous on
  the parameter set with uniform modulus `θ₁ > 0` and exponent
  `θ₂ ∈ ]0,1]`. -/
def def_4_C₂ {H M : Type*} [NormedAddCommGroup H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) : Prop :=
  ∃ θ₁ θ₂ : ℝ, 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V →
    ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂

/-- Conditions `(C₁)` and `(C₂)` of Section 3, kept as the bundled form for
  consumers that use both at once.  The two conditions are available separately
  as `def_4_C₁` and `def_4_C₂`, so that each can be cited on its own, as in the
  paper (where e.g. Corollary 4.1 only needs `(C₁)`).

  The parameter set is an arbitrary `V : Set M`: the paper writes
  `𝒱(μ̄)`, the reference neighbourhood of `μ̄`, which is what the call sites
  supply (each theorem assuming `V ∈ 𝓝 μ̄`). -/
def def_4 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup M]
    (V : Set M) (A : M → H → H) : Prop :=
  def_4_C₁ V A ∧ def_4_C₂ V A

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
