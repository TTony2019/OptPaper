import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.prop_4

/-!
# Normal cone stability for convex polyhedra
Let $C \subset H$ be a convex polyhedron and $\overline{x} \in C$.
Then there exists a neighbourhood $V$ of $\overline{x}$ such that for all $x \in V$,
$N_C(x) \subset N_C(\overline{x})$.
Cited from: known property of convex polyhedra
(see e.g. R.T. Rockafellar and R. Wets, Variational Analysis, Springer, 1998).
-/
open Set
open scoped Topology
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- For a convex polyhedron `C` and `xbar ∈ C`, there exists a neighbourhood `V` of `xbar`
such that for all `x ∈ V`, `N_C(x) ⊆ N_C(xbar)`. -/
theorem normalCone_stability_convexPolyhedron (C : Set H) (hC : ConvexPolyhedron C) (xbar : H)
    (hxbar : xbar ∈ C) : ∃ (V : Set H), V ∈ 𝓝 xbar ∧ ∀ x ∈ V, normalCone C x ⊆ normalCone C xbar := by
  sorry
