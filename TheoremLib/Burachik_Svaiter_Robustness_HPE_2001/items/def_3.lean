import Foundation.Convex.NormalCone
import Mathlib.Tactic

/-! The normality operator `N_C` of the paper is Foundation's normal cone
(Bauschke--Combettes, Definition 6.38 (2)), `Set.normalCone C : H → Set H`: the if-then-else
presentation `z ↦ if z ∈ C then {w | ∀ u ∈ C, ⟪w, z - u⟫ ≥ 0} else ∅` used in the paper is
`Set.normalCone_eq`, and the pointwise variational form is `Set.mem_normalCone_iff_forall`. -/
recall Set.normalCone
recall Set.mem_normalCone_iff_forall
