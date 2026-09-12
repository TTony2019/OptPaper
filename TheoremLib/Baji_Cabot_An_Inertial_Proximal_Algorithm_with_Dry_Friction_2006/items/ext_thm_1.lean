import Mathlib
import Foundation.SetValued.Basic
import Foundation.SetValued.MaximalMonotoneSum
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_1

/-!
# Sum of maximal monotone operators (Brézis Corollary 2.7)
Let $A, B: H \Rightarrow H$ be maximal monotone operators. If
$\operatorname{int}(\operatorname{dom} A) \cap \operatorname{dom} B \neq \emptyset$,
then $A + B$ is maximal monotone.
Cited from: H. Brézis, Opérateurs maximaux monotones dans les espaces de Hilbert
et équations d'évolution, Lecture Notes 5, North Holland, Amsterdam, 1972, Corollary 2.7.
It is the second regularity alternative of Bauschke--Combettes Corollary 25.5 with the
roles of `A` and `B` exchanged, so it is proved here from the migrated
`SetValuedOperator.Maximal.add_of_interior_dom_inter_dom_nonempty`.
-/
open SetValuedOperator
open scoped Pointwise
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- If `A` and `B` are maximal monotone and `int(dom A) ∩ dom B` is nonempty,
then `A + B` is maximal monotone (Brézis Corollary 2.7). -/
theorem sum_maximal_monotone (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    IsMaximalMonotone (A + B) := by
  exact (isMaximalMonotone_iff_maximal_isMonotone (A + B)).2
    (Maximal.add_of_interior_dom_inter_dom_nonempty
      ((isMaximalMonotone_iff_maximal_isMonotone A).1 hA)
      ((isMaximalMonotone_iff_maximal_isMonotone B).1 hB) hdom)
