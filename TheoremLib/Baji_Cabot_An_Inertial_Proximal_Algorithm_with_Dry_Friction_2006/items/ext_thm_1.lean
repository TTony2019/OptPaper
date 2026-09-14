import Foundation.SetValued.MaximalMonotoneSum

open SetValuedOperator
open scoped Pointwise
open scoped Topology

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
