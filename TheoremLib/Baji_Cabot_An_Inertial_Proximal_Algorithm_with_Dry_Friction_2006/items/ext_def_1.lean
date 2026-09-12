import Mathlib.Tactic
import Foundation.SetValued.Monotone

/-!
# Maximal monotone operator
A set-valued operator $A: H \Rightarrow H$ on a Hilbert space $H$ is monotone if
$\forall (x,u), (y,v) \in \operatorname{gra} A$, $\langle u - v, x - y \rangle \geqslant 0$.
It is maximal monotone if its graph is not properly contained in the graph of any
other monotone operator. The domain is
$\operatorname{dom} A = \{x \in H \mid A(x) \neq \emptyset\}$.
-/
open SetValuedOperator
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- A set-valued operator `T : H ⇉ H` is monotone if for all `x, y` and all
`u ∈ T x`, `v ∈ T y`, we have `inner ℝ (u - v) (x - y) ≥ 0`. -/
recall SetValuedOperator.IsMonotone
export SetValuedOperator (IsMonotone)
/-- A set-valued operator `A` is maximal monotone if it is monotone and its graph
is maximal among graphs of monotone operators (i.e., not properly contained in the
graph of any other monotone operator). -/
recall SetValuedOperator.IsMaximalMonotone
export SetValuedOperator (IsMaximalMonotone)
