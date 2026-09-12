import Mathlib
import Foundation.SetValued.Basic

/-!
# Function $\Phi_A$
For a monotone operator $A: H \Rightarrow H$, the function $\Phi_A$ is defined by:
$$\Phi_A(x) := \inf_{y \in A(x)} \langle y, x \rangle.$$
-/
open SetValuedOperator
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The function `Φ_A(x) = inf_{y ∈ A(x)} ⟨y, x⟩`. -/
noncomputable def PhiA (A : SetValuedOperator H H) (x : H) : EReal :=
  sInf ((fun y : H => (inner ℝ y x : EReal)) '' A x)
