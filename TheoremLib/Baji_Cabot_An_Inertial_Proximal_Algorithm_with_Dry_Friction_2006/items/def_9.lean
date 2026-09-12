import Mathlib

/-!
# Function of class $\mathcal{C}^{1,1}$
A function $f: H \to \mathbb{R}$ is said to be of class $\mathcal{C}^{1,1}$
if it is of class $\mathcal{C}^1$ and if its gradient $\nabla f$ is locally
Lipschitz on $H$.
-/
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- A function is of class C^{1,1} if it is C^1 and its gradient is locally Lipschitz. -/
def IsC11 (f : H → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ LocallyLipschitz (gradient f)
