import Mathlib

/-!
# Strongly convex function (gradient form)
A $\mathcal{C}^1$ function $f: H \to \mathbb{R}$ is said to be strongly convex
if there exists $M > 0$ such that:
$$\forall x, y \in H, \langle \nabla f(x) - \nabla f(y), x - y \rangle \geqslant M |x - y|^2.$$
Equivalently, there exists $M > 0$ such that:
$$\forall x, y \in H, f(x) \ge f(y) + \langle \nabla f(y), x - y \rangle + \frac{M}{2} |x-y|^2.$$
-/
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
/-- A C^1 function `f` is strongly convex with constant `M > 0` if
`⟨∇f(x) - ∇f(y), x - y⟩ ≥ M |x - y|^2` for all `x, y`. -/
def IsStronglyConvex (f : H → ℝ) (M : ℝ) : Prop :=
  M > 0 ∧ ContDiff ℝ 1 f ∧
    ∀ x y, inner ℝ (gradient f x - gradient f y) (x - y) ≥ M * ‖x - y‖^2
