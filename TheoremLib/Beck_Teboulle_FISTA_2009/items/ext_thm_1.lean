import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_3
import TheoremLib.Beck_Teboulle_FISTA_2009.items.lem_1

open scoped RealInnerProductSpace

/-- External theorem: The Descent Lemma (quadratic upper bound for `C^{1,1}` functions).

Let `f : ℝⁿ → ℝ` be continuously differentiable with Lipschitz continuous gradient
and Lipschitz constant `L(f)`. Then for any `L ≥ L(f)`,
`f(x) ≤ f(y) + ⟨∇f(y), x - y⟩ + (L/2)‖x - y‖²` for every `x, y ∈ ℝⁿ`.

Cited from: J. M. Ortega and W. C. Rheinboldt, Iterative Solution of Nonlinear
Equations in Several Variables, SIAM, 2000; and D. P. Bertsekas, Nonlinear
Programming, 2nd ed., Athena Scientific, 1999. -/
theorem descent_lemma_C11 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {Lf L : ℝ}
    (hf : IsC11 f Lf) (hL : Lf ≤ L) (x y : EuclideanSpace ℝ (Fin n)) :
    f x ≤ f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 :=
  quadratic_upper_bound_C11 hf hL x y
