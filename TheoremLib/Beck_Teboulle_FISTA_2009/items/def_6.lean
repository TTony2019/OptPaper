import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5

open scoped RealInnerProductSpace

/-- The quadratic approximation `Q_L(x, y)` of `F(x) := f(x) + g(x)` at a given point `y`:
`Q_L(x, y) := f(y) + ⟨∇f(y), x - y⟩ + (L/2)‖x - y‖² + g(x)`. (Equation 2.5) -/
noncomputable def quadraticApprox {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x
