import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.Extr
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_6

open Set
open scoped RealInnerProductSpace

/-- The predicate `IsProxPoint f g L y z` states that `z` is a minimizer of the
quadratic approximation `Q_L(·, y)`. This is the relational version of the paper's
proximal operator `p_L(y) := argmin_{x} Q_L(x, y)`. (Equation 2.6) -/
def IsProxPoint {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsMinOn (fun x => quadraticApprox f g L x y) univ z
