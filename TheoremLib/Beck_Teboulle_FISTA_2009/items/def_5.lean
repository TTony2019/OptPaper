import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Extr
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_3

open Set

/-- The general convex optimization model (Problem P):
`min {F(x) := f(x) + g(x) : x ∈ ℝⁿ}`, where:
- `g` is a continuous convex function (possibly nonsmooth),
- `f` is a smooth convex function of type `C^{1,1}` with constant `L`,
- The problem is solvable (`X* ≠ ∅`).

This bundles the standing assumptions of the paper (§2.2). -/
structure ProblemP {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : outParam ℝ) : Prop where
  smooth_f : IsC11 f L
  convex_f : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) f
  continuous_g : Continuous g
  convex_g : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n))) g
  solution_nonempty : ∃ xStar, IsMinOn (fun x => f x + g x) univ xStar

/-- The composite objective `F(x) = f(x) + g(x)`. -/
def compositeObjective {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + g x

/-- The set of optimal solutions `X*`. -/
def solutionSet {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | IsMinOn (compositeObjective f g) univ x}
