import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1

/-- The set of minimizers of the proximal objective; this is the paper's `J_λ y`.

This item uses the finite-valued specialization `f : H → ℝ`.  The source paper
allows `+∞` values; those are represented separately by `ObjectiveAssumptions`
and are not part of this real-valued algorithm interface. -/
def proximalPoints {H : Type*} [NormedAddCommGroup H] (f : H → ℝ) (lam : ℝ) (y : H) : Set H :=
  {p | 0 < lam ∧ IsMinOn (fun z => f z + ‖z - y‖ ^ 2 / (2 * lam)) Set.univ p}

/-- The parameter qualification in the paper's notation `J_λ`. -/
def IsProximalParameter (lam : ℝ) : Prop := 0 < lam
