import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_1

/-- The finite-dimensional Euclidean vector space `ℝⁿ`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The shrinkage (soft-thresholding) operator `T_α : ℝⁿ → ℝⁿ` defined componentwise:
`T_α(x)_i = (|x_i| - α)⁺ · sgn(x_i)`. -/
noncomputable def shrinkageOperator {n : ℕ} (α : ℝ) (x : Vec n) : Vec n :=
  WithLp.toLp 2 (fun i : Fin n =>
    positivePart (|x i| - α) * Real.sign (x i))
