import Mathlib.Analysis.InnerProductSpace.PiL2
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7

/-- ISTA with constant stepsize, equation (3.1).

The paper fixes `L = L(f)` and computes `x_k = p_L(x_{k-1})` for every `k ≥ 1`. -/
structure ISTAConstantStepsize {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  x : ℕ → EuclideanSpace ℝ (Fin n)
  x_zero : x 0 = x0
  proximal_step : ∀ k : ℕ, 1 ≤ k → IsProxPoint f g Lf (x (k - 1)) (x k)

namespace ISTAConstantStepsize

/-- Reindexed form of the fixed-step update, useful for sums beginning at `0`. -/
theorem proximal_step_at {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTAConstantStepsize f g Lf x0)
    (k : ℕ) : IsProxPoint f g Lf (A.x k) (A.x (k + 1)) := by
  exact A.proximal_step (k + 1) (by omega)

end ISTAConstantStepsize
