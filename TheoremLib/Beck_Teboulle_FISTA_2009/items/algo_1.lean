import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sqrt
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_5
import TheoremLib.Beck_Teboulle_FISTA_2009.items.def_7

open scoped RealInnerProductSpace

/-- FISTA with constant stepsize, equations (4.1)--(4.3).

The parameter `Lf` is the paper's fixed value `L = L(f)`.  The sequence is indexed as in
the paper: `y 1 = x 0`, `t 1 = 1`, and the first proximal step produces `x 1`. -/
structure FISTAConstantStepsize {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (Lf : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) where
  x : ℕ → EuclideanSpace ℝ (Fin n)
  y : ℕ → EuclideanSpace ℝ (Fin n)
  t : ℕ → ℝ
  x_zero : x 0 = x0
  y_one : y 1 = x0
  t_one : t 1 = 1
  proximal_step : ∀ k : ℕ, 1 ≤ k → IsProxPoint f g Lf (y k) (x k)
  t_update : ∀ k : ℕ, 1 ≤ k →
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ 2)) / 2
  y_update : ∀ k : ℕ, 1 ≤ k →
    y (k + 1) = x k + ((t k - 1) / t (k + 1)) • (x k - x (k - 1))

namespace FISTAConstantStepsize

/-- In the paper's indexing, the constant-step proximal update maps `y k` to `x k`.
This lemma only reindexes the structure field so that it can be used with sums starting
at `k = 0`. -/
theorem proximal_step_at {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTAConstantStepsize f g Lf x0)
    (k : ℕ) : IsProxPoint f g Lf (A.y (k + 1)) (A.x (k + 1)) := by
  exact A.proximal_step (k + 1) (by omega)

end FISTAConstantStepsize
