import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

/-- The class `C^{1,1}` of continuously differentiable functions with Lipschitz continuous
gradient. A function `f : ℝⁿ → ℝ` is of type `C^{1,1}` if it is continuously differentiable
and its gradient is `L`-Lipschitz with `L > 0`. This matches the paper's definition in §2.2. -/
structure IsC11 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : outParam ℝ) : Prop where
  hL_pos : 0 < L
  contDiff : ContDiff ℝ 1 f
  grad_lipschitz : LipschitzWith (Real.toNNReal L) (fun x : EuclideanSpace ℝ (Fin n) => gradient f x)
