import Mathlib

open scoped InnerProductSpace Gradient

namespace Nesterov1983

/-- A real-valued function on a Hilbert space which is continuously differentiable
and whose gradient is `L`-Lipschitz. -/
structure IsC11 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  contDiff : ContDiff ℝ 1 f
  lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- A `C^{1,1}` function admits `gradient f x` as its gradient at every point. -/
theorem IsC11.hasGradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (h : IsC11 f L) (x : E) :
    HasGradientAt f (gradient f x) x :=
  h.contDiff.differentiable_one.differentiableAt.hasGradientAt

end Nesterov1983
