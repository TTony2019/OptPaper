import Mathlib

namespace LorenzPock

/-- A bounded self-adjoint positive-definite metric operator. -/
structure PositiveDefiniteMetric (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  toContinuousLinearMap : H →L[ℝ] H
  self_adjoint : ∀ u v, inner ℝ (toContinuousLinearMap u) v = inner ℝ u (toContinuousLinearMap v)
  positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (toContinuousLinearMap u) u

/-- The quadratic form induced by a bounded, self-adjoint, positive-definite operator. -/
def weightedInner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : PositiveDefiniteMetric H) (u v : H) : ℝ :=
  inner ℝ (P.toContinuousLinearMap u) v

/-- The squared quantity `‖u‖²_P = ⟪P u, u⟫`. -/
def weightedNormSq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : PositiveDefiniteMetric H) (u : H) : ℝ :=
  weightedInner P u u

end LorenzPock
