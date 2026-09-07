import Mathlib.Tactic
import Foundation.Projection.BestApproximation

/-! Metric projection is provided by Foundation as `setValuedProjector`; uniqueness for nonempty
closed convex sets is provided by the recalled theorem. -/
recall setValuedProjector
recall isChebyshev_of_nonempty_isClosed_convex
