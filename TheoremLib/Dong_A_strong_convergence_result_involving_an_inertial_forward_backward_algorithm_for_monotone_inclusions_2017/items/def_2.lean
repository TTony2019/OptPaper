import Mathlib.Tactic
import Foundation.Projection.BestApproximation
import Foundation.Hilbert.WeakConvergence

/-! Metric projections and the Kadec--Klee property used in Section 2. -/

recall isChebyshev_of_nonempty_isClosed_convex
recall eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
recall tendsto_iff_tendsto_weakly_and_tendsto_norm
