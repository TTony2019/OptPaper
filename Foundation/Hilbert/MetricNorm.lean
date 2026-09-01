import Mathlib

/-!
# Variable-metric norms

`metricNorm`: the norm `‖x‖_M = √⟨Mx, x⟩` induced by a positive self-adjoint
operator `M`, and the metric Moreau envelope `f_λ^M` computed in that norm.

Promoted from
`TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/ext_def_7` and
`TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/def_5`.
-/

open scoped InnerProductSpace

/-- The `M`-norm of `x`, the square root of the quadratic form `⟨Mx, x⟩`, for a
positive self-adjoint operator `M`. -/
noncomputable def metricNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H) (x : H) : ℝ := Real.sqrt (inner ℝ (M x) x)

/-- The metric Moreau envelope `f_λ^M(x) = min_{ξ ∈ H} {f(ξ) + ‖x-ξ‖_M²/(2λ)}` with
`λ > 0` and `M` self-adjoint and **strictly** positive definite (`⟨M u, u⟩ > 0` for
`u ≠ 0`).  This is a definition, not a theorem — the envelope is the infimum over
all `ξ ∈ H`. -/
noncomputable def metricMoreauEnvelope {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : H →L[ℝ] H) (f : H → ℝ) (lam : ℝ) (x : H)
    (_hlam : 0 < lam)
    (_hMselfadjoint : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v))
    (_hMposdef : ∀ u, u ≠ 0 → 0 < inner ℝ (M u) u) : ℝ :=
  sInf {f ξ + metricNorm M (x - ξ) ^ 2 / (2 * lam) | ξ : H}
