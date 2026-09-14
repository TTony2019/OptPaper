import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2

open ERealFunction

/-- Distance from a point to a set, as the infimum of the pointwise distances. -/
noncomputable def residualDistance {H : Type*} [NormedAddCommGroup H] (x : H) (S : Set H)
    : ℝ := Metric.infDist x S

/-- The residual of the convex subdifferential at a point. -/
noncomputable def subdifferentialResidual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (g : H → ℝ) (x : H) : ℝ :=
  residualDistance (0 : H) (subdifferential (fun y => (g y : EReal)) x)

/-- The paper's residual notation is used only for nonempty sets. -/
theorem residualDistance_defined_for_nonempty {H : Type*} [NormedAddCommGroup H]
    (x : H) (S : Set H) (hS : S.Nonempty) :
    residualDistance x S = sInf {r | ∃ s ∈ S, r = ‖x - s‖} := by
  have himage : ((fun s => dist x s) '' S) = {r | ∃ s ∈ S, r = ‖x - s‖} := by
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp [dist_eq_norm]⟩
    · rintro ⟨s, hs, hrs⟩
      refine ⟨s, hs, ?_⟩
      simpa [dist_eq_norm] using hrs.symm
  rw [residualDistance,
    ← (Metric.isGLB_infDist (x := x) hS).csInf_eq (hS.image _), himage]
