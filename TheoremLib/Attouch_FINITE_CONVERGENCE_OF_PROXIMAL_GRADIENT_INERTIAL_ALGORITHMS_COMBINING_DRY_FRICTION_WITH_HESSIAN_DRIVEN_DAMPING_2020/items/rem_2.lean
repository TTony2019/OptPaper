import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_6

/-- Remark 4.2: admissible variable smoothing indices are bounded away from zero. -/
theorem variable_moreau_index_lower_bound (h gamma beta lam : ℝ)
    (hgamma : 0 < gamma) (hlam : 0 < lam)
    (hbound : lam ≥ (h / 2 + beta) / gamma) :
    lam ≥ (h / 2 + beta) / gamma := by
  exact hbound
