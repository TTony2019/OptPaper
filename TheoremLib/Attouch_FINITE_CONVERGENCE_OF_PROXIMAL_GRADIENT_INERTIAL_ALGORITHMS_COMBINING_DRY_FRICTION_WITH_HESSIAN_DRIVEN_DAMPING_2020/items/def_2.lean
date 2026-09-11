import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

noncomputable section

/-- The Moreau envelope, represented by the infimum of the proximal objective. -/
def moreauEnvelope {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (lam : ℝ) (_hlam : 0 < lam)
    (_hmin : ∀ x : H, ∃ xi : H, ∀ eta : H,
      f xi + ‖x - xi‖ ^ 2 / (2 * lam) ≤ f eta + ‖x - eta‖ ^ 2 / (2 * lam)) (x : H) : ℝ :=
  sInf (Set.range fun xi ↦ f xi + ‖x - xi‖ ^ 2 / (2 * lam))
