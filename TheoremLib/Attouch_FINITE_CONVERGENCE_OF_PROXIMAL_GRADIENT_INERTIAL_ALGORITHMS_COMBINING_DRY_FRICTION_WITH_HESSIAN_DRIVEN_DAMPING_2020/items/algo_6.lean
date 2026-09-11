import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

/-- The variable version of the extrapolated IPAHDD-N scheme. -/
structure IPAHDDNVar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (prox : ℝ → H → H) (h gamma beta : ℝ) where
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  extrapolate (k : ℕ) : y k = x (k + 1) + (1 / (h * (1 + h * gamma))) • (x (k + 1) - x k)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h • prox (h / (1 + h * gamma))
    (y k - x (k + 1) - (beta / (1 + h * gamma)) •
      (gradient f (x (k + 1)) - gradient f (x k)) - (h / (1 + h * gamma)) • gradient f (y k))
