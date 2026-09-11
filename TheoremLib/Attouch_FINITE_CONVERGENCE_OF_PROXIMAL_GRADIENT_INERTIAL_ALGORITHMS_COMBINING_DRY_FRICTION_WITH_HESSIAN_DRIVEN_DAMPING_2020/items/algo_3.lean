import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

/-- The variable-friction IPAHDD iteration. -/
structure IPAHDDVar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (prox : ℝ → H → H) (h gamma beta : ℝ) where
  x : ℕ → H
  initial0 : H
  initial1 : H
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  update (k : ℕ) : x (k + 2) = x (k + 1) + h • prox h
    (((1 - h * gamma) / h) • (x (k + 1) - x k) -
      beta • (gradient f (x (k + 1)) - gradient f (x k)) - h • gradient f (x (k + 1)))
