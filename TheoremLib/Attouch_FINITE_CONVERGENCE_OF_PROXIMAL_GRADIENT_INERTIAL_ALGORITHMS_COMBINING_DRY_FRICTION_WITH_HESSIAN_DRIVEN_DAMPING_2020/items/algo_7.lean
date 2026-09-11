import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

/-- IPAHDD applied to a nonsmooth objective through its Moreau proximal map. -/
structure IPAHDDNonsmooth {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (proxF proxPhi : ℝ → H → H) (h gamma beta lam : ℝ) where
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  aux (k : ℕ) : y k = (1 / (1 + h * gamma)) •
    (((lam - beta * h) / (lam * h)) • (x (k + 1) - x k) +
      (beta / lam) • (proxF lam (x (k + 1)) - proxF lam (x k)) -
      (h / lam) • (x (k + 1) - proxF lam (x (k + 1))))
  update (k : ℕ) : x (k + 2) = x (k + 1) + h • proxPhi (h / (1 + h * gamma)) (y k)
