import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

/-- IPAHDD applied to a nonsmooth objective through its Moreau proximal map. -/
structure IPAHDDNonsmooth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta lam : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  lam_pos : 0 < lam
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  aux (k : ℕ) : y k = (1 / (1 + h * gamma)) •
    (((lam - beta * h) / (lam * h)) • (x (k + 1) - x k) +
      (beta / lam) • (ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x (k + 1)) -
        ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x k)) -
      (h / lam) • (x (k + 1) -
        ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x (k + 1))))
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩ (y k)
