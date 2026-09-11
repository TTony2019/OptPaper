import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_4
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

/-- IPAHDD-Lasso, parameterized by its computed smooth gradient sequence. -/
structure IPAHDDLasso {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → Set.Ioi (⊥ : EReal)) (hΦ : Φ ∈ Γ₀(H))
    (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A Aadj M : H → H) (b : H) (normA lam h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  lam_pos : 0 < lam
  x : ℕ → H
  y : ℕ → H
  z : ℕ → H
  initial0 : H
  initial1 : H
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  metric : M = fun v ↦ v - lam • Aadj (A v)
  lam_norm_sq : 0 < lam * normA ^ 2 ∧ lam * normA ^ 2 < 1
  z_def (k : ℕ) : z k = (1 / lam) • M (x (k + 1) -
    ERealFunction.scaledProximityOperator G hG ⟨lam, lam_pos⟩
      (x (k + 1) - lam • Aadj (A (x (k + 1)) - b)))
  aux (k : ℕ) (hk : 1 ≤ k) : y k = (1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
    (beta / (1 + h * gamma)) • (z k - z (k - 1)) - (h / (1 + h * gamma)) • z k
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator Φ hΦ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩ (y k)
