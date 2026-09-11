import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_4
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_8
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_5
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_thm_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_2

open scoped InnerProductSpace

open ERealFunction

open Filter Topology

private theorem linear_dry_friction_subgradient_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (phi : H -> ℝ) (r : ℝ)
    (hphi : ∀ x, phi x = r * ‖x‖) (hr : 0 < r) {q : H}
    (hq : q ∈ subdifferential phi 0) : ‖q‖ ≤ r := by
  by_cases hq0 : q = 0
  · simpa [hq0] using hr.le
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hineq : ‖q‖ ^ 2 ≤ r * ‖q‖ := by
    have hq' := hq q
    change (⟪q - 0, q⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi q : EReal) at hq'
    norm_cast at hq'
    simp [hphi, sub_zero] at hq'
    exact hq'
  nlinarith

/-- Theorem 5.1: the variable-metric Lasso trajectory inherits the IPAHDD
finite-length and finite-stopping conclusions from its envelope realization. -/
theorem IPAHDDLasso_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi fLam : H → ℝ) (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A Aadj : H → H) (M : H → H) (b : H)
    (normA h gamma beta lam r L : ℝ) (hdf : DryFriction phi)
    (alg : IPAHDDLasso phi.toEReal hdf.toEReal_mem_gammaZero G hG A Aadj M b normA lam h gamma beta)
    (p : H → H)
    (hphi : ∀ x, phi x = r * ‖x‖)
    (hr : 0 < r) (hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0)
    (hfLam : ContDiff ℝ 1 fLam)
    (hLip : HasLipschitzGradient (gradient fLam) L) (hL_nonneg : 0 ≤ L)
    (hCont : Continuous (gradient fLam)) (hbelow : ∃ c : ℝ, ∀ x, c ≤ fLam x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hsmooth : ∃ smooth : IPAHDD fLam phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta,
      smooth.x = alg.x)
    (hcomposite : ∀ x, ∃ u,
      u ∈ subdifferential G (p x) ∧
        gradient fLam x = Aadj (A (p x) - b) + u) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} => ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      (∃ u, u ∈ subdifferential G (p xInf) ∧
        ‖Aadj (A (p xInf) - b) + u‖ ≤ r) ∧
      (‖gradient fLam xInf‖ < r -> IsFinitelyConvergent alg.x) := by
  rcases hsmooth with ⟨smooth, hsmooth⟩
  obtain ⟨xInf, Ebase, hEbase, hfinite, hlim, hcritical, hlen, _⟩ :=
    IPAHDD_finiteLength_and_critical fLam phi h gamma beta L r hdf smooth
      hfLam hLip hL_nonneg hbelow hpositive hr hdf_r hgamma
  obtain ⟨u, hu, hgrad⟩ := hcomposite xInf
  have hnormgrad : ‖gradient fLam xInf‖ ≤ r := by
    have hsub : -gradient fLam xInf ∈ subdifferential phi 0 := hcritical
    simpa only [norm_neg] using
      linear_dry_friction_subgradient_norm_le phi r hphi hr hsub
  have hstationary : ‖Aadj (A (p xInf) - b) + u‖ ≤ r := by
    rw [← hgrad]
    exact hnormgrad
  refine ⟨xInf, Ebase, ?_, ?_, ?_, ?_, ⟨u, hu, hstationary⟩, ?_⟩
  · simpa [hsmooth] using hEbase
  · simpa [hsmooth] using hfinite
  · simpa [hsmooth] using hlim
  · simpa [hsmooth] using hlen
  · intro hgradstrict
    obtain ⟨kStop, hkStop⟩ := IPAHDD_geometric_and_finite fLam phi
      h gamma beta L r hdf smooth xInf hfLam hLip hL_nonneg hbelow hpositive hr
      hdf_r hgamma hlim |>.2 hgradstrict
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa [hsmooth] using hkStop)
