import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.algo_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.thm_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_6

open scoped InnerProductSpace

open ERealFunction

/-- Corollary 2.5, in the IPAHDD formulation supplied by the proximal
specialization of the soft-threshold update. -/
theorem IPAHDD_softThreshold_finiteConvergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ)
    (h gamma beta r L : ℝ) (hdf : DryFriction phi)
    (alg : IPAHDD f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta) (hr : 0 < r)
    (hf : ContDiff ℝ 1 f) (hL : HasLipschitzGradient (gradient f) L)
    (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hdf_r : Metric.ball (0 : H) r ⊆ subdifferential phi 0) :
    ∃ xInf, HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      IsDryFrictionCritical phi f xInf ∧
      (let q := 1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L));
        (-gradient f xInf ∈ interior (subdifferential phi 0) →
          0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
            ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
            ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
        (‖gradient f xInf‖ < r → IsFinitelyConvergent alg.x)) := by
  rcases hpositive with ⟨hh, hg, hb⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  obtain ⟨xInf, E1, hE1, hfinite, hlimit, hcritical, hlength, hacc⟩ :=
    IPAHDD_finiteLength_and_critical f phi h gamma beta L r hdf alg hf hL hL_nonneg
      hbelow ⟨hh, hg, hb⟩ hr hdf_r hgamma
  refine ⟨xInf, hfinite, hlimit, hcritical, ?_⟩
  dsimp
  obtain ⟨hgeometric, hstopping⟩ :=
    IPAHDD_geometric_and_finite f phi h gamma beta L r hdf alg xInf hf hL hL_nonneg
      hbelow ⟨hh, hg, hb⟩ hr hdf_r hgamma hlimit
  constructor
  · exact hgeometric
  · intro hmargin
    obtain ⟨kStop, hstop⟩ := hstopping hmargin
    exact eventually_constant_of_eventual_successor_eq alg.x kStop hstop
