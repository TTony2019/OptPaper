import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_lem_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

open scoped InnerProductSpace

open ERealFunction

/-- Lemma 1.2: the dry-friction ball makes the proximal velocity vanish. -/
theorem proximal_eq_zero_of_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (r lam : ℝ) (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ phi) (hcontinuous : Continuous phi)
    (P : ProximalMapping phi lam hlam hconvex hcontinuous.lowerSemicontinuous) (_hr : 0 < r)
    (hball : Metric.closedBall (0 : H) r ⊆ subdifferential phi 0)
    (x : H) (hx : ‖x‖ ≤ lam * r) : P.toFun x = 0 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hscaled_norm : ‖lam⁻¹ • x‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), inv_mul_le_iff₀ hlam]
    simpa [mul_comm] using hx
  have hscaled_mem : lam⁻¹ • x ∈ subdifferential phi 0 :=
    hball (mem_closedBall_zero_iff.mpr hscaled_norm)
  have hprox_zero : IsProximalPoint phi lam x 0 := by
    rw [IsProximalPoint]
    refine ⟨hlam, ?_⟩
    simpa [sub_zero] using hscaled_mem
  have hunique : (0 : H) = P.toFun x := P.unique x 0 hprox_zero
  exact hunique.symm
