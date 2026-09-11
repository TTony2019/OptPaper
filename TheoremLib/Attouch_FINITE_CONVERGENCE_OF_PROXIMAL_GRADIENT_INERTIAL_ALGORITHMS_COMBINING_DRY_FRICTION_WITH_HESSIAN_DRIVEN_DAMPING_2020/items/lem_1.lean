import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_lem_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3

open scoped InnerProductSpace

open ERealFunction
open Pointwise

/-- Lemma 1.2: the dry-friction ball makes the proximal velocity vanish. -/
theorem proximal_eq_zero_of_norm_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (phi : H → ℝ) (r lam : ℝ) (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ phi) (hcontinuous : Continuous phi) (_hr : 0 < r)
    (hball : Metric.closedBall (0 : H) r ⊆ subdifferential phi 0)
    (x : H) (hx : ‖x‖ ≤ lam * r) :
    ERealFunction.scaledProximityOperator phi.toEReal
      (toEReal_mem_gammaZero_of_continuous_convexOn_univ hcontinuous hconvex)
      ⟨lam, hlam⟩ x = 0 := by
  have hΓ : phi.toEReal ∈ Γ₀(H) :=
    toEReal_mem_gammaZero_of_continuous_convexOn_univ hcontinuous hconvex
  have hscaled_norm : ‖lam⁻¹ • x‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam), inv_mul_le_iff₀ hlam]
    simpa [mul_comm] using hx
  have hmem : lam⁻¹ • x ∈ subdifferential phi 0 :=
    hball (mem_closedBall_zero_iff.mpr hscaled_norm)
  rw [ERealFunction.scaledProximityOperator, eq_comm]
  refine (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
    (f := (⟨lam, hlam⟩ : PosReal) • phi.toEReal)
    (ERealFunction.smul_mem_gammaZero phi.toEReal hΓ ⟨lam, hlam⟩) x 0).2 ?_
  rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
  change x - 0 ∈ (lam : ℝ) • ((∂ (Function.toEReal phi)) 0)
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  simpa [sub_zero] using hmem
