import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

private theorem subgradient_ball_implies_linear_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) {R : ℝ} (hzero : phi 0 = 0) (hR : 0 < R)
    (hball : Metric.ball (0 : H) R ⊆ subdifferential phi 0) :
    ∀ xi : H, phi xi ≥ (R / 2) * ‖xi‖ := by
  intro xi
  by_cases hxi : xi = 0
  · simp [hxi, hzero]
  have hnorm : ‖xi‖ ≠ 0 := norm_ne_zero_iff.mpr hxi
  let p : H := (R / 2) • ((‖xi‖)⁻¹ • xi)
  have hp_norm : ‖p‖ < R := by
    dsimp [p]
    rw [norm_smul, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by linarith), Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg xi)]
    field_simp
    linarith
  have hp : p ∈ subdifferential phi 0 := hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hp_norm)
  have hinner : inner ℝ p xi = (R / 2) * ‖xi‖ := by
    dsimp [p]
    rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [map_inv₀, starRingEnd_apply, star_trivial]
    field_simp
  have hp' := hp xi
  change (⟪xi - 0, p⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi xi : EReal) at hp'
  norm_cast at hp'
  simp [hzero] at hp'
  rw [real_inner_comm] at hp'
  rw [← hinner]
  exact hp'

private theorem linear_lower_bound_implies_subgradient_ball
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) {R : ℝ} (hzero : phi 0 = 0) (hR : 0 < R)
    (hco : ∀ xi : H, phi xi ≥ R * ‖xi‖) :
    Metric.ball (0 : H) (R / 2) ⊆ subdifferential phi 0 := by
  intro g hg
  have hg_norm : ‖g‖ < R / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hg
    simpa using hg
  change ∀ xi : H, (⟪xi - 0, g⟫_ℝ : EReal) + (phi 0 : EReal) ≤ (phi xi : EReal)
  intro xi
  norm_cast
  have hgr : ‖g‖ ≤ R := le_of_lt (lt_trans hg_norm (by linarith))
  have hmul : ‖g‖ * ‖xi‖ ≤ R * ‖xi‖ :=
    mul_le_mul_of_nonneg_right hgr (norm_nonneg xi)
  have hinter : inner ℝ g xi ≤ R * ‖xi‖ :=
    le_trans (real_inner_le_norm g xi) hmul
  simpa [hzero, real_inner_comm] using le_trans hinter (hco xi)

/-- Lemma 1.1: the ball, coercivity, and dual-support formulations of dry friction. -/
theorem dryFriction_equivalences {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (_hconvex : ConvexOn ℝ Set.univ phi) (_hcontinuous : Continuous phi)
    (_hmin : ∀ x, phi 0 ≤ phi x) (hzero : phi 0 = 0) :
    (((0 : H) ∈ interior (subdifferential phi 0)) ↔
      (∃ r > 0, Metric.ball (0 : H) r ⊆ subdifferential phi 0)) ∧
    ((∃ r > 0, Metric.ball (0 : H) r ⊆ subdifferential phi 0) ↔
      (∃ r > 0, ∀ xi : H, phi xi ≥ r * ‖xi‖)) ∧
    ((∃ r > 0, ∀ xi : H, phi xi ≥ r * ‖xi‖) ↔
      (∃ r > 0, ∀ g : H, ‖g‖ ≤ r → ∀ xi : H, inner ℝ g xi ≤ phi xi)) := by
  constructor
  · constructor
    · intro h
      rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h) with ⟨r, hr, hball⟩
      exact ⟨r, hr, hball⟩
    · rintro ⟨r, hr, hball⟩
      exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, hball⟩)
  constructor
  · constructor
    · rintro ⟨R, hR, hball⟩
      exact ⟨R / 2, by linarith, subgradient_ball_implies_linear_lower_bound phi hzero hR hball⟩
    · rintro ⟨R, hR, hco⟩
      exact ⟨R / 2, by linarith, linear_lower_bound_implies_subgradient_ball phi hzero hR hco⟩
  constructor
  · rintro ⟨R, hR, hco⟩
    refine ⟨R / 2, by linarith, ?_⟩
    intro g hg xi
    have hgr : ‖g‖ ≤ R := le_trans hg (by linarith)
    exact le_trans (le_trans (real_inner_le_norm g xi)
      (mul_le_mul_of_nonneg_right hgr (norm_nonneg xi))) (hco xi)
  · rintro ⟨R, hR, hdual⟩
    refine ⟨R / 2, by linarith, ?_⟩
    intro xi
    by_cases hxi : xi = 0
    · simp [hxi, hzero]
    have hnorm : ‖xi‖ ≠ 0 := norm_ne_zero_iff.mpr hxi
    let g : H := (R / 2) • ((‖xi‖)⁻¹ • xi)
    have hg_norm : ‖g‖ ≤ R := by
      dsimp [g]
      rw [norm_smul, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (by linarith), Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg xi)]
      field_simp
      linarith
    have hinner : inner ℝ g xi = (R / 2) * ‖xi‖ := by
      dsimp [g]
      rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [map_inv₀, starRingEnd_apply, star_trivial]
      field_simp
    simpa [hinner] using hdual g hg_norm xi
