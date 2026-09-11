import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_2
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_4

open scoped InnerProductSpace

open ERealFunction

private theorem proximal_residual_mem_subgradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) {lam : ℝ} (hlam : 0 < lam) {x p : H}
    (hp : IsProximalPoint f lam x p) :
    (1 / lam) • (x - p) ∈ subdifferential f p := by
  -- `IsProximalPoint` is now the subgradient-form `0 < lam ∧
  -- (lam⁻¹ • (x - p)) ∈ subdifferential (fun z => (f z : EReal)) p`,
  -- whose membership part is the global affine-minorant inequality
  -- `∀ y, ⟪y - p, lam⁻¹ • (x - p)⟫_ℝ + (f p : EReal) ≤ (f y : EReal)`
  -- (no witness/equation component anymore).
  rcases hp with ⟨hlam', hmem⟩
  simpa [one_div, mem_subdifferential_iff] using hmem

private theorem proximal_firm_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x y : H) :
    ‖P.toFun x - P.toFun y‖ ^ 2 ≤
      @inner ℝ H _ (x - y) (P.toFun x - P.toFun y) := by
  have hx := proximal_residual_mem_subgradient f hlam (P.optimality x)
  have hy := proximal_residual_mem_subgradient f hlam (P.optimality y)
  rw [subdifferential] at hx hy
  have h1 := hx (P.toFun y)
  have h2 := hy (P.toFun x)
  have hmono : 0 ≤ @inner ℝ H _
      ((1 / lam) • (x - P.toFun x) - (1 / lam) • (y - P.toFun y))
      (P.toFun x - P.toFun y) := by
    change (⟪P.toFun y - P.toFun x, (1 / lam) • (x - P.toFun x)⟫_ℝ : EReal) +
        (f (P.toFun x) : EReal) ≤ (f (P.toFun y) : EReal) at h1
    change (⟪P.toFun x - P.toFun y, (1 / lam) • (y - P.toFun y)⟫_ℝ : EReal) +
        (f (P.toFun y) : EReal) ≤ (f (P.toFun x) : EReal) at h2
    norm_cast at h1 h2
    rw [show P.toFun y - P.toFun x = -(P.toFun x - P.toFun y) by abel,
      inner_neg_left, real_inner_comm] at h1
    rw [real_inner_comm] at h2
    rw [inner_sub_left]
    linarith
  have hinv : 0 < 1 / lam := one_div_pos.mpr hlam
  have h' : 0 ≤ @inner ℝ H _ ((x - y) - (P.toFun x - P.toFun y))
      (P.toFun x - P.toFun y) := by
    rw [show (1 / lam) • (x - P.toFun x) - (1 / lam) • (y - P.toFun y) =
        (1 / lam) • ((x - y) - (P.toFun x - P.toFun y)) by module,
      inner_smul_left, starRingEnd_apply, star_trivial] at hmono
    nlinarith
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h'
  exact sub_nonneg.mp h'

private theorem proximal_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x y : H) :
    ‖P.toFun x - P.toFun y‖ ≤ ‖x - y‖ := by
  have hfirm := proximal_firm_nonexpansive f hconvex hlsc hlam P x y
  have hcs := real_inner_le_norm (x - y) (P.toFun x - P.toFun y)
  have hp : 0 ≤ ‖P.toFun x - P.toFun y‖ := norm_nonneg _
  have hx : 0 ≤ ‖x - y‖ := norm_nonneg _
  nlinarith

private theorem proximal_residual_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x y : H) :
    ‖(1 / lam) • (x - P.toFun x) - (1 / lam) • (y - P.toFun y)‖ ≤
      (1 / lam) * ‖x - y‖ := by
  have hfirm := proximal_firm_nonexpansive f hconvex hlsc hlam P x y
  have hsq : ‖(x - P.toFun x) - (y - P.toFun y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [show (x - P.toFun x) - (y - P.toFun y) =
        (x - y) - (P.toFun x - P.toFun y) by module, norm_sub_sq_real]
    nlinarith [sq_nonneg ‖P.toFun x - P.toFun y‖]
  have hres : ‖(x - P.toFun x) - (y - P.toFun y)‖ ≤ ‖x - y‖ := by
    nlinarith [norm_nonneg ((x - P.toFun x) - (y - P.toFun y)), norm_nonneg (x - y)]
  have hinv : 0 ≤ 1 / lam := (one_div_pos.mpr hlam).le
  rw [show (1 / lam) • (x - P.toFun x) - (1 / lam) • (y - P.toFun y) =
      (1 / lam) • ((x - P.toFun x) - (y - P.toFun y)) by module,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  exact mul_le_mul_of_nonneg_left hres hinv

private theorem moreauEnvelope_eq_prox_objective {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x : H) :
    moreauEnvelope f lam hlam (fun z ↦ ⟨P.toFun z, fun eta ↦ by
      simpa [norm_sub_rev] using P.minimizes z eta⟩) x =
      f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam) := by
  unfold _root_.moreauEnvelope
  apply le_antisymm
  · apply csInf_le
    · refine ⟨f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam), ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa [norm_sub_rev] using P.minimizes x z
    · exact ⟨P.toFun x, by simp⟩
  · apply le_csInf
    · exact ⟨f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam),
        ⟨P.toFun x, rfl⟩⟩
    · rintro _ ⟨z, rfl⟩
      simpa [norm_sub_rev] using P.minimizes x z

private theorem prox_objective_upper_remainder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x h : H) :
    (f (P.toFun (x + h)) + ‖(x + h) - P.toFun (x + h)‖ ^ 2 / (2 * lam)) -
        (f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam)) -
        @inner ℝ H _ ((1 / lam) • (x - P.toFun x)) h ≤ ‖h‖ ^ 2 / (2 * lam) := by
  have hineq := P.minimizes (x + h) (P.toFun x)
  have hsplit : (P.toFun x - (x + h)) = -((x - P.toFun x) + h) := by module
  rw [norm_sub_rev (P.toFun (x + h)) (x + h), hsplit, norm_neg, norm_add_sq_real] at hineq
  rw [inner_smul_left, starRingEnd_apply, star_trivial]
  field_simp [ne_of_gt hlam] at hineq ⊢
  nlinarith

private theorem prox_objective_lower_remainder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x h : H) :
    -(3 * ‖h‖ ^ 2 / (2 * lam)) ≤
      (f (P.toFun (x + h)) + ‖(x + h) - P.toFun (x + h)‖ ^ 2 / (2 * lam)) -
        (f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam)) -
        @inner ℝ H _ ((1 / lam) • (x - P.toFun x)) h := by
  have hineq := P.minimizes x (P.toFun (x + h))
  have hlip := proximal_residual_lipschitz f hconvex hlsc hlam P x (x + h)
  have hlip' : ‖(1 / lam) • ((x + h) - P.toFun (x + h)) -
      (1 / lam) • (x - P.toFun x)‖ ≤ (1 / lam) * ‖h‖ := by
    calc
      ‖(1 / lam) • ((x + h) - P.toFun (x + h)) -
          (1 / lam) • (x - P.toFun x)‖ =
          ‖-((1 / lam) • (x - P.toFun x) -
            (1 / lam) • ((x + h) - P.toFun (x + h)))‖ := by
              congr 1
              module
      _ = ‖(1 / lam) • (x - P.toFun x) -
            (1 / lam) • ((x + h) - P.toFun (x + h))‖ := norm_neg _
      _ ≤ (1 / lam) * ‖x - (x + h)‖ := hlip
      _ = (1 / lam) * ‖h‖ := by rw [show x - (x + h) = -h by module, norm_neg]
  have hinner := neg_le_of_abs_le
    (abs_real_inner_le_norm ((1 / lam) • ((x + h) - P.toFun (x + h)) -
      (1 / lam) • (x - P.toFun x)) h)
  have hsplit : x - P.toFun (x + h) = ((x + h) - P.toFun (x + h)) - h := by module
  have hqnorm : ‖x - P.toFun (x + h)‖ ^ 2 =
      ‖((x + h) - P.toFun (x + h)) - h‖ ^ 2 := by rw [hsplit]
  rw [norm_sub_rev (P.toFun x) x, norm_sub_rev (P.toFun (x + h)) x,
    hqnorm, norm_sub_sq_real ((x + h) - P.toFun (x + h)) h] at hineq
  rw [inner_sub_left] at hinner
  rw [inner_smul_left, inner_smul_left, starRingEnd_apply, star_trivial] at hinner
  rw [inner_smul_left, starRingEnd_apply, star_trivial]
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  field_simp [ne_of_gt hlam] at hineq hinner hlip' ⊢
  nlinarith [mul_le_mul_of_nonneg_right hlip' hnorm]

private theorem prox_objective_hasFDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (P : ProximalMapping f lam hlam hconvex hlsc) (x : H) :
    HasFDerivAt (fun y ↦ f (P.toFun y) + ‖y - P.toFun y‖ ^ 2 / (2 * lam))
      (innerSL ℝ ((1 / lam) • (x - P.toFun x))) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let C : ℝ := 3 / (2 * lam)
  have hC : 0 < C := by dsimp [C]; positivity
  refine Metric.eventually_nhds_iff.2 ⟨ε / C, div_pos hε hC, ?_⟩
  intro h hh
  have hdist : ‖h‖ < ε / C := by simpa [dist_eq_norm] using hh
  have hupper := prox_objective_upper_remainder f hconvex hlsc hlam P x h
  have hlower := prox_objective_lower_remainder f hconvex hlsc hlam P x h
  have hnorm : 0 ≤ ‖h‖ := norm_nonneg _
  have hsmall : C * ‖h‖ ≤ ε := by
    simpa [mul_comm] using le_of_lt ((lt_div_iff₀ hC).1 hdist)
  have hquad : C * ‖h‖ ^ 2 ≤ ε * ‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hnorm]
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · dsimp [C] at hlower hquad ⊢
    have hlow_eq : 3 * ‖h‖ ^ 2 / (2 * lam) = 3 / (2 * lam) * ‖h‖ ^ 2 := by
      field_simp [ne_of_gt hlam]
    rw [hlow_eq] at hlower
    nlinarith
  · dsimp [C] at hupper hquad ⊢
    have hupper' : ‖h‖ ^ 2 / (2 * lam) ≤ 3 / (2 * lam) * ‖h‖ ^ 2 := by
      have hsq : 0 ≤ ‖h‖ ^ 2 := sq_nonneg _
      field_simp [ne_of_gt hlam]
      nlinarith
    exact hupper.trans (hupper'.trans hquad)

/-- External result: Moreau envelopes are smooth and their gradients equal proximal residuals. -/
theorem moreauEnvelope_regular {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f) (hlsc : LowerSemicontinuous f)
    (lam : ℝ) (hlam : 0 < lam) (P : ProximalMapping f lam hlam hconvex hlsc) :
    (∀ x, IsProximalPoint f lam x (P.toFun x)) ∧
    (∀ x, (1 / lam) • (x - P.toFun x) ∈ subdifferential f (P.toFun x)) ∧
    (∀ x y, ‖P.toFun x - P.toFun y‖ ≤ ‖x - y‖) ∧
    HasLipschitzGradient (fun x ↦ (1 / lam) • (x - P.toFun x)) (1 / lam) ∧
    ∃ fLam : H → ℝ, Differentiable ℝ fLam ∧
      (∀ x, fderiv ℝ fLam x = innerSL ℝ ((1 / lam) • (x - P.toFun x))) ∧
      HasLipschitzGradient (fun x ↦ (1 / lam) • (x - P.toFun x)) (1 / lam) ∧
      ∀ x, fLam x = moreauEnvelope f lam hlam (fun z ↦ ⟨P.toFun z, fun eta ↦ by
        simpa [norm_sub_rev] using P.minimizes z eta⟩) x := by
  let e : H → ℝ := fun x => f (P.toFun x) + ‖x - P.toFun x‖ ^ 2 / (2 * lam)
  have hres : ∀ x, (1 / lam) • (x - P.toFun x) ∈ subdifferential f (P.toFun x) :=
    fun x => proximal_residual_mem_subgradient f hlam (P.optimality x)
  have hnonexp : ∀ x y, ‖P.toFun x - P.toFun y‖ ≤ ‖x - y‖ :=
    fun x y => proximal_nonexpansive f hconvex hlsc hlam P x y
  have hlip : HasLipschitzGradient (fun x ↦ (1 / lam) • (x - P.toFun x)) (1 / lam) :=
    fun x y => proximal_residual_lipschitz f hconvex hlsc hlam P x y
  have henv : ∀ x, moreauEnvelope f lam hlam (fun z ↦ ⟨P.toFun z, fun eta ↦ by
      simpa [norm_sub_rev] using P.minimizes z eta⟩) x = e x :=
    fun x => moreauEnvelope_eq_prox_objective f hconvex hlsc hlam P x
  refine ⟨P.optimality, hres, hnonexp, hlip, ?_⟩
  refine ⟨e, ?_, ?_, hlip, ?_⟩
  · intro x
    exact (prox_objective_hasFDerivAt f hconvex hlsc hlam P x).differentiableAt
  · intro x
    exact (prox_objective_hasFDerivAt f hconvex hlsc hlam P x).fderiv
  · intro x
    exact (henv x).symm
