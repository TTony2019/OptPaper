import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_3
import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.def_4

open scoped InnerProductSpace

open ERealFunction
open Pointwise

set_option linter.unusedVariables false in
/-- `]-∞,+∞]`-valued objectives that are proper, convex (with convex epigraph) and lower
semicontinuous lie in `Γ₀(H)`, so Foundation's proximity operator is available for them. -/
private theorem properIoi_mem_gammaZero_of_epigraph_convex_lsc {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {g : H → EReal} (hproper : ERealFunction.IsProper g)
    (hconvex : Convex ℝ (ERealFunction.epigraph g)) (hlsc : LowerSemicontinuous g) :
    ERealFunction.properIoi g hproper ∈ Γ₀(H) :=
  ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hproper (by
    rw [ERealFunction.mem_gamma_iff]
    exact ⟨ERealFunction.isConvex_of_convex_epigraph hproper hconvex, hlsc⟩)

/-- Proximal points of a `Γ₀` objective are unique at a positive index; this is Foundation's
`HasUniqueProxPoint` in its primal `IsProxPoint` form. -/
theorem isProxPoint_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {g : H → EReal} (hproper : ERealFunction.IsProper g)
    (hΓ : ERealFunction.properIoi g hproper ∈ Γ₀(H))
    (lam : ℝ) (hlam : 0 < lam) (w p q : H)
    (hp : IsProxPoint ((⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper) w p)
    (hq : IsProxPoint ((⟨lam, hlam⟩ : PosReal) • ERealFunction.properIoi g hproper) w q) :
    p = q :=
  ExistsUnique.unique
    (hasUniqueProxPoint_of_mem_gammaZero
      (smul_mem_gammaZero (ERealFunction.properIoi g hproper) hΓ ⟨lam, hlam⟩) w) hp hq

/-- After multiplying by `lam`, the variable-metric objective and the forward-backward
proximal objective differ by a constant independent of the candidate point. -/
private theorem composite_metric_objective_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H) (b : H)
    (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (c : ℝ) (x y : H) :
    lam * ((1 / 2 : ℝ) * ‖A y - b‖ ^ 2 + c + metricNormSq M (x - y) / (2 * lam)) =
      lam * c + (1 / 2 : ℝ) * ‖x - lam • A.adjoint (A x - b) - y‖ ^ 2 +
        (lam / 2) * ‖A x - b‖ ^ 2 - (lam ^ 2 / 2) * ‖A.adjoint (A x - b)‖ ^ 2 := by
  rw [hM]
  simp only [metricNormSq, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [inner_sub_left, inner_smul_left, A.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hw : x - lam • A.adjoint (A x - b) - y =
      (x - y) - lam • A.adjoint (A x - b) := by abel
  have hAy : A y - b = (A x - b) - A (x - y) := by
    rw [map_sub]
    abel
  rw [hw, hAy]
  rw [norm_sub_sq_real (A x - b) (A (x - y))]
  rw [norm_sub_sq_real (x - y) (lam • A.adjoint (A x - b))]
  rw [inner_smul_right]
  have hadj : @inner ℝ H _ (x - y) (A.adjoint (A x - b)) =
      @inner ℝ H _ (A x - b) (A (x - y)) := by
    rw [real_inner_comm]
    exact A.adjoint_inner_left (x - y) (A x - b)
  rw [hadj]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have hstar : (starRingEnd ℝ) lam = lam := by simp
  rw [hstar, real_inner_self_eq_norm_sq]
  field_simp [hlam_ne]
  ring

/-- Formula (5.6): the variable-metric proximity operator of a Lasso objective splits
forward-backward.  The left-hand side is the operator defined directly by the unique minimizer
in (5.2), rather than an arbitrary map satisfying the optimality condition (5.3). -/
theorem variableMetric_composite_proximal_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f g : H → EReal) (A : H →L[ℝ] H) (b : H)
    (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam)
    (hconvex : Convex ℝ (ERealFunction.epigraph g))
    (hlsc : LowerSemicontinuous g) (hproper : ERealFunction.IsProper g)
    (hf : ∀ x, f x = (((1 / 2 : ℝ) * ‖A x - b‖ ^ 2 : ℝ) : EReal) + g x)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (_hM_positive : ∀ v, v ≠ 0 → 0 < @inner ℝ H _ (M v) v)
    (hprox_unique : HasUniqueVariableMetricProxPoint f M ⟨lam, hlam⟩) (x : H) :
    variableMetricProximityOperator f M ⟨lam, hlam⟩ hprox_unique x =
      ERealFunction.scaledProximityOperator (ERealFunction.properIoi g hproper)
      (properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc) ⟨lam, hlam⟩
      (x - lam • A.adjoint (A x - b)) := by
  let lamPos : PosReal := ⟨lam, hlam⟩
  let p : H := variableMetricProximityOperator f M lamPos hprox_unique x
  let w : H := x - lam • A.adjoint (A x - b)
  have hp_min : ∀ y, variableMetricProximalObjective f M lamPos x p ≤
      variableMetricProximalObjective f M lamPos x y := by
    have hp := variableMetricProximityOperator_isProxPoint f M lamPos hprox_unique x
    have hp' : p ∈ variableMetricProximalPoints f M lamPos x := by
      simpa [p] using hp
    rw [variableMetricProximalPoints, ERealFunction.mem_argmin_iff,
      isMinOn_univ_iff] at hp'
    intro y
    exact hp' y
  obtain ⟨z, hz⟩ := hproper.2
  have hgz_top : g z ≠ ⊤ := ne_of_lt ((ERealFunction.mem_dom_iff g z).1 hz)
  have hfz_top : f z ≠ ⊤ := by
    rw [hf z]
    exact EReal.add_ne_top (EReal.coe_ne_top _) hgz_top
  have hobjz_top : variableMetricProximalObjective f M lamPos x z ≠ ⊤ := by
    rw [variableMetricProximalObjective]
    exact EReal.add_ne_top hfz_top (EReal.coe_ne_top _)
  have hobjp_top : variableMetricProximalObjective f M lamPos x p ≠ ⊤ :=
    ne_top_of_le_ne_top hobjz_top (hp_min z)
  have hfp_top : f p ≠ ⊤ := by
    intro hp_top
    apply hobjp_top
    simp [variableMetricProximalObjective, hp_top]
  have hgp_top : g p ≠ ⊤ := by
    intro hp_top
    apply hfp_top
    rw [hf p, hp_top]
    exact EReal.coe_add_top _
  have hp_standard : IsProxPoint (lamPos • ERealFunction.properIoi g hproper) w p := by
    unfold IsProxPoint ERealFunction.proximalPoints
    rw [ERealFunction.mem_argmin_iff, isMinOn_univ_iff]
    intro y
    by_cases hgy_top : g y = ⊤
    · have hright : ((lamPos • ERealFunction.properIoi g hproper) y : EReal) = ⊤ := by
        change (lamPos : EReal) * g y = ⊤
        rw [hgy_top]
        simpa [lamPos] using EReal.coe_mul_top_of_pos hlam
      simp only [ERealFunction.proximalObjective]
      rw [hright, EReal.top_add_coe]
      exact le_top
    · have hp_bot : g p ≠ ⊥ := hproper.1 p
      have hy_bot : g y ≠ ⊥ := hproper.1 y
      have hmin := hp_min y
      simp only [variableMetricProximalObjective] at hmin
      rw [hf p, hf y,
        ← EReal.coe_toReal hgp_top hp_bot, ← EReal.coe_toReal hgy_top hy_bot] at hmin
      have hmin_real :
          (1 / 2 : ℝ) * ‖A p - b‖ ^ 2 + (g p).toReal +
              metricNormSq M (x - p) / (2 * lam) ≤
            (1 / 2 : ℝ) * ‖A y - b‖ ^ 2 + (g y).toReal +
              metricNormSq M (x - y) / (2 * lam) := by
        exact_mod_cast hmin
      have hmul := mul_le_mul_of_nonneg_left hmin_real hlam.le
      rw [composite_metric_objective_identity A b M lam hlam hM (g p).toReal x p,
        composite_metric_objective_identity A b M lam hlam hM (g y).toReal x y] at hmul
      have hscaled :
          lam * (g p).toReal + (1 / 2 : ℝ) * ‖w - p‖ ^ 2 ≤
            lam * (g y).toReal + (1 / 2 : ℝ) * ‖w - y‖ ^ 2 := by
        dsimp [w]
        linarith
      have hscaled_ereal :
          (((lam * (g p).toReal + (1 / 2 : ℝ) * ‖w - p‖ ^ 2 : ℝ) : EReal) ≤
            ((lam * (g y).toReal + (1 / 2 : ℝ) * ‖w - y‖ ^ 2 : ℝ) : EReal)) :=
        EReal.coe_le_coe hscaled
      simpa [ERealFunction.proximalObjective, ERealFunction.posReal_smul_apply,
        ERealFunction.properIoi_apply, lamPos, EReal.coe_mul, EReal.coe_add,
        EReal.coe_toReal hgp_top hp_bot, EReal.coe_toReal hgy_top hy_bot,
        div_eq_mul_inv] using hscaled_ereal
  have hΓ : ERealFunction.properIoi g hproper ∈ Γ₀(H) :=
    properIoi_mem_gammaZero_of_epigraph_convex_lsc hproper hconvex hlsc
  have hp_eq := ERealFunction.eq_proximityOperator_of_isProxPoint
    (f := lamPos • ERealFunction.properIoi g hproper)
    (ERealFunction.hasUniqueProxPoint_of_mem_gammaZero
      (ERealFunction.smul_mem_gammaZero _ hΓ lamPos)) hp_standard
  simpa [p, w, lamPos, ERealFunction.scaledProximityOperator] using hp_eq
