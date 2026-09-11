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

open Pointwise

/-- The proximal point of the Lasso objective in the metric induced by `M = Id - λ AᵀA`
(paper (5.6)): `p x = prox^M_{λf}(x) = prox_{λg}(x - λ Aᵀ(Ax - b))`. -/
noncomputable def lassoProx {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (b : H) (γ : PosReal) (x : H) : H :=
  ERealFunction.scaledProximityOperator G hG γ (x - (γ : ℝ) • A.adjoint (A x - b))

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

/-- The real-valued Lasso objective `x ↦ (1/2)‖Ax - b‖² + g(x)` of (5.1): the quadratic data term
together with the finite part of `g`. -/
noncomputable def lassoObjectiveReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → Set.Ioi (⊥ : EReal)) (A : H →L[ℝ] H) (b : H) (x : H) : ℝ :=
  (1 / 2) * ‖A x - b‖ ^ 2 + ((G x : EReal)).toReal

/-- The variable-metric Moreau envelope (5.2) of the Lasso objective at `x`, evaluated at the
proximal point `p x = lassoProx … x` realizing its minimum (5.6). -/
noncomputable def lassoEnvelope {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H) (γ : PosReal) (x : H) : ℝ :=
  lassoObjectiveReal G A b (lassoProx G hG A b γ x) +
    metricNormSq M (x - lassoProx G hG A b γ x) / (2 * (γ : ℝ))

/-- The metric `M = Id - λ AᵀA` of (5.5) is symmetric. -/
theorem lassoMetric_symm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H) (M : H →L[ℝ] H) (lam : ℝ)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A)) (x y : H) :
    inner ℝ (M x) y = inner ℝ x (M y) := by
  subst hM
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- The metric `M = Id - λ AᵀA` is positive semidefinite when `λ‖A‖² ≤ 1`. -/
theorem lassoMetric_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H) (M : H →L[ℝ] H) (lam : ℝ)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (hlam : 0 ≤ lam) (hA : lam * ‖A‖ ^ 2 ≤ 1) (x : H) :
    0 ≤ metricNormSq M x := by
  subst hM
  rw [metricNormSq]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have hbound : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
  have hAsq : ‖A x‖ ^ 2 ≤ (‖A‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hkey : lam * ‖A x‖ ^ 2 ≤ lam * ((‖A‖ * ‖x‖) ^ 2) :=
    mul_le_mul_of_nonneg_left hAsq hlam
  have hA1 : lam * (‖A‖ * ‖x‖) ^ 2 = (lam * ‖A‖ ^ 2) * ‖x‖ ^ 2 := by ring
  rw [hA1] at hkey
  nlinarith [sq_nonneg ‖x‖, hA, mul_le_mul_of_nonneg_right hA (sq_nonneg ‖x‖)]

/-- Quadratic expansion of `metricNormSq` along a difference. -/
theorem metricNormSq_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H)
    (hsymm : ∀ x y : H, inner ℝ (M x) y = inner ℝ x (M y)) (a b : H) :
    metricNormSq M (a - b) = metricNormSq M a - 2 * inner ℝ (M a) b + metricNormSq M b := by
  simp only [metricNormSq, map_sub, inner_sub_left, inner_sub_right]
  rw [hsymm b a, real_inner_comm (M a) b]
  ring

/-- Quadratic expansion of `metricNormSq` along a sum. -/
private theorem metricNormSq_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H) (hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y)) (a h : H) :
    metricNormSq M (a + h) = metricNormSq M a + 2 * inner ℝ (M a) h + metricNormSq M h := by
  simp only [metricNormSq, map_add, inner_add_left, inner_add_right]
  rw [hsymm h a, real_inner_comm h (M a)]
  ring

/-- The `M`-metric proximal point is the minimizer of the proximal subproblem. -/
private theorem metricProx_minimizes {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (M : H →L[ℝ] H) (gamma : ℝ) (hgamma : 0 < gamma) (p : H → H)
    (hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hnonneg : ∀ x, 0 ≤ metricNormSq M x)
    (hfinite : ∀ x, f (p x) ≠ ⊤) (hnebot : ∀ x, f x ≠ ⊥)
    (hopt : ∀ x, (1 / gamma) • M (x - p x) ∈ subdifferential f (p x)) (x ξ : H) :
    f (p x) + ((metricNormSq M (x - p x) / (2 * gamma) : ℝ) : EReal) ≤
      f ξ + ((metricNormSq M (x - ξ) / (2 * gamma) : ℝ) : EReal) := by
  by_cases htop : f ξ = ⊤
  · rw [htop]
    exact le_top
  have hpx_top : f (p x) ≠ ⊤ := hfinite x
  have hpx_bot : f (p x) ≠ ⊥ := hnebot (p x)
  have hξ_bot : f ξ ≠ ⊥ := hnebot ξ
  have hlin := (mem_subdifferential_iff f (p x) ((1 / gamma) • M (x - p x))).mp (hopt x) ξ
  have hlin' : ((inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) : ℝ) : EReal) +
      (f (p x) : EReal) ≤ (f ξ : EReal) := hlin
  have hlin_real :
      inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) + (f (p x)).toReal ≤ (f ξ).toReal := by
    have h := EReal.toReal_le_toReal hlin'
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hpx_bot⟩) htop
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hpx_top hpx_bot] at h
    exact h
  have hquad_real : metricNormSq M (x - p x) / (2 * gamma) ≤
      inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) + metricNormSq M (x - ξ) / (2 * gamma) := by
    have hexp := metricNormSq_sub M hsymm (x - p x) (ξ - p x)
    have hsub : x - p x - (ξ - p x) = x - ξ := by abel
    rw [hsub] at hexp
    have hnn : 0 ≤ metricNormSq M (ξ - p x) := hnonneg _
    have hinner : inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) * (2 * gamma) =
        2 * inner ℝ (M (x - p x)) (ξ - p x) := by
      rw [inner_smul_right, real_inner_comm (ξ - p x) (M (x - p x))]
      field_simp
    have h2g : 0 < 2 * gamma := by linarith
    rw [div_le_iff₀ h2g]
    have hmul : (inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) +
        metricNormSq M (x - ξ) / (2 * gamma)) * (2 * gamma) =
        inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) * (2 * gamma) + metricNormSq M (x - ξ) := by
      field_simp
    rw [hmul, hinner]
    linarith [hexp, hnn]
  have hquad : ((metricNormSq M (x - p x) / (2 * gamma) : ℝ) : EReal) ≤
      ((inner ℝ (ξ - p x) ((1 / gamma) • M (x - p x)) : ℝ) : EReal) +
        ((metricNormSq M (x - ξ) / (2 * gamma) : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    exact_mod_cast hquad_real
  have hL : (f (p x) + ((metricNormSq M (x - p x) / (2 * gamma) : ℝ) : EReal)).toReal =
      (f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma) := by
    rw [EReal.toReal_add hpx_top hpx_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
  have hR : (f ξ + ((metricNormSq M (x - ξ) / (2 * gamma) : ℝ) : EReal)).toReal =
      (f ξ).toReal + metricNormSq M (x - ξ) / (2 * gamma) := by
    rw [EReal.toReal_add htop hξ_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  rw [← EReal.coe_toReal (EReal.add_ne_top hpx_top (EReal.coe_ne_top _))
        (EReal.add_ne_bot_iff.mpr ⟨hpx_bot, EReal.coe_ne_bot _⟩),
      ← EReal.coe_toReal (EReal.add_ne_top htop (EReal.coe_ne_top _))
        (EReal.add_ne_bot_iff.mpr ⟨hξ_bot, EReal.coe_ne_bot _⟩)]
  rw [hL, hR]
  exact_mod_cast (show (f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma) ≤
    (f ξ).toReal + metricNormSq M (x - ξ) / (2 * gamma) from by linarith [hlin_real, hquad_real])

/-- The `M`-metric proximal residual is monotone in the `M`-norm. -/
private theorem metricProx_mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (M : H →L[ℝ] H) (gamma : ℝ) (hgamma : 0 < gamma) (p : H → H)
    (_hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hnonneg : ∀ x, 0 ≤ metricNormSq M x)
    (hfinite : ∀ x, f (p x) ≠ ⊤) (hnebot : ∀ x, f x ≠ ⊥)
    (hopt : ∀ x, (1 / gamma) • M (x - p x) ∈ subdifferential f (p x)) (x y : H) :
    inner ℝ (M (p y - p x)) (y - x) ≤ metricNormSq M (y - x) := by
  have hpx_top : f (p x) ≠ ⊤ := hfinite x
  have hpy_top : f (p y) ≠ ⊤ := hfinite y
  have hpx_bot : f (p x) ≠ ⊥ := hnebot (p x)
  have hpy_bot : f (p y) ≠ ⊥ := hnebot (p y)
  have h1 := (mem_subdifferential_iff f (p x) ((1 / gamma) • M (x - p x))).mp (hopt x) (p y)
  have h1' : ((inner ℝ (p y - p x) ((1 / gamma) • M (x - p x)) : ℝ) : EReal) +
      (f (p x) : EReal) ≤ (f (p y) : EReal) := h1
  have h1r : inner ℝ (p y - p x) ((1 / gamma) • M (x - p x)) + (f (p x)).toReal ≤
      (f (p y)).toReal := by
    have h := EReal.toReal_le_toReal h1'
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hpx_bot⟩) hpy_top
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hpx_top hpx_bot] at h
    exact h
  have h2 := (mem_subdifferential_iff f (p y) ((1 / gamma) • M (y - p y))).mp (hopt y) (p x)
  have h2' : ((inner ℝ (p x - p y) ((1 / gamma) • M (y - p y)) : ℝ) : EReal) +
      (f (p y) : EReal) ≤ (f (p x) : EReal) := h2
  have h2r : inner ℝ (p x - p y) ((1 / gamma) • M (y - p y)) + (f (p y)).toReal ≤
      (f (p x)).toReal := by
    have h := EReal.toReal_le_toReal h2'
      (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hpy_bot⟩) hpx_top
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hpy_top hpy_bot] at h
    exact h
  have hsum : inner ℝ (p y - p x) ((1 / gamma) • M (x - p x)) +
      inner ℝ (p x - p y) ((1 / gamma) • M (y - p y)) ≤ 0 := by linarith [h1r, h2r]
  have hmono : 0 ≤ inner ℝ (((1 / gamma) • M (x - p x)) - ((1 / gamma) • M (y - p y)))
      (p x - p y) := by
    rw [inner_sub_left]
    rw [real_inner_comm (p x - p y) ((1 / gamma) • M (x - p x)),
      real_inner_comm (p x - p y) ((1 / gamma) • M (y - p y))]
    have e3 : inner ℝ (p y - p x) ((1 / gamma) • M (x - p x)) =
        -inner ℝ (p x - p y) ((1 / gamma) • M (x - p x)) := by
      rw [show p y - p x = -(p x - p y) by abel, inner_neg_left]
    rw [e3] at hsum
    linarith
  have hkey : 0 ≤ inner ℝ (M (x - p x) - M (y - p y)) (x - y) := by
    have hxy : x - y = ((x - p x) - (y - p y)) + (p x - p y) := by abel
    rw [← map_sub, hxy, inner_add_right]
    apply add_nonneg
    · exact hnonneg _
    · have hMab : M ((x - p x) - (y - p y)) = gamma •
          (((1 / gamma) • M (x - p x)) - ((1 / gamma) • M (y - p y))) := by
        rw [map_sub, smul_sub]
        congr 1
        · rw [smul_smul]
          have hc : gamma * (1 / gamma) = 1 := by field_simp
          rw [hc, one_smul]
        · rw [smul_smul]
          have hc : gamma * (1 / gamma) = 1 := by field_simp
          rw [hc, one_smul]
      rw [hMab, real_inner_smul_left]
      exact mul_nonneg hgamma.le hmono
  have h1' : inner ℝ (M (x - p x) - M (y - p y)) (x - y) =
      metricNormSq M (y - x) - inner ℝ (M (p y - p x)) (y - x) := by
    rw [← map_sub]
    have hab : (x - p x) - (y - p y) = -(y - x) + (p y - p x) := by abel
    rw [hab, show x - y = -(y - x) by abel]
    simp only [map_add, map_neg, inner_add_left, inner_neg_left, inner_neg_right, metricNormSq]
    ring
  linarith [hkey, h1']

/-- Formula (5.4): the gradient of a variable-metric Moreau envelope.  If `p x` is the
`M`-metric proximal point of an extended-real objective `f` at `x` (witnessed by the optimality
inclusion `(1/γ) M (x - p x) ∈ ∂f (p x)`), then the envelope `x ↦ f (p x) + ‖x - p x‖²_M / (2γ)`
has Euclidean gradient `(1/γ) M (x - p x)`. -/
theorem gradient_metricMoreauEnvelope_of_optimality {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (M : H →L[ℝ] H) (gamma : ℝ) (hgamma : 0 < gamma) (p : H → H)
    (hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hnonneg : ∀ x, 0 ≤ metricNormSq M x)
    (hfinite : ∀ x, f (p x) ≠ ⊤) (hnebot : ∀ x, f x ≠ ⊥)
    (hopt : ∀ x, (1 / gamma) • M (x - p x) ∈ subdifferential f (p x)) :
    gradient (fun y : H => (f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) =
      fun x : H => (1 / gamma) • M (x - p x) := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_tendsto]
  have hupper : ∀ y : H,
      ((f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) -
        ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) -
        inner ℝ ((1 / gamma) • M (x - p x)) (y - x) ≤
          metricNormSq M (y - x) / (2 * gamma) := by
    intro y
    have hmin := metricProx_minimizes f M gamma hgamma p hsymm hnonneg hfinite hnebot hopt y (p x)
    have hmin' : (f (p y) + ((metricNormSq M (y - p y) / (2 * gamma) : ℝ) : EReal)) ≤
        (f (p x) + ((metricNormSq M (y - p x) / (2 * gamma) : ℝ) : EReal)) := hmin
    have hpy_top : f (p y) ≠ ⊤ := hfinite y
    have hpx_top : f (p x) ≠ ⊤ := hfinite x
    have hpy_bot : f (p y) ≠ ⊥ := hnebot (p y)
    have hpx_bot : f (p x) ≠ ⊥ := hnebot (p x)
    have hminr : (f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma) ≤
        (f (p x)).toReal + metricNormSq M (y - p x) / (2 * gamma) := by
      have h := EReal.toReal_le_toReal hmin'
        (EReal.add_ne_bot_iff.mpr ⟨hpy_bot, EReal.coe_ne_bot _⟩)
        (EReal.add_ne_top hpx_top (EReal.coe_ne_top _))
      rw [EReal.toReal_add hpy_top hpy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_add hpx_top hpx_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe, EReal.toReal_coe] at h
      exact h
    have hbound : (f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma) -
        ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) ≤
          metricNormSq M (y - p x) / (2 * gamma) - metricNormSq M (x - p x) / (2 * gamma) := by
      linarith [hminr]
    have hquaddiff : metricNormSq M (y - p x) / (2 * gamma) -
        metricNormSq M (x - p x) / (2 * gamma) =
          inner ℝ ((1 / gamma) • M (x - p x)) (y - x) +
            metricNormSq M (y - x) / (2 * gamma) := by
      have h := metricNormSq_add M hsymm (x - p x) (y - x)
      have hs : x - p x + (y - x) = y - p x := by abel
      rw [hs] at h
      rw [h, real_inner_smul_left]
      field_simp
      ring
    linarith [hbound, hquaddiff]
  have hlower : ∀ y : H,
      -(metricNormSq M (y - x) / (2 * gamma)) ≤
        ((f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) -
          ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) -
          inner ℝ ((1 / gamma) • M (x - p x)) (y - x) := by
    intro y
    have hmin := metricProx_minimizes f M gamma hgamma p hsymm hnonneg hfinite hnebot hopt x (p y)
    have hmin' : (f (p x) + ((metricNormSq M (x - p x) / (2 * gamma) : ℝ) : EReal)) ≤
        (f (p y) + ((metricNormSq M (x - p y) / (2 * gamma) : ℝ) : EReal)) := hmin
    have hpy_top : f (p y) ≠ ⊤ := hfinite y
    have hpx_top : f (p x) ≠ ⊤ := hfinite x
    have hpy_bot : f (p y) ≠ ⊥ := hnebot (p y)
    have hpx_bot : f (p x) ≠ ⊥ := hnebot (p x)
    have hminr : (f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma) ≤
        (f (p y)).toReal + metricNormSq M (x - p y) / (2 * gamma) := by
      have h := EReal.toReal_le_toReal hmin'
        (EReal.add_ne_bot_iff.mpr ⟨hpx_bot, EReal.coe_ne_bot _⟩)
        (EReal.add_ne_top hpy_top (EReal.coe_ne_top _))
      rw [EReal.toReal_add hpx_top hpx_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_add hpy_top hpy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe, EReal.toReal_coe] at h
      exact h
    have hbound : (f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma) -
        ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) ≥
          metricNormSq M (y - p y) / (2 * gamma) - metricNormSq M (x - p y) / (2 * gamma) := by
      linarith [hminr]
    have hquaddiff : metricNormSq M (y - p y) / (2 * gamma) -
        metricNormSq M (x - p y) / (2 * gamma) =
          inner ℝ ((1 / gamma) • M (x - p y)) (y - x) +
            metricNormSq M (y - x) / (2 * gamma) := by
      have h := metricNormSq_add M hsymm (x - p y) (y - x)
      have hs : x - p y + (y - x) = y - p y := by abel
      rw [hs] at h
      rw [h, real_inner_smul_left]
      field_simp
      ring
    have hsplit : inner ℝ ((1 / gamma) • M (x - p y)) (y - x) =
        inner ℝ ((1 / gamma) • M (x - p x)) (y - x) -
          inner ℝ ((1 / gamma) • M (p y - p x)) (y - x) := by
      have hM : M (x - p y) = M (x - p x) - M (p y - p x) := by
        rw [← map_sub]; congr 1; abel
      rw [hM, smul_sub, inner_sub_left]
    have hmono := metricProx_mono f M gamma hgamma p hsymm hnonneg hfinite hnebot hopt x y
    have h3 : inner ℝ ((1 / gamma) • M (p y - p x)) (y - x) ≤
        metricNormSq M (y - x) / gamma := by
      have hle : (0 : ℝ) ≤ 1 / gamma := by positivity
      calc inner ℝ ((1 / gamma) • M (p y - p x)) (y - x)
          = (1 / gamma) * inner ℝ (M (p y - p x)) (y - x) := by rw [real_inner_smul_left]
        _ ≤ (1 / gamma) * metricNormSq M (y - x) := mul_le_mul_of_nonneg_left hmono hle
        _ = metricNormSq M (y - x) / gamma := by ring
    have hA : (f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma) -
          ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) ≥
          inner ℝ ((1 / gamma) • M (x - p x)) (y - x) -
            metricNormSq M (y - x) / gamma + metricNormSq M (y - x) / (2 * gamma) := by
      linarith [hbound, hquaddiff, hsplit, h3]
    have hB : inner ℝ ((1 / gamma) • M (x - p x)) (y - x) -
          metricNormSq M (y - x) / gamma + metricNormSq M (y - x) / (2 * gamma) =
          inner ℝ ((1 / gamma) • M (x - p x)) (y - x) -
            metricNormSq M (y - x) / (2 * gamma) := by
      field_simp
      ring
    linarith [hA, hB]
  have hbd : ∀ y : H, ‖y - x‖⁻¹ *
      ‖((f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) -
        ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) -
        inner ℝ ((1 / gamma) • M (x - p x)) (y - x)‖ ≤
      (1 / (2 * gamma)) * ‖M‖ * ‖y - x‖ := by
    intro y
    have habs : ‖((f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) -
        ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) -
        inner ℝ ((1 / gamma) • M (x - p x)) (y - x)‖ ≤ metricNormSq M (y - x) / (2 * gamma) := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hlower y, hupper y⟩
    have hMle : metricNormSq M (y - x) ≤ ‖M‖ * ‖y - x‖ ^ 2 := by
      rw [metricNormSq]
      calc inner ℝ (M (y - x)) (y - x) ≤ ‖M (y - x)‖ * ‖y - x‖ := real_inner_le_norm _ _
        _ ≤ (‖M‖ * ‖y - x‖) * ‖y - x‖ :=
            mul_le_mul_of_nonneg_right (M.le_opNorm _) (norm_nonneg _)
        _ = ‖M‖ * ‖y - x‖ ^ 2 := by ring
    have h2g : 0 < 2 * gamma := by linarith
    calc ‖y - x‖⁻¹ * ‖((f (p y)).toReal + metricNormSq M (y - p y) / (2 * gamma)) -
          ((f (p x)).toReal + metricNormSq M (x - p x) / (2 * gamma)) -
          inner ℝ ((1 / gamma) • M (x - p x)) (y - x)‖
        ≤ ‖y - x‖⁻¹ * (metricNormSq M (y - x) / (2 * gamma)) :=
          mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ‖y - x‖⁻¹ * ((‖M‖ * ‖y - x‖ ^ 2) / (2 * gamma)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
          exact div_le_div_of_nonneg_right hMle h2g.le
      _ = (1 / (2 * gamma)) * ‖M‖ * ‖y - x‖ := by
          have hkey2 : ‖y - x‖⁻¹ * ((‖M‖ * ‖y - x‖ ^ 2) / (2 * gamma)) =
              (1 / (2 * gamma)) * ‖M‖ * ‖y - x‖ := by
            rcases eq_or_ne ‖y - x‖ 0 with hyx | hyx
            · simp [hyx]
            · field_simp
          exact hkey2
  have hnorm : Filter.Tendsto (fun y : H => ‖y - x‖) (nhds x) (nhds 0) := by
    have hcont : Continuous fun y : H => ‖y - x‖ :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    simpa using (show Filter.Tendsto (fun y : H => ‖y - x‖) (nhds x) (nhds (‖x - x‖)) from
      hcont.continuousAt)
  have hlim : Filter.Tendsto (fun y : H => (1 / (2 * gamma)) * ‖M‖ * ‖y - x‖)
      (nhds x) (nhds 0) := by
    have h0 : Filter.Tendsto (fun y : H => ((1 / (2 * gamma)) * ‖M‖) * ‖y - x‖)
        (nhds x) (nhds (((1 / (2 * gamma)) * ‖M‖) * 0)) :=
      tendsto_const_nhds.mul hnorm
    simpa using h0
  exact squeeze_zero (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hbd hlim

/-- The extended-real Lasso objective `z ↦ (1/2)‖Az - b‖² + g z`. -/
noncomputable def lassoObjectiveE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → Set.Ioi (⊥ : EReal)) (A : H →L[ℝ] H) (b : H) : H → EReal :=
  fun z => (G z : EReal) + (((1 / 2 : ℝ) * ‖A z - b‖ ^ 2 : ℝ) : EReal)

/-- The forward-backward splitting (5.6) witnesses the `M`-metric optimality condition of the
Lasso proximal point: `(1/λ) M (x - prox x)` is a subgradient of the objective at `prox x`. -/
private theorem lasso_prox_optimality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H) (lam : ℝ) (hlam : 0 < lam)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A)) (x : H) :
    (1 / lam) • M (x - lassoProx G hG A b ⟨lam, hlam⟩ x) ∈
      subdifferential (lassoObjectiveE G A b) (lassoProx G hG A b ⟨lam, hlam⟩ x) := by
  let p : H := lassoProx G hG A b ⟨lam, hlam⟩ x
  let u : H := x - lam • A.adjoint (A x - b)
  have hmem : (lam)⁻¹ • (u - p) ∈ subdifferential G p := by
    have hres := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, hlam⟩ u
    simpa [p, u, lassoProx] using hres
  set g : H → Set.Ioi (⊥ : EReal) := (fun w : H => (1 / 2 : ℝ) * ‖w - b‖ ^ 2).toEReal with hg
  have hg_mem : (A p - b) ∈ subdifferential g (A p) := by
    rw [mem_subdifferential_iff]
    intro y
    change (((⟪y - A p, A p - b⟫_ℝ : ℝ) : EReal) + (g (A p) : EReal)) ≤ (g y : EReal)
    have h1 : (g (A p) : EReal) = (((1 / 2 : ℝ) * ‖A p - b‖ ^ 2 : ℝ) : EReal) := by
      simp [g, Function.toEReal]
    have h2 : (g y : EReal) = (((1 / 2 : ℝ) * ‖y - b‖ ^ 2 : ℝ) : EReal) := by
      simp [g, Function.toEReal]
    rw [h1, h2, ← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    have hdecomp : y - b = (A p - b) + (y - A p) := by abel
    rw [hdecomp, norm_add_sq_real, real_inner_comm (A p - b) (y - A p)]
    nlinarith [sq_nonneg ‖y - A p‖]
  have hsum := subdifferential_add_adjoint_image_subset_subdifferential_add_comp G g A p
  have hmem2 : (lam)⁻¹ • (u - p) + A.adjoint (A p - b) ∈
      ((∂ G) p + ContinuousLinearMap.adjointImageSubdifferential A g p) := by
    refine Set.mem_add.mpr ⟨(lam)⁻¹ • (u - p), hmem, A.adjoint (A p - b), ?_, rfl⟩
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
    exact ⟨A p - b, hg_mem, rfl⟩
  have hmem3 := hsum hmem2
  have hveq : (lam)⁻¹ • (u - p) + A.adjoint (A p - b) = (1 / lam) • M (x - p) := by
    have hM' : M (x - p) = (x - p) - lam • A.adjoint (A (x - p)) := by
      rw [hM]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [hM', one_div]
    have hAdj : A.adjoint (A (x - p)) = A.adjoint (A x - b) - A.adjoint (A p - b) := by
      simp only [map_sub]; abel
    rw [hAdj]
    simp only [u, smul_sub, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    module
  rw [← hveq]
  exact hmem3

/-- The variable-metric Moreau envelope of the Lasso objective has gradient
`(1/λ) M (x - prox x)`, which is formula (5.7) of the paper. -/
theorem gradient_lassoEnvelope {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H) (lam : ℝ) (hlam : 0 < lam)
    (hM : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A))
    (hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (hnonneg : ∀ x, 0 ≤ metricNormSq M x) :
    gradient (lassoEnvelope G hG A M b ⟨lam, hlam⟩) =
      fun x => (1 / lam) • M (x - lassoProx G hG A b ⟨lam, hlam⟩ x) := by
  have hdom : (ERealFunction.effectiveDomain G).Nonempty := (isProper_of_mem_gammaZero hG).2
  have hGtop : ∀ y, (G (lassoProx G hG A b ⟨lam, hlam⟩ y) : EReal) ≠ ⊤ := by
    intro y
    have hmem := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, hlam⟩
      (y - lam • A.adjoint (A y - b))
    have hsub : SubdifferentiableAt G (lassoProx G hG A b ⟨lam, hlam⟩ y) :=
      (SetValuedOperator.mem_dom_iff (∂ G) (lassoProx G hG A b ⟨lam, hlam⟩ y)).mpr
        ⟨_, by simpa [lassoProx] using hmem⟩
    have hpdom := SubdifferentiableAt.mem_effectiveDomain hdom hsub
    exact ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp hpdom)
  have hfinite : ∀ y, lassoObjectiveE G A b (lassoProx G hG A b ⟨lam, hlam⟩ y) ≠ ⊤ :=
    fun y => EReal.add_ne_top (hGtop y) (EReal.coe_ne_top _)
  have hnebot : ∀ y, lassoObjectiveE G A b y ≠ ⊥ :=
    fun y => EReal.add_ne_bot_iff.mpr ⟨ne_of_gt (G y).2, EReal.coe_ne_bot _⟩
  have hgen := gradient_metricMoreauEnvelope_of_optimality (lassoObjectiveE G A b) M lam hlam
    (lassoProx G hG A b ⟨lam, hlam⟩) hsymm hnonneg hfinite hnebot
    (fun x => lasso_prox_optimality G hG A M b lam hlam hM x)
  have hobj : ∀ y, (lassoObjectiveE G A b (lassoProx G hG A b ⟨lam, hlam⟩ y)).toReal =
      lassoObjectiveReal G A b (lassoProx G hG A b ⟨lam, hlam⟩ y) := by
    intro y
    have hbot : (G (lassoProx G hG A b ⟨lam, hlam⟩ y) : EReal) ≠ ⊥ :=
      ne_of_gt (G (lassoProx G hG A b ⟨lam, hlam⟩ y)).2
    simp only [lassoObjectiveE, lassoObjectiveReal]
    rw [EReal.toReal_add (hGtop y) hbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
    ring
  have hfun : lassoEnvelope G hG A M b ⟨lam, hlam⟩ =
      fun y => (lassoObjectiveE G A b (lassoProx G hG A b ⟨lam, hlam⟩ y)).toReal +
        metricNormSq M (y - lassoProx G hG A b ⟨lam, hlam⟩ y) / (2 * lam) := by
    funext y
    simp only [lassoEnvelope, hobj y]
  rw [hfun, hgen]

/-- Quadratic expansion of the data term `(1/2)‖A · - b‖²`. -/
private theorem lassoQuadratic_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : H →L[ℝ] H) (b p y : H) :
    (1 / 2 : ℝ) * ‖A y - b‖ ^ 2 =
      (1 / 2 : ℝ) * ‖A p - b‖ ^ 2 + inner ℝ (A.adjoint (A p - b)) (y - p) +
        (1 / 2 : ℝ) * ‖A (y - p)‖ ^ 2 := by
  have hdecomp : A y - b = (A p - b) + A (y - p) := by
    rw [map_sub]; abel
  rw [hdecomp, norm_add_sq_real, A.adjoint_inner_left]
  ring


/--
Theorem 5.1: (Human checked)
the variable-metric Lasso trajectory inherits the IPAHDD
finite-length and finite-stopping conclusions from its envelope realization.
-/
theorem IPAHDDLasso_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi fLam : H → ℝ) (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H)
    (h gamma beta lam r L : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDLasso phi.toEReal hdf.toEReal_mem_gammaZero G hG A M b lam h gamma beta)
    (hphi : ∀ x, phi x = r * ‖x‖)
    (hfLam : ContDiff ℝ 1 fLam)
    (hLip : HasLipschitzGradient (gradient fLam) L) (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, (c : EReal) ≤ lassoObjectiveE G A b x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hfLam_def : fLam = lassoEnvelope G hG A M b ⟨lam, alg.lam_pos⟩) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} => ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      (∃ u, u ∈ subdifferential G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) ∧
        ‖A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) - b) + u‖ ≤ r) ∧
      (‖gradient fLam xInf‖ < r -> IsFinitelyConvergent alg.x) := by
  -- The Lasso potential `fLam` is the variable-metric Moreau envelope, so its gradient is
  -- formula (5.7) rather than an extra hypothesis.
  have hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y) :=
    lassoMetric_symm A M lam alg.metric
  have hnorm_le : lam * ‖A‖ ^ 2 ≤ 1 := le_of_lt alg.lam_norm_sq.2
  have hnonneg : ∀ x, 0 ≤ metricNormSq M x :=
    lassoMetric_nonneg A M lam alg.metric alg.lam_pos.le hnorm_le
  have hgrad : ∀ x, gradient fLam x =
      (1 / lam) • M (x - lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) := by
    intro x
    rw [hfLam_def]
    exact congrFun (gradient_lassoEnvelope G hG A M b lam alg.lam_pos alg.metric hsymm hnonneg) x
  -- The variable-metric Moreau envelope preserves the infimum, so a lower bound on the Lasso
  -- objective bounds the envelope.
  have hGtop : ∀ y, (G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y) : EReal) ≠ ⊤ := by
    intro y
    have hmem := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, alg.lam_pos⟩
      (y - lam • A.adjoint (A y - b))
    have hsub : SubdifferentiableAt G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y) :=
      (SetValuedOperator.mem_dom_iff (∂ G) (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y)).mpr
        ⟨_, by simpa [lassoProx] using hmem⟩
    exact ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
      (SubdifferentiableAt.mem_effectiveDomain (isProper_of_mem_gammaZero hG).2 hsub))
  have hbelowLam : ∃ c : ℝ, ∀ x, c ≤ fLam x := by
    obtain ⟨c, hc⟩ := hbelow
    refine ⟨c, fun x => ?_⟩
    set p : H := lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x with hp
    have hobj : (lassoObjectiveE G A b p).toReal = lassoObjectiveReal G A b p := by
      simp only [lassoObjectiveE, lassoObjectiveReal]
      rw [EReal.toReal_add (hGtop x) (ne_of_gt (G p).2) (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe]
      ring
    have h1 : c ≤ (lassoObjectiveE G A b p).toReal :=
      EReal.toReal_le_toReal (hc p) (EReal.coe_ne_bot _)
        (EReal.add_ne_top (hGtop x) (EReal.coe_ne_top _))
    have hEnv : lassoEnvelope G hG A M b ⟨lam, alg.lam_pos⟩ x =
        lassoObjectiveReal G A b p + metricNormSq M (x - p) / (2 * lam) := by
      simp only [lassoEnvelope, ← hp]
    have h2 : 0 ≤ metricNormSq M (x - p) / (2 * lam) := by
      apply div_nonneg (hnonneg _)
      linarith [alg.lam_pos]
    rw [hfLam_def, hEnv, ← hobj]
    linarith
  -- Splitting (5.6)+(5.7) identifies the Lasso surrogate `z k` with `∇f_λ(x k)`, hence the
  -- Lasso iteration `alg` is literally the IPAHDD trajectory of the envelope `fLam`.
  have hz : ∀ k, alg.z k = gradient fLam (alg.x k) := by
    intro k
    rw [alg.z_def k, hgrad (alg.x k)]
    simp [lassoProx]
  have hsmooth : ∃ smooth : IPAHDD fLam phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta,
      smooth.x = alg.x := by
    refine ⟨{ h_pos := alg.h_pos
              gamma_pos := alg.gamma_pos
              x := alg.x
              initial0 := alg.x 0
              initial1 := alg.x 1
              init0 := rfl
              init1 := rfl
              update := ?_ }, rfl⟩
    intro k
    rw [alg.update k]
    congr 1
    rw [alg.aux k, hz (k + 1), hz k]
  obtain ⟨smooth, hsmooth⟩ := hsmooth
  -- Paper (5.6) and (5.7) give `∇f_λ^M(x) = Aᵀ(A p x - b) + u` with `u ∈ ∂g(p x)`, where
  -- `p x = prox_{λg}(x - λ Aᵀ(Ax - b))` is the variable-metric proximal point.
  have hcomposite : ∀ x, ∃ u,
      u ∈ subdifferential G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) ∧
        gradient fLam x =
          A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) - b) + u := by
    intro x
    set p : H := lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x with hp
    have hM : M (x - p) = (x - p) - lam • A.adjoint (A (x - p)) := by
      rw [alg.metric]
      simp
    have hgrad' : gradient fLam x = (1 / lam) • M (x - p) := by
      rw [hgrad x, hp]
    have hmem : (lam)⁻¹ • ((x - lam • A.adjoint (A x - b)) - p) ∈ subdifferential G p := by
      have hres := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, alg.lam_pos⟩
        (x - lam • A.adjoint (A x - b))
      simpa [p, lassoProx] using hres
    refine ⟨(lam)⁻¹ • ((x - lam • A.adjoint (A x - b)) - p), hmem, ?_⟩
    rw [hgrad', hM, one_div]
    have hAdj : A.adjoint (A (x - p)) = A.adjoint (A x - b) - A.adjoint (A p - b) := by
      simp only [map_sub]
      abel
    rw [hAdj]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ alg.lam_pos.ne', one_smul]
    abel
  obtain ⟨xInf, Ebase, hEbase, hfinite, hlim, hcritical, hlen, _⟩ :=
    IPAHDD_finiteLength_and_critical fLam phi h gamma beta L r hdf smooth
      hfLam hLip hL_nonneg hbelowLam hpositive hgamma
  obtain ⟨u, hu, hgrad_eq⟩ := hcomposite xInf
  have hnormgrad : ‖gradient fLam xInf‖ ≤ r := by
    have hsub : -gradient fLam xInf ∈ subdifferential phi 0 := hcritical
    simpa only [norm_neg] using
      linear_dry_friction_subgradient_norm_le phi r hphi hdf.radius_pos hsub
  have hstationary :
      ‖A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) - b) + u‖ ≤ r := by
    rw [← hgrad_eq]
    exact hnormgrad
  refine ⟨xInf, Ebase, ?_, ?_, ?_, ?_, ⟨u, hu, hstationary⟩, ?_⟩
  · simpa [hsmooth] using hEbase
  · simpa [hsmooth] using hfinite
  · simpa [hsmooth] using hlim
  · simpa [hsmooth] using hlen
  · intro hgradstrict
    obtain ⟨kStop, hkStop⟩ := IPAHDD_geometric_and_finite fLam phi
      h gamma beta L r hdf smooth xInf hfLam hLip hL_nonneg hbelowLam hpositive
      hgamma hlim |>.2 hgradstrict
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa [hsmooth] using hkStop)
