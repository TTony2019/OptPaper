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
Theorem 5.1:
the variable-metric Lasso trajectory inherits the IPAHDD
finite-length and finite-stopping conclusions from its envelope realization.
-/
theorem IPAHDDLasso_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi fLam : H → ℝ) (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H)
    (normA h gamma beta lam r L : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDLasso phi.toEReal hdf.toEReal_mem_gammaZero G hG A M b normA lam h gamma beta)
    (hphi : ∀ x, phi x = r * ‖x‖)
    (hfLam : ContDiff ℝ 1 fLam)
    (hLip : HasLipschitzGradient (gradient fLam) L) (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ fLam x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hsmooth : ∃ smooth : IPAHDD fLam phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta,
      smooth.x = alg.x)
    (hgrad : ∀ x, gradient fLam x =
      (1 / lam) • M (x - lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x)) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} => ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      (∃ u, u ∈ subdifferential G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) ∧
        ‖A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) - b) + u‖ ≤ r) ∧
      (‖gradient fLam xInf‖ < r -> IsFinitelyConvergent alg.x) := by
  rcases hsmooth with ⟨smooth, hsmooth⟩
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
      hfLam hLip hL_nonneg hbelow hpositive hgamma
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
      h gamma beta L r hdf smooth xInf hfLam hLip hL_nonneg hbelow hpositive
      hgamma hlim |>.2 hgradstrict
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa [hsmooth] using hkStop)
