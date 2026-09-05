import Mathlib
import Foundation.Differentiation.Gateaux
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3

namespace AttouchAdlyDryFrictionDynamics2023

open Filter Asymptotics

private lemma hasDerivAt_max_sq_zero {u : ℝ → ℝ} {u' t : ℝ}
    (hu : HasDerivAt u u' t) (hut : u t = 0) :
    HasDerivAt (fun s => max (u s) 0 ^ 2) 0 t := by
  rw [hasDerivAt_iff_isLittleO]
  rcases (isBigO_iff.mp hu.isBigO_sub) with ⟨c, hc⟩
  let C : ℝ := max c 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCbound : ∀ᶠ s in nhds t, ‖u s - u t‖ ≤ C * ‖s - t‖ := by
    filter_upwards [hc] with s hs
    exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hmaxsq : IsBigOWith (C * C) (nhds t)
      (fun s => max (u s) 0 ^ 2) (fun s => ‖s - t‖ ^ 2) := by
    apply IsBigOWith.of_bound
    filter_upwards [hCbound] with s hs
    have hmax_nonneg : 0 ≤ max (u s) 0 := le_max_right _ _
    have hmax_le : max (u s) 0 ≤ C * ‖s - t‖ := by
      rw [max_le_iff]
      constructor
      · rw [hut, sub_zero] at hs
        exact le_trans (le_abs_self _) hs
      · exact mul_nonneg (le_of_lt hC) (norm_nonneg _)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (max (u s) 0))]
    have hsq_bound : max (u s) 0 ^ 2 ≤ (C * ‖s - t‖) ^ 2 :=
      sq_le_sq₀ hmax_nonneg (mul_nonneg (le_of_lt hC) (norm_nonneg _)) |>.mpr hmax_le
    calc
      max (u s) 0 ^ 2 ≤ (C * ‖s - t‖) ^ 2 := hsq_bound
      _ = C * C * ‖‖s - t‖ ^ 2‖ := by
        simp only [Real.norm_eq_abs]
        simp
        nlinarith [sq_abs (s - t)]
  have hlittle : (fun s => max (u s) 0 ^ 2) =o[nhds t] (fun s => s - t) :=
    hmaxsq.trans_isLittleO (isLittleO_pow_sub_sub t (m := 2) (by norm_num)) (mul_pos hC hC)
  convert hlittle using 1
  · simp [hut]

private theorem frictionBall_not_mem_initial_infDist_pos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : H} {r : ℝ} (hr : 0 ≤ r) (hx : r < ‖x‖) :
    0 < Metric.infDist x (frictionBall r) := by
  have hnotmem : x ∉ frictionBall r := by
    intro hmem
    have hle : ‖x‖ ≤ r := by
      simpa [frictionBall, dist_zero_right] using hmem
    exact (not_le_of_gt hx) hle
  have hnonempty : (frictionBall (H := H) r).Nonempty := by
    simpa [frictionBall] using
      (Metric.nonempty_closedBall.mpr hr : (Metric.closedBall (0 : H) r).Nonempty)
  have hclosed : IsClosed (frictionBall (H := H) r) := by
    simpa [frictionBall] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) r))
  exact (hclosed.notMem_iff_infDist_pos hnonempty).mp hnotmem

private theorem weighted_energy_antitone {E : ℝ → ℝ} {a : ℝ}
    (hE : ∀ t, HasDerivAt E (deriv E t) t)
    (hineq : ∀ t, deriv E t + a * E t ≤ 0) :
    Antitone (fun t => Real.exp (a * t) * E t) := by
  apply antitone_of_deriv_nonpos
  · intro t
    have hdiff := (((hasDerivAt_id t).const_mul a).exp).differentiableAt.mul
      (hE t).differentiableAt
    simpa only [Pi.mul_apply, id_eq] using hdiff
  · intro t
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s))
        (Real.exp (a * t) * a) t := by
      simpa using (((hasDerivAt_id t).const_mul a).exp)
    have hformula : deriv (fun s : ℝ => Real.exp (a * s) * E s) t =
        Real.exp (a * t) * (deriv E t + a * E t) := by
      change deriv ((fun s : ℝ => Real.exp (a * s)) * E) t = _
      rw [(hexp.mul (hE t)).deriv]
      ring
    rw [hformula]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) (hineq t)

private theorem weighted_energy_monotone {E : ℝ → ℝ} {a : ℝ}
    (hE : ∀ t, HasDerivAt E (deriv E t) t)
    (hineq : ∀ t, 0 ≤ deriv E t + a * E t) :
    Monotone (fun t => Real.exp (a * t) * E t) := by
  apply monotone_of_deriv_nonneg
  · intro t
    have hdiff := (((hasDerivAt_id t).const_mul a).exp).differentiableAt.mul
      (hE t).differentiableAt
    simpa only [Pi.mul_apply, id_eq] using hdiff
  · intro t
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s))
        (Real.exp (a * t) * a) t := by
      simpa using (((hasDerivAt_id t).const_mul a).exp)
    have hderiv := hexp.mul (hE t)
    have hformula : deriv (fun s : ℝ => Real.exp (a * s) * E s) t =
        Real.exp (a * t) * (deriv E t + a * E t) := by
      change deriv ((fun s : ℝ => Real.exp (a * s)) * E) t = _
      rw [hderiv.deriv]
      ring
    rw [hformula]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hineq t)

private theorem coercive_bounds_of_posdef_finiteDim
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [Nontrivial H]
    (A : H →L[ℝ] H) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) :
    ∃ μ ν : ℝ, 0 < μ ∧ 0 < ν ∧ ∀ ξ : H,
      μ * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ ∧ inner ℝ (A ξ) ξ ≤ ν * ‖ξ‖ ^ 2 := by
  letI : ProperSpace H := FiniteDimensional.proper ℝ H
  obtain ⟨v, hv⟩ := exists_norm_eq H (show 0 ≤ (1 : ℝ) by norm_num)
  have hsphere : (Metric.sphere (0 : H) 1).Nonempty :=
    ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : H) 1).exists_isMinOn hsphere
      A.reApplyInnerSelf_continuous.continuousOn
  refine ⟨inner ℝ (A u) u, ‖A‖, ?_, ?_, ?_⟩
  · exact hpos u (by
      intro huz
      have : ‖u‖ = 0 := by simp [huz]
      linarith [mem_sphere_zero_iff_norm.mp hu])
  · have hAne : A ≠ 0 := by
      intro hA
      obtain ⟨x, hx⟩ := exists_ne (0 : H)
      have h := hpos x hx
      rw [hA] at h
      simp at h
    exact norm_pos_iff.mpr hAne
  · intro x
    constructor
    · by_cases hx : x = 0
      · simp [hx]
      · let w : H := ‖x‖⁻¹ • x
        have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hwnorm : ‖w‖ = 1 := by
          rw [show w = ‖x‖⁻¹ • x by rfl, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (le_of_lt hxnorm))]
          exact inv_mul_cancel₀ (ne_of_gt hxnorm)
        have hw : w ∈ Metric.sphere (0 : H) 1 := mem_sphere_zero_iff_norm.mpr hwnorm
        have hquad : inner ℝ (A u) u ≤ inner ℝ (A w) w := by
          simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hmin hw
        have hxrep : ‖x‖ • w = x := by
          dsimp [w]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxnorm), one_smul]
        have hscale : inner ℝ (A (‖x‖ • w)) (‖x‖ • w) =
            ‖x‖ ^ 2 * inner ℝ (A w) w := by
          simpa [ContinuousLinearMap.reApplyInnerSelf_apply, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg x)] using A.reApplyInnerSelf_smul w (c := ‖x‖)
        calc
          inner ℝ (A u) u * ‖x‖ ^ 2 ≤ inner ℝ (A w) w * ‖x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hquad (sq_nonneg ‖x‖)
          _ = inner ℝ (A (‖x‖ • w)) (‖x‖ • w) := by simpa [mul_comm] using hscale.symm
          _ = inner ℝ (A x) x := by rw [hxrep]
    · calc
        inner ℝ (A x) x ≤ ‖A x‖ * ‖x‖ := real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg x)
        _ = ‖A‖ * ‖x‖ ^ 2 := by ring

private theorem isInvertible_of_posdef_finiteDim
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [FiniteDimensional ℝ H] [Nontrivial H]
    (A : H →L[ℝ] H) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) :
    A.IsInvertible := by
  have hinj : Function.Injective A := by
    intro x y hxy
    by_contra hne
    have hp := hpos (x - y) (sub_ne_zero.mpr hne)
    rw [A.map_sub, hxy, sub_self] at hp
    simp at hp
  have hsurj : Function.Surjective A := by
    let L : H →ₗ[ℝ] H := A.toLinearMap
    have hLsurj : Function.Surjective L :=
      LinearMap.injective_iff_surjective.mp hinj
    intro y
    obtain ⟨x, hx⟩ := hLsurj y
    exact ⟨x, hx⟩
  let e : H ≃ₗ[ℝ] H := LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩
  let ec : H ≃L[ℝ] H := e.toContinuousLinearEquiv
  refine ⟨ec, ?_⟩
  ext x
  rfl

private theorem quadratic_completion_general
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A Ainv : H →L[ℝ] H) (hsymm : A.IsSymmetric)
    (hright : A.comp Ainv = ContinuousLinearMap.id ℝ H) (x y : H) :
    inner ℝ y x - inner ℝ (A x) x / 2 =
      inner ℝ (Ainv y) y / 2 - inner ℝ (A (x - Ainv y)) (x - Ainv y) / 2 := by
  have hy : A (Ainv y) = y := by simpa using congrArg (fun L => L y) hright
  have hcross : inner ℝ (A (Ainv y)) x = inner ℝ (A x) (Ainv y) := by
    calc
      inner ℝ (A (Ainv y)) x = inner ℝ (Ainv y) (A x) := by
        simpa using hsymm.apply_clm (Ainv y) x
      _ = inner ℝ (A x) (Ainv y) := real_inner_comm _ _
  have hquad : inner ℝ (Ainv y) y = inner ℝ (A (Ainv y)) (Ainv y) := by
    rw [hy]
    exact real_inner_comm _ _
  have hinner : inner ℝ y x = inner ℝ (A x) (Ainv y) := by
    calc
      inner ℝ y x = inner ℝ (A (Ainv y)) x := by rw [hy]
      _ = inner ℝ (A x) (Ainv y) := hcross
  rw [hinner, hquad, A.map_sub]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hcross]
  ring

private lemma ereal_sub_half_general (a b : ℝ) :
    (a : EReal) - ((b / 2 : ℝ) : EReal) = ((a - b / 2 : ℝ) : EReal) := by
  rw [EReal.coe_div, EReal.coe_sub, EReal.coe_div]

private theorem quadratic_conjugate_general
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A Ainv : H →L[ℝ] H) (hsymm : A.IsSymmetric)
    (hright : A.comp Ainv = ContinuousLinearMap.id ℝ H)
    (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) (y : H) :
    ERealFunction.conjugate (fun x => (inner ℝ (A x) x / 2 : ℝ) : H → EReal) y =
      ((inner ℝ (Ainv y) y / 2 : ℝ) : EReal) := by
  rw [ERealFunction.conjugate_apply_swap]
  apply le_antisymm
  · apply iSup_le
    intro x
    have hq : 0 ≤ inner ℝ (A (x - Ainv y)) (x - Ainv y) := by
      by_cases hz : x - Ainv y = 0
      · simp [hz]
      · exact le_of_lt (hpos _ hz)
    have hc := quadratic_completion_general A Ainv hsymm hright x y
    change ((inner ℝ y x : ℝ) : EReal) -
      ((inner ℝ (A x) x / 2 : ℝ) : EReal) ≤ _
    rw [ereal_sub_half_general, hc]
    exact EReal.coe_le_coe (by nlinarith)
  · apply le_iSup_of_le (Ainv y)
    have hc := quadratic_completion_general A Ainv hsymm hright (Ainv y) y
    have hz : inner ℝ (A (Ainv y - Ainv y)) (Ainv y - Ainv y) = 0 := by simp
    apply le_of_eq
    calc
      ((inner ℝ (Ainv y) y / 2 : ℝ) : EReal) =
          ((inner ℝ y (Ainv y) - inner ℝ (A (Ainv y)) (Ainv y) / 2 : ℝ) : EReal) := by
            rw [hc, hz]
            norm_num
      _ = ((inner ℝ y (Ainv y) : ℝ) : EReal) -
          ((inner ℝ (A (Ainv y)) (Ainv y) / 2 : ℝ) : EReal) := by
            rw [ereal_sub_half_general]

private theorem inverse_isSymmetric_of_posdef
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [FiniteDimensional ℝ H] [Nontrivial H]
    (A : H →L[ℝ] H) (hsymm : A.IsSymmetric)
    (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) :
    (A.inverse).IsSymmetric := by
  have hi := isInvertible_of_posdef_finiteDim A hpos
  have hright := hi.self_comp_inverse
  have hleft := hi.inverse_comp_self
  intro x y
  have hx : A (A.inverse x) = x := hi.self_apply_inverse x
  have hy : A (A.inverse y) = y := hi.self_apply_inverse y
  calc
    inner ℝ (A.inverse x) y = inner ℝ (A.inverse x) (A (A.inverse y)) := by rw [hy]
    _ = inner ℝ (A (A.inverse x)) (A.inverse y) := by
      simpa using (hsymm.apply_clm (A.inverse x) (A.inverse y)).symm
    _ = inner ℝ x (A.inverse y) := by rw [hx]

private theorem hessian_quadratic_conjugate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [FiniteDimensional ℝ H] [Nontrivial H]
    (A : H →L[ℝ] H) (hsymm : A.IsSymmetric)
    (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x) :
    fderiv ℝ (gradient (fun q =>
      (ERealFunction.conjugate (fun x => (inner ℝ (A x) x / 2 : ℝ) : H → EReal) q).toReal)) =
      fun _ => A.inverse := by
  let Ainv := A.inverse
  have hi := isInvertible_of_posdef_finiteDim A hpos
  have hright : A.comp Ainv = ContinuousLinearMap.id ℝ H := hi.self_comp_inverse
  have hinvsymm : Ainv.IsSymmetric := inverse_isSymmetric_of_posdef A hsymm hpos
  have hconj : ∀ y : H,
      ERealFunction.conjugate (fun x => (inner ℝ (A x) x / 2 : ℝ) : H → EReal) y =
        ((inner ℝ (Ainv y) y / 2 : ℝ) : EReal) := by
    intro y
    exact quadratic_conjugate_general A Ainv hsymm hright hpos y
  have hfun : (fun q =>
      (ERealFunction.conjugate (fun x => (inner ℝ (A x) x / 2 : ℝ) : H → EReal) q).toReal) =
      quadratic_affine_functional ((1 / 2 : ℝ) • Ainv) 0 := by
    funext y
    rw [hconj y]
    simp only [EReal.toReal_coe, one_div, quadratic_affine_functional_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_zero_right, sub_zero]
    rw [real_inner_smul_left]
    ring
  rw [hfun]
  funext y
  rw [fderiv_gradient_quadratic_affine_functional]
  have hadj : Ainv.adjoint = Ainv := LinearMap.IsSymmetric.clm_adjoint_eq hinvsymm
  ext x
  apply ext_inner_left ℝ
  intro y
  simp only [one_div, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, hadj]
  have hv : (2⁻¹ : ℝ) • Ainv x + (2⁻¹ : ℝ) • Ainv x = Ainv x := by
    rw [← add_smul]
    norm_num
  rw [hv]

/-- Theorem 3.3: exponential upper and lower bounds for the quadratic case.

The quadratic specialization is stated in the form used in the paper: the
primal energy is `f x = 1/2 ⟪A x, x⟫`, and the dual trajectory satisfies the
Hessian equation for the Foundation Fenchel conjugate of `f`.  Here Mathlib's
`fderiv ℝ (gradient ·)` is the Hessian operator.  The projector is represented
by the selected point `p t`.
-/
theorem theorem_3_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {t₀ r : ℝ} (hr : 0 < r) (A : H →L[ℝ] H) (f : H → ℝ)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (g p : ℝ → H)
    (hf_quadratic : ∀ x : H, f x = inner ℝ (A x) x / 2)
    (hg : Differentiable ℝ g)
    (hdualFlow : ∀ t, p t ∈ frictionBallProjector r (g t) ∧
      fderiv ℝ (gradient (fun q =>
        (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal))
        (g t) (deriv g t) + g t - p t = 0)
    (hinitial : r < ‖g t₀‖) :
    ∃ Cupper Clower μ ν : ℝ, 0 < Cupper ∧ 0 < Clower ∧ 0 < μ ∧ 0 < ν ∧
      (∀ t ∈ Set.Ici t₀, Metric.infDist (g t) (frictionBall r) ≤ Cupper * Real.exp (-μ * t)) ∧
      (∀ t ∈ Set.Ici t₀, Clower * Real.exp (-ν * t) ≤ Metric.infDist (g t) (frictionBall r)) ∧
      ∀ t ∈ Set.Ici t₀, g t ∉ frictionBall r := by
  obtain ⟨μ, ν, hμ, hν, hquad⟩ := coercive_bounds_of_posdef_finiteDim A hpos
  have hi := isInvertible_of_posdef_finiteDim A hpos
  have hHessian := hessian_quadratic_conjugate A hsymm hpos
  have hvel : ∀ t : ℝ, deriv g t = A (p t - g t) := by
    intro t
    have hflow := hdualFlow t |>.2
    have hH := congrFun hHessian (g t)
    have hsum : A.inverse (deriv g t) + g t = p t := by
      have hz : A.inverse (deriv g t) + g t - p t = 0 := by
        rw [← hH]
        simpa only [hf_quadratic] using hflow
      exact sub_eq_zero.mp hz
    have hinv : A.inverse (deriv g t) = p t - g t :=
      (eq_sub_iff_add_eq).2 hsum
    have happly := congrArg A hinv
    simpa [A.map_sub, hi.self_apply_inverse] using happly
  let E : ℝ → ℝ := fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2
  have hd0 : 0 < Metric.infDist (g t₀) (frictionBall r) :=
    frictionBall_not_mem_initial_infDist_pos (le_of_lt hr) hinitial
  have hEderiv : ∀ t, HasDerivAt E
      (- inner ℝ (g t - p t) (A (g t - p t))) t := by
    intro t
    have hdist_formula : ∀ s : ℝ,
        Metric.infDist (g s) (frictionBall r) = max (‖g s‖ - r) 0 :=
      fun s => infDist_frictionBall_eq r hr (g s)
    have hE_formula : E = fun s => max (‖g s‖ - r) 0 ^ 2 / 2 := by
      funext s
      simp [E, hdist_formula s]
    rw [hE_formula]
    by_cases hzero : g t = 0
    · have hnorm_cont : Tendsto (fun s => ‖g s‖) (nhds t) (nhds (0 : ℝ)) := by
        simpa [hzero] using ((hg t).continuousAt.norm.tendsto)
      have hlt : ∀ᶠ s in nhds t, ‖g s‖ < r := by
        filter_upwards [hnorm_cont.eventually (eventually_lt_nhds hr)] with s hs
        exact hs
      have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
      have hzero' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
        have hz := hconst.congr_of_eventuallyEq
          (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
            filter_upwards [hlt] with s hs
            rw [max_eq_right (sub_nonpos.mpr hs.le)]
            norm_num)
        simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
      have hp_eq : p t = 0 := by
        have hpdist := (hdualFlow t).1.2
        simp [hzero, infDist_frictionBall_eq r hr] at hpdist
        apply norm_eq_zero.mp
        simpa [hr.le] using hpdist
      convert hzero' using 1
      rw [hzero, hp_eq]
      simp
    · have hnorm_ne : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
      have hgderiv : HasDerivAt g (deriv g t) t := (hg t).hasDerivAt
      have hnorm_deriv : HasDerivAt (fun s => ‖g s‖)
          (inner ℝ (g t) (deriv g t) / ‖g t‖) t := by
        have hs := hgderiv.norm_sq.sqrt (pow_ne_zero 2 hnorm_ne)
        convert hs using 1
        all_goals simp [norm_nonneg]
        all_goals field_simp
      have hu : HasDerivAt (fun s => ‖g s‖ - r)
          (inner ℝ (g t) (deriv g t) / ‖g t‖) t := hnorm_deriv.sub_const r
      by_cases hout : r < ‖g t‖
      · have hpos : ∀ᶠ s in nhds t, 0 < ‖g s‖ - r := by
          have hcont : Tendsto (fun s => ‖g s‖ - r) (nhds t) (nhds (‖g t‖ - r)) :=
            hu.continuousAt
          filter_upwards [hcont.eventually (eventually_gt_nhds (sub_pos.mpr hout))] with s hs
          exact hs
        have hsq' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2)
            ((‖g t‖ - r) * (inner ℝ (g t) (deriv g t) / ‖g t‖)) t := by
          have hsq := (hu.pow 2).const_mul (1 / 2 : ℝ)
          have hsq0 := hsq.congr_of_eventuallyEq
            (show (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) =ᶠ[nhds t]
                (fun s => (1 / 2 : ℝ) * (‖g s‖ - r) ^ 2) by
              filter_upwards [hpos] with s hs
              rw [max_eq_left hs.le]
              ring)
          convert hsq0 using 1; ring
        have hp_eq : p t = (r / ‖g t‖) • g t := by
          have hp_can : p t = frictionBallProjection r hr (g t) := by
            exact (frictionBall_isChebyshev hr.le (g t)).choose_spec.2 _ (hdualFlow t).1
          rw [hp_can, frictionBallProjection_eq_sub_softThresholder r hr,
            softThresholder_apply, if_pos hout]
          module
        have hvel_inner : inner ℝ (g t - p t) (A (g t - p t)) =
            -((‖g t‖ - r) * (inner ℝ (g t) (deriv g t) / ‖g t‖)) := by
          have hvel_t := hvel t
          have hA : A (g t - p t) = -deriv g t := by
            rw [show g t - p t = -(p t - g t) by abel, map_neg, hvel_t]
          rw [hA, inner_neg_right, hp_eq]
          rw [show g t - ((r / ‖g t‖) • g t) =
            (1 - r / ‖g t‖) • g t by module]
          rw [real_inner_smul_left]
          field_simp
        convert hsq' using 1
        rw [hvel_inner]
        ring
      · have hle : ‖g t‖ ≤ r := not_lt.mp hout
        have hp_eq : p t = g t := by
          have hpdist := (hdualFlow t).1.2
          rw [infDist_frictionBall_eq r hr (g t), max_eq_right (sub_nonpos.mpr hle)] at hpdist
          have : dist (g t) (p t) = 0 := hpdist
          exact (sub_eq_zero.mp (by simpa [dist_eq_norm] using this)).symm
        have hvel_zero : deriv g t = 0 := by
          rw [hvel t, hp_eq, sub_self]
          simp
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
        have hzero' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
          by_cases heq : ‖g t‖ = r
          · have hz := hasDerivAt_max_sq_zero (hu := hu) (by linarith)
            simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
          · have hlt : ‖g t‖ < r := lt_of_le_of_ne hle heq
            have hpos : ∀ᶠ s in nhds t, ‖g s‖ - r < 0 := by
              filter_upwards [hu.continuousAt.eventually
                (eventually_lt_nhds (sub_neg.mpr hlt))] with s hs
              exact hs
            have hz := hconst.congr_of_eventuallyEq
              (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
                filter_upwards [hpos] with s hs
                rw [max_eq_right hs.le]
                norm_num)
            simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
        convert hzero' using 1
        rw [hp_eq]
        simp
  have hupperDiff : ∀ t, deriv E t + 2 * μ * E t ≤ 0 := by
    intro t
    have hq := (hquad (g t - p t)).1
    have hdist := (hdualFlow t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hlowerDiff : ∀ t, 0 ≤ deriv E t + 2 * ν * E t := by
    intro t
    have hq := (hquad (g t - p t)).2
    have hdist := (hdualFlow t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hEderiv' : ∀ t, HasDerivAt E (deriv E t) t := by
    intro t
    convert hEderiv t using 1
    exact (hEderiv t).deriv
  have hlowerDistance : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) ≤
        Metric.infDist (g t) (frictionBall r) := by
    intro t ht
    have henergy : E t₀ * Real.exp (-(2 * ν) * (t - t₀)) ≤ E t := by
      have hdiv : (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) ≤ E t :=
        (div_le_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_monotone hEderiv' hlowerDiff ht)
      calc
        E t₀ * Real.exp (-(2 * ν) * (t - t₀)) =
            E t₀ * (Real.exp (2 * ν * t₀) / Real.exp (2 * ν * t)) := by
              rw [← Real.exp_sub]
              congr 2; ring
        _ = (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) := by ring
        _ ≤ E t := hdiv
    have hsq : Metric.infDist (g t₀) (frictionBall r) ^ 2 *
        Real.exp (-(2 * ν) * (t - t₀)) ≤ Metric.infDist (g t) (frictionBall r) ^ 2 := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-ν * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * ν) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    exact (sq_le_sq₀ (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))
      Metric.infDist_nonneg).mp (by rwa [hident])
  refine ⟨Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀),
    Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀), μ, ν,
    mul_pos hd0 (Real.exp_pos _), mul_pos hd0 (Real.exp_pos _), hμ, hν, ?_, ?_, ?_⟩
  · intro t ht
    have henergy : E t ≤ E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by
      have hdiv : E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_antitone hEderiv' hupperDiff ht)
      calc
        E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) := hdiv
        _ = E t₀ * (Real.exp (2 * μ * t₀) / Real.exp (2 * μ * t)) := by ring
        _ = E t₀ * Real.exp (2 * μ * t₀ - 2 * μ * t) := by rw [Real.exp_sub]
        _ = E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by congr 2; ring
    have hsq : Metric.infDist (g t) (frictionBall r) ^ 2 ≤
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-μ * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    have hdist : Metric.infDist (g t) (frictionBall r) ≤
        Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) :=
      (sq_le_sq₀ Metric.infDist_nonneg
        (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))).mp
        (by rwa [hident])
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀) * Real.exp (-μ * t) =
          Metric.infDist (g t₀) (frictionBall r) *
            (Real.exp (μ * t₀) * Real.exp (-μ * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀ + -μ * t) := by
        rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) := by congr 2; ring
  · intro t ht
    have hdist := hlowerDistance t ht
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀) * Real.exp (-ν * t) =
          Metric.infDist (g t₀) (frictionBall r) *
            (Real.exp (ν * t₀) * Real.exp (-ν * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀ + -ν * t) := by
        rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) := by congr 2; ring
  · intro t ht hmem
    have hlower := hlowerDistance t ht
    have hposdist : 0 < Metric.infDist (g t) (frictionBall r) :=
      lt_of_lt_of_le (mul_pos hd0 (Real.exp_pos _)) hlower
    have hzero := Metric.infDist_zero_of_mem hmem
    linarith

end AttouchAdlyDryFrictionDynamics2023
