import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.prop_4
import Mathlib

namespace AbbasDynamical2015

open scoped Gradient

private theorem convex_supporting_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (grad : H → H)
    (hconvex : ConvexOn ℝ Set.univ f) (hgrad : ∀ z, HasGradientAt f (grad z) z)
    (z u : H) : f z + inner ℝ (grad z) (u - z) ≤ f u := by
  let phi : ℝ → ℝ := f ∘ AffineMap.lineMap z u
  have hphi_convex : ConvexOn ℝ Set.univ phi := by
    simpa [phi] using hconvex.comp_affineMap (AffineMap.lineMap z u)
  have hpath : HasDerivAt (fun t : ℝ ↦ z + t • (u - z)) (u - z) 0 := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const (𝕜 := ℝ) 0 z).add ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (u - z))
  have houter : HasFDerivAt f (InnerProductSpace.toDual ℝ H (grad z))
      ((fun t : ℝ ↦ z + t • (u - z)) 0) := by
    simpa using (hgrad z).hasFDerivAt
  have hphi_deriv : HasDerivAt phi (inner ℝ (grad z) (u - z)) 0 := by
    simpa [phi, Function.comp_def, AffineMap.lineMap_apply, add_comm, one_smul, add_zero,
      InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt 0 houter hpath
  have hslope := hphi_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hphi_deriv
  have h : inner ℝ (grad z) (u - z) ≤ f u - f z := by
    simpa [phi, slope, Function.comp_def, AffineMap.lineMap_apply, zero_smul, one_smul,
      zero_add, add_zero] using hslope
  linarith

private theorem gradient_monotone_of_convex_differentiable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → ℝ) (hconvex : ConvexOn ℝ Set.univ Phi)
    (hgradient : Differentiable ℝ Phi) :
    ∀ x y : H, 0 ≤ inner ℝ (∇ Phi x - ∇ Phi y) (x - y) := by
  have hgradAt : ∀ q : H, HasGradientAt Phi (∇ Phi q) q := fun q =>
    (hgradient q).hasGradientAt
  intro x y
  have hxy := convex_supporting_local Phi (fun q => ∇ Phi q)
    hconvex hgradAt x y
  have hyx := convex_supporting_local Phi (fun q => ∇ Phi q)
    hconvex hgradAt y x
  rw [inner_sub_left]
  have h : inner ℝ (∇ Phi y) (x - y) = -inner ℝ (∇ Phi y) (y - x) := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  have hx : inner ℝ (∇ Phi x) (x - y) = -inner ℝ (∇ Phi x) (y - x) := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  linarith

private theorem gradient_derivative_inner_nonnegative {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → ℝ) (hconvex : ConvexOn ℝ Set.univ Phi)
    (hgradient : Differentiable ℝ Phi) (x : ℝ → H) {t : ℝ} {dx dv : H}
    (hx : HasDerivAt x dx t)
    (hv : HasDerivAt (fun s => ∇ Phi (x s)) dv t) :
    0 ≤ inner ℝ dx dv := by
  let qx : ℝ → H := fun h => h⁻¹ • (x (t + h) - x t)
  let qv : ℝ → H := fun h => h⁻¹ • (∇ Phi (x (t + h)) - ∇ Phi (x t))
  have hqx : Filter.Tendsto qx (nhdsWithin 0 {0}ᶜ) (nhds dx) := by
    simpa [qx, add_comm] using hx.tendsto_slope_zero
  have hqv : Filter.Tendsto qv (nhdsWithin 0 {0}ᶜ) (nhds dv) := by
    simpa [qv, add_comm] using hv.tendsto_slope_zero
  have hlim : Filter.Tendsto (fun h => inner ℝ (qx h) (qv h))
      (nhdsWithin 0 {0}ᶜ) (nhds (inner ℝ dx dv)) := hqx.inner hqv
  rw [← neg_nonpos]
  apply le_of_tendsto hlim.neg
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ⟨1, zero_lt_one, ?_⟩
  intro h _ hne
  have hmono := gradient_monotone_of_convex_differentiable Phi hconvex hgradient
    (x (t + h)) (x t)
  dsimp only [qx, qv]
  rw [real_inner_smul_left, inner_smul_right]
  have hrewrite : h⁻¹ * (h⁻¹ * inner ℝ (x (t + h) - x t)
      (∇ Phi (x (t + h)) - ∇ Phi (x t))) =
      (h⁻¹ * h⁻¹) * inner ℝ (∇ Phi (x (t + h)) - ∇ Phi (x t))
        (x (t + h) - x t) := by
    rw [real_inner_comm]
    ring
  rw [hrewrite]
  exact neg_nonpos.mpr (mul_nonneg (mul_self_nonneg _) hmono)

private theorem newton_gradient_exponential_rate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → ℝ) (x : ℝ → H) (c : ℝ)
    (hconvex : ConvexOn ℝ Set.univ Phi) (hgradient : Differentiable ℝ Phi)
    (hc : 0 < c) (hmin : ∃ z : H, ∀ y : H, Phi z ≤ Phi y)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hv : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => ∇ Phi (x s)) (deriv (fun s => ∇ Phi (x s)) t) t)
    (hsys : ∀ t, 0 ≤ t → (c * Real.exp (-t)) • deriv x t +
      deriv (fun s => ∇ Phi (x s)) t + ∇ Phi (x t) = 0) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖∇ Phi (x t)‖ ≤ C * Real.exp (-t) := by
  rcases hmin with ⟨z, hz⟩
  let v : ℝ → H := fun s => ∇ Phi (x s)
  let p : ℝ → H := fun s => x s + (c⁻¹ * Real.exp s) • v s
  have hcoef : ∀ t : ℝ, (c⁻¹ * Real.exp t) * (c * Real.exp (-t)) = 1 := by
    intro t
    field_simp [hc.ne']
    rw [← Real.exp_add]
    simp
  have hpderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt p 0 s := by
    intro s hs
    have ha : HasDerivAt (fun r : ℝ => c⁻¹ * Real.exp r) (c⁻¹ * Real.exp s) s := by
      convert ((hasDerivAt_const s c⁻¹).mul (Real.hasDerivAt_exp s)) using 1; ring
    have hraw := (hx s hs).add (ha.smul (hv s hs))
    have hzero : deriv x s + (c⁻¹ * Real.exp s) • deriv (fun r => ∇ Phi (x r)) s +
        (c⁻¹ * Real.exp s) • ∇ Phi (x s) = 0 := by
      have h := congrArg (fun w : H => (c⁻¹ * Real.exp s) • w) (hsys s hs)
      simpa [smul_add, smul_smul, hcoef] using h
    simpa only [p, v] using hraw.congr_deriv (by
      simpa [smul_add, add_assoc, add_left_comm, add_comm] using hzero)
  have hpconst : ∀ t : ℝ, 0 ≤ t → p t = p 0 := by
    intro t ht
    apply constant_of_has_deriv_right_zero
      (fun s hs => (hpderiv s hs.1).continuousAt.continuousWithinAt)
    · intro s hs
      exact (hpderiv s hs.1).hasDerivWithinAt
    · exact ⟨ht, le_rfl⟩
  refine ⟨c * ‖p 0 - z‖, ?_⟩
  intro t ht
  have hgradAt : ∀ q : H, HasGradientAt Phi (∇ Phi q) q := fun q =>
    (hgradient q).hasGradientAt
  have hsupport := convex_supporting_local Phi (fun q => ∇ Phi q)
    hconvex hgradAt (x t) z
  have hpair : 0 ≤ inner ℝ (v t) (x t - z) := by
    dsimp [v] at hsupport ⊢
    rw [show z - x t = -(x t - z) by abel, inner_neg_right] at hsupport
    linarith [hz (x t)]
  have hmain : (c⁻¹ * Real.exp t) * ‖v t‖ ^ 2 ≤ inner ℝ (v t) (p 0 - z) := by
    rw [← hpconst t ht]
    dsimp [p]
    rw [show x t + (c⁻¹ * Real.exp t) • v t - z =
      (x t - z) + (c⁻¹ * Real.exp t) • v t by abel]
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linarith
  have ha_pos : 0 < c⁻¹ * Real.exp t := mul_pos (inv_pos.mpr hc) (Real.exp_pos _)
  have hbound : ‖v t‖ ≤ (c * Real.exp (-t)) * ‖p 0 - z‖ := by
    by_cases hvzero : ‖v t‖ = 0
    · simp [hvzero, mul_nonneg, hc.le, (Real.exp_pos _).le]
    have hlin : (c⁻¹ * Real.exp t) * ‖v t‖ ≤ ‖p 0 - z‖ := by
      apply le_of_mul_le_mul_right _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hvzero))
      nlinarith [hmain, real_inner_le_norm (v t) (p 0 - z)]
    have hinv : (c⁻¹ * Real.exp t)⁻¹ = c * Real.exp (-t) := by
      field_simp [hc.ne', Real.exp_ne_zero]
      rw [← Real.exp_add]
      simp
    have hdiv : ‖v t‖ ≤ ‖p 0 - z‖ / (c⁻¹ * Real.exp t) :=
      (le_div_iff₀ ha_pos).2 (by simpa [mul_comm] using hlin)
    rw [div_eq_mul_inv, hinv] at hdiv
    simpa [mul_comm] using hdiv
  simpa only [v, mul_assoc, mul_left_comm, mul_comm] using hbound

private theorem semigroup_gradient_rate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Phi : H → ℝ) (x : ℝ → H)
    (hconvex : ConvexOn ℝ Set.univ Phi) (hgradient : Differentiable ℝ Phi)
    (hmin : ∃ z : H, ∀ y : H, Phi z ≤ Phi y)
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (-∇ Phi (x t)) t)
    (hv : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => ∇ Phi (x s)) (deriv (fun s => ∇ Phi (x s)) t) t) :
    ∃ C : ℝ, ∀ t, 0 < t → ‖∇ Phi (x t)‖ ≤ C / t := by
  rcases hmin with ⟨z, hz⟩
  let v : ℝ → H := fun s => ∇ Phi (x s)
  let E : ℝ → ℝ := fun s => Phi (x s) - Phi z
  let D : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖x s - z‖ ^ 2
  have hgradAt : ∀ q : H, HasGradientAt Phi (∇ Phi q) q := fun q =>
    (hgradient q).hasGradientAt
  have hvnorm_deriv : ∀ s, 0 ≤ s →
      HasDerivAt (fun r => ‖v r‖ ^ 2)
        (2 * inner ℝ (v s) (deriv v s)) s := by
    intro s hs
    simpa only [v] using (hv s hs).norm_sq
  have hvpair : ∀ s, 0 ≤ s → 0 ≤ inner ℝ (-v s) (deriv v s) := by
    intro s hs
    simpa only [v] using gradient_derivative_inner_nonnegative Phi hconvex hgradient x
      (hx s hs) (hv s hs)
  have hnorm_sq_anti : AntitoneOn (fun s => ‖v s‖ ^ 2) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s hs
      exact (hvnorm_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      exact (hvnorm_deriv s hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      rw [(hvnorm_deriv s hs0).deriv]
      have h := hvpair s hs0
      rw [inner_neg_left] at h
      nlinarith
  have hEderiv : ∀ s, 0 ≤ s → HasDerivAt E (-‖v s‖ ^ 2) s := by
    intro s hs
    have hraw := HasFDerivAt.comp_hasDerivAt s (hgradAt (x s)).hasFDerivAt (hx s hs)
    simpa [E, v, real_inner_self_eq_norm_sq, InnerProductSpace.toDual_apply_apply] using
      hraw.sub_const (Phi z)
  have hEanti : AntitoneOn E (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s hs
      exact (hEderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      exact (hEderiv s hs0).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      rw [(hEderiv s hs0).deriv]
      exact neg_nonpos.mpr (sq_nonneg _)
  have hDderiv : ∀ s, 0 ≤ s →
      HasDerivAt D (-inner ℝ (v s) (x s - z)) s := by
    intro s hs
    have hraw := ((hx s hs).sub_const z).norm_sq.const_mul (1 / 2 : ℝ)
    simpa [D, v, real_inner_comm] using hraw
  have hsupport : ∀ s, E s ≤ inner ℝ (v s) (x s - z) := by
    intro s
    have h := convex_supporting_local Phi (fun q => ∇ Phi q)
      hconvex hgradAt (x s) z
    dsimp [E, v] at h ⊢
    rw [show z - x s = -(x s - z) by abel, inner_neg_right] at h
    linarith [hz (x s)]
  have hDle : ∀ s, 0 ≤ s → deriv D s ≤ -E s := by
    intro s hs
    rw [(hDderiv s hs).deriv]
    linarith [hsupport s]
  have hEnonneg : ∀ s, 0 ≤ E s := by
    intro s
    dsimp [E]
    linarith [hz (x s)]
  have hDnonneg : ∀ s, 0 ≤ D s := by
    intro s
    dsimp [D]
    positivity
  have hQbound : ∀ s, 0 ≤ s → s * E s ≤ D 0 := by
    let Q : ℝ → ℝ := D + id * E
    have hQderiv : ∀ r, 0 ≤ r →
        HasDerivAt Q (-inner ℝ (v r) (x r - z) + E r + r * (-‖v r‖ ^ 2)) r := by
      intro r hr
      have hraw := (hDderiv r hr).add ((hasDerivAt_id r).mul (hEderiv r hr))
      change HasDerivAt (D + id * E) _ r
      convert hraw using 1; simp only [id_eq]; ring
    have hQanti : AntitoneOn Q (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro r hr
        exact (hQderiv r hr).continuousAt.continuousWithinAt
      · intro r hr
        have hr0 : 0 ≤ r := interior_subset hr
        exact (hQderiv r hr0).differentiableAt.differentiableWithinAt
      · intro r hr
        have hr0 : 0 ≤ r := interior_subset hr
        rw [(hQderiv r hr0).deriv]
        have hsup := hsupport r
        have hsq : 0 ≤ r * ‖v r‖ ^ 2 := mul_nonneg hr0 (sq_nonneg _)
        linarith
    intro s hs
    have hQ : Q s ≤ Q 0 := hQanti (by simp) hs hs
    change D s + s * E s ≤ D 0 + 0 * E 0 at hQ
    norm_num at hQ
    linarith [hDnonneg s]
  refine ⟨Real.sqrt 2 * ‖x 0 - z‖, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := ht.le
  let a : ℝ := t / 2
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha0 : 0 ≤ a := ha_pos.le
  have hEbound : E a ≤ ‖x 0 - z‖ ^ 2 / t := by
    have hQa : a * E a ≤ D 0 := hQbound a ha0
    simp [D, a] at hQa
    apply (le_div_iff₀ ht).2
    nlinarith
  let R : ℝ → ℝ := fun s => E s + ‖v t‖ ^ 2 * (s - a)
  have hRderiv : ∀ s, a ≤ s → s ≤ t →
      HasDerivAt R (-‖v s‖ ^ 2 + ‖v t‖ ^ 2) s := by
    intro s hs _
    have hlinear := ((hasDerivAt_id s).sub_const a).const_mul (‖v t‖ ^ 2)
    have hraw := (hEderiv s (le_trans ha0 hs)).add hlinear
    simpa [R, sub_eq_add_neg, mul_add, mul_assoc, add_assoc, add_left_comm, add_comm] using hraw
  have hRanti : AntitoneOn R (Set.Icc a t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a t)
    · intro s hs
      exact (hRderiv s hs.1 hs.2).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : a < s ∧ s < t := by simpa [interior_Icc] using hs
      exact (hRderiv s hs'.1.le hs'.2.le).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : a < s ∧ s < t := by simpa [interior_Icc] using hs
      rw [(hRderiv s hs'.1.le hs'.2.le).deriv]
      have hanti := hnorm_sq_anti (le_trans ha0 hs'.1.le) ht0 hs'.2.le
      nlinarith
  have ha_le_t : a ≤ t := by
    dsimp [a]
    linarith
  have hR : R t ≤ R a := hRanti ⟨le_rfl, ha_le_t⟩ ⟨ha_le_t, le_rfl⟩ ha_le_t
  have hgrad_sq : ‖v t‖ ^ 2 ≤ (2 * ‖x 0 - z‖ ^ 2) / t ^ 2 := by
    dsimp [R] at hR
    have hEt : 0 ≤ E t := hEnonneg t
    have hhalf : t - a = t / 2 := by dsimp [a]; ring
    rw [hhalf] at hR
    have hstep : (t / 2) * ‖v t‖ ^ 2 ≤ E a := by linarith
    have hbound_mul : t * E a ≤ ‖x 0 - z‖ ^ 2 := by
      simpa [mul_comm] using (le_div_iff₀ ht).mp hEbound
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    nlinarith [mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * t by positivity)]
  dsimp [v] at hgrad_sq ⊢
  have hright : 0 ≤ (Real.sqrt 2 * ‖x 0 - z‖) / t :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) ht0
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [div_pow]
  convert hgrad_sq using 1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Remark 4.3: gradient-rate estimates for the two dynamics when `B = 0`. -/
theorem gradient_rate_comparison {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → ℝ) (xSemigroup xNewton : ℝ → H) (c : ℝ)
    (hconvex : ConvexOn ℝ Set.univ Phi) (hgradient : Differentiable ℝ Phi)
    (hc : 0 < c)
    (hmin : ∃ z : H, ∀ y : H, Phi z ≤ Phi y)
    (hsemigroup : ∀ t, 0 ≤ t → HasDerivAt xSemigroup (-∇ Phi (xSemigroup t)) t)
    (hsemigroup_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xSemigroup s))
        (deriv (fun s ↦ ∇ Phi (xSemigroup s)) t) t)
    (hnewton_xclassical : ∀ t, 0 ≤ t → HasDerivAt xNewton (deriv xNewton t) t)
    (hnewton_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xNewton s)) (deriv (fun s ↦ ∇ Phi (xNewton s)) t) t)
    (hnewton : ∀ t, 0 ≤ t → (c * Real.exp (-t)) • deriv xNewton t +
      deriv (fun s ↦ ∇ Phi (xNewton s)) t + ∇ Phi (xNewton t) = 0) :
    (∃ C : ℝ, ∀ t, 0 < t → ‖∇ Phi (xSemigroup t)‖ ≤ C / t) ∧
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖∇ Phi (xNewton t)‖ ≤ C * Real.exp (-t) := by
  refine ⟨?_, newton_gradient_exponential_rate Phi xNewton c hconvex hgradient hc hmin
    hnewton_xclassical hnewton_vclassical hnewton⟩
  exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup
    hsemigroup_vclassical

end AbbasDynamical2015
