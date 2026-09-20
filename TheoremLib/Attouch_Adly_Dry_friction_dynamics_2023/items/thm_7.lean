import Mathlib
import Foundation.Differentiation.Gateaux
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_5

namespace AttouchAdlyDryFrictionDynamics2023

open Filter Asymptotics

private theorem hasDerivAt_max_sq_zero {u : ℝ → ℝ} {u' t : ℝ}
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
  simp [hut]

private theorem quadratic_gradient_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (f : H → ℝ)
    (hf : ∀ u : H, f u = inner ℝ (A u) u / 2) (hsymm : A.IsSymmetric) :
    gradient f = A := by
  have hfun : f = quadratic_affine_functional ((1 / 2 : ℝ) • A) 0 := by
    funext u
    rw [hf u]
    simp only [quadratic_affine_functional_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, inner_zero_right, sub_zero, real_inner_smul_left]
    ring
  rw [hfun, gradient_quadratic_affine_functional]
  ext u
  apply ext_inner_left ℝ
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    sub_zero, inner_add_right, real_inner_smul_right]
  have hadj_inner : inner ℝ v ((ContinuousLinearMap.adjoint ((1 / 2 : ℝ) • A)) u) =
      (1 / 2 : ℝ) * inner ℝ v (A u) := by
    rw [real_inner_comm]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, real_inner_smul_right]
    rw [← (hsymm.apply_clm u v), real_inner_comm]
  rw [hadj_inner]
  ring

private theorem friction_distance_sq_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {r : ℝ} (hr : 0 < r) (g : ℝ → H) (p : H) {t : ℝ}
    (hg : DifferentiableAt ℝ g t) (hp : p ∈ frictionBallProjector r (g t)) :
    HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2)
      (inner ℝ (g t - p) (deriv g t)) t := by
  by_cases hzero : g t = 0
  · have hnorm_cont : Filter.Tendsto (fun s => ‖g s‖) (nhds t) (nhds (0 : ℝ)) := by
      simpa [hzero] using hg.continuousAt.norm.tendsto
    have hlt : ∀ᶠ s in nhds t, ‖g s‖ < r := by
      filter_upwards [hnorm_cont.eventually (eventually_lt_nhds hr)] with s hs
      exact hs
    have henergy : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
      have hz := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
          filter_upwards [hlt] with s hs
          rw [max_eq_right (sub_nonpos.mpr hs.le)]
          norm_num)
      simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
    have hp_eq : p = 0 := by
      have hpdist := hp.2
      simp [hzero, infDist_frictionBall_eq r hr] at hpdist
      apply norm_eq_zero.mp
      simpa [dist_eq_norm, hr.le] using hpdist
    convert henergy using 1
    simp [hzero, hp_eq]
  · have hnorm_ne : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
    have hgderiv : HasDerivAt g (deriv g t) t := hg.hasDerivAt
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
        filter_upwards [hu.continuousAt.eventually
          (eventually_gt_nhds (sub_pos.mpr hout))] with s hs
        exact hs
      have henergy : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2)
          ((‖g t‖ - r) * (inner ℝ (g t) (deriv g t) / ‖g t‖)) t := by
        have hsq := (hu.pow 2).const_mul (1 / 2 : ℝ)
        have hsq0 := hsq.congr_of_eventuallyEq
          (show (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) =ᶠ[nhds t]
              (fun s => (1 / 2 : ℝ) * (‖g s‖ - r) ^ 2) by
            filter_upwards [hpos] with s hs
            rw [max_eq_left hs.le]
            ring)
        convert hsq0 using 1
        all_goals ring
      have hp_eq : p = (r / ‖g t‖) • g t := by
        have hp_can : p = frictionBallProjection r hr (g t) :=
          (frictionBall_isChebyshev hr.le (g t)).choose_spec.2 _ hp
        rw [hp_can, frictionBallProjection_eq_sub_softThresholder r hr,
          softThresholder_apply, if_pos hout]
        module
      convert henergy using 1
      rw [hp_eq, show g t - (r / ‖g t‖) • g t =
        (1 - r / ‖g t‖) • g t by module, real_inner_smul_left]
      field_simp
    · have hle : ‖g t‖ ≤ r := not_lt.mp hout
      have hp_eq : p = g t := by
        have hpdist := hp.2
        rw [infDist_frictionBall_eq r hr (g t), max_eq_right (sub_nonpos.mpr hle)] at hpdist
        exact (dist_eq_zero.mp hpdist).symm
      have henergy : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
        by_cases heq : ‖g t‖ = r
        · have hz := hasDerivAt_max_sq_zero (hu := hu) (by linarith)
          simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
        · have hlt : ‖g t‖ < r := lt_of_le_of_ne hle heq
          have hneg : ∀ᶠ s in nhds t, ‖g s‖ - r < 0 := by
            filter_upwards [hu.continuousAt.eventually
              (eventually_lt_nhds (sub_neg.mpr hlt))] with s hs
            exact hs
          have hz := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
            (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
              filter_upwards [hneg] with s hs
              rw [max_eq_right hs.le]
              norm_num)
          simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
      convert henergy using 1
      simp [hp_eq]

/-- Theorem 4.3: a quadratic DRYSTAR trajectory has an `exp (-μ s²)` residual rate. -/
theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (A : H →L[ℝ] H) (f : H → ℝ)
    (hf_quadratic : ∀ u : H, f u = inner ℝ (A u) u / 2)
    (hsymm : A.IsSymmetric)
    (hpos : ∃ m : ℝ, 0 < m ∧ ∀ u : H, m * ‖u‖ ^ 2 ≤ inner ℝ (A u) u)
    (x : ℝ → H) (hx : ContDiff ℝ 2 x)
    (hsolution : ∃ p : ℝ → H, IsDryStarTrajectory r α s₀ f x p) :
    ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ ∀ s ∈ Set.Ici s₀,
      Metric.infDist (gradient f (x s + (s / (α - 1)) • deriv x s)) (frictionBall r) ≤
        C * Real.exp (-μ * s ^ 2) := by
  obtain ⟨p, hsolution⟩ := hsolution
  obtain ⟨m, hm, hcoercive⟩ := hpos
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have hgradient : gradient f = A := quadratic_gradient_eq A f hf_quadratic hsymm
  let y : ℝ → H := fun s => x s + (s / (α - 1)) • deriv x s
  let g : ℝ → H := fun s => A (y s)
  let E : ℝ → ℝ := fun s => max (‖g s‖ - r) 0 ^ 2 / 2
  let k : ℝ := m / (α - 1)
  have hx_diff : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hdx_diff : Differentiable ℝ (deriv x) := by
    have h := (contDiff_nat_iff_iteratedDeriv.mp hx).2 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  have hy_deriv : ∀ s : ℝ, HasDerivAt y
      (deriv x s + (1 / (α - 1)) • deriv x s +
        (s / (α - 1)) • deriv (deriv x) s) s := by
    intro s
    dsimp [y]
    convert (hx_diff s).hasDerivAt.add
      ((hasDerivAt_id s).div_const (α - 1) |>.smul (hdx_diff s).hasDerivAt) using 1
    all_goals
      simp
      module
  have hg_deriv : ∀ s : ℝ, HasDerivAt g
      (A (deriv x s + (1 / (α - 1)) • deriv x s +
        (s / (α - 1)) • deriv (deriv x) s)) s := by
    intro s
    simpa [g, Function.comp_def] using A.hasFDerivAt.comp_hasDerivAt s (hy_deriv s)
  have hg_diff : Differentiable ℝ g := fun s => (hg_deriv s).differentiableAt
  have hflow : ∀ s ∈ Set.Ici s₀,
      deriv g s = (s / (α - 1)) • A (p s - g s) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have heq := (hsolution s hs).2
    rw [hgradient] at heq
    change deriv (deriv x) s + (α / s) • deriv x s + g s - p s = 0 at heq
    have hacc : deriv (deriv x) s + (α / s) • deriv x s = p s - g s := by
      apply (eq_sub_iff_add_eq).2
      exact sub_eq_zero.mp heq
    rw [(hg_deriv s).deriv]
    rw [← hacc]
    simp only [map_add, map_smul, smul_add, smul_smul]
    have hcoeff : 1 + 1 / (α - 1) = (s / (α - 1)) * (α / s) := by
      field_simp [ne_of_gt hα1, ne_of_gt hspos]
      ring
    rw [← hcoeff]
    module
  have hE_deriv : ∀ s ∈ Set.Ici s₀, HasDerivAt E
      (-((s / (α - 1)) * inner ℝ (g s - p s) (A (g s - p s)))) s := by
    intro s hs
    have hp : p s ∈ frictionBallProjector r (g s) := by
      simpa [g, y, hgradient] using (hsolution s hs).1
    have hdist := friction_distance_sq_hasDerivAt hr g (p s) (hg_diff s) hp
    have hvel := hflow s hs
    rw [hvel] at hdist
    change HasDerivAt E _ s at hdist
    convert hdist using 1
    rw [show p s - g s = -(g s - p s) by abel, map_neg, real_inner_smul_right,
      inner_neg_right]
    ring
  have hE_diff_ineq : ∀ s ∈ Set.Ici s₀,
      deriv E s + 2 * m * (s / (α - 1)) * E s ≤ 0 := by
    intro s hs
    have hsnonneg : 0 ≤ s / (α - 1) :=
      div_nonneg (le_trans (le_of_lt hs₀) hs) hα1.le
    have hco := hcoercive (g s - p s)
    have hscaled := mul_le_mul_of_nonneg_left hco hsnonneg
    have hnorm : ‖g s - p s‖ = Metric.infDist (g s) (frictionBall r) := by
      have hp : p s ∈ frictionBallProjector r (g s) := by
        simpa [g, y, hgradient] using (hsolution s hs).1
      simpa [dist_eq_norm] using hp.2
    rw [(hE_deriv s hs).deriv]
    rw [hnorm] at hscaled
    rw [infDist_frictionBall_eq r hr] at hscaled
    rw [real_inner_comm] at hscaled
    dsimp [E]
    nlinarith
  let W : ℝ → ℝ := fun s => Real.exp (k * s ^ 2) * E s
  have hW_cont : Continuous W := by
    dsimp [W, E]
    exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).mul
      (((hg_diff.continuous.norm.sub continuous_const).max continuous_const).pow 2 |>.div_const 2))
  have hW_deriv : ∀ s ∈ Set.Ici s₀, HasDerivAt W
      (Real.exp (k * s ^ 2) * (2 * m * (s / (α - 1)) * E s + deriv E s)) s := by
    intro s hs
    have hexp := (((hasDerivAt_id s).pow 2).const_mul k).exp
    have hprod := hexp.mul (hE_deriv s hs)
    convert hprod using 1
    rw [(hE_deriv s hs).deriv]
    dsimp [k]
    field_simp [ne_of_gt hα1]
  have hW_antitone : AntitoneOn W (Set.Ici s₀) := by
    apply antitoneOn_of_deriv_nonpos (D := Set.Ici s₀) (convex_Ici s₀) hW_cont.continuousOn
    · intro s hs
      exact (hW_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hW_deriv s (interior_subset hs)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith [hE_diff_ineq s (interior_subset hs)])
  have hk : 0 < k := div_pos hm hα1
  let μ : ℝ := k / 2
  have hμ : 0 < μ := div_pos hk (by norm_num)
  let d₀ : ℝ := Metric.infDist (g s₀) (frictionBall r)
  let C : ℝ := (d₀ + 1) * Real.exp (μ * s₀ ^ 2)
  have hC : 0 < C := mul_pos
    (add_pos_of_nonneg_of_pos Metric.infDist_nonneg zero_lt_one) (Real.exp_pos _)
  refine ⟨C, μ, hC, hμ, ?_⟩
  intro s hs
  have hmono := hW_antitone (Set.mem_Ici.mpr le_rfl) hs hs
  have henergy : E s ≤ E s₀ * Real.exp (-k * (s ^ 2 - s₀ ^ 2)) := by
    have hdiv : E s ≤ (Real.exp (k * s₀ ^ 2) * E s₀) / Real.exp (k * s ^ 2) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [W, mul_comm] using hmono)
    calc
      E s ≤ (Real.exp (k * s₀ ^ 2) * E s₀) / Real.exp (k * s ^ 2) := hdiv
      _ = E s₀ * Real.exp (-k * (s ^ 2 - s₀ ^ 2)) := by
        rw [show (Real.exp (k * s₀ ^ 2) * E s₀) / Real.exp (k * s ^ 2) =
          E s₀ * (Real.exp (k * s₀ ^ 2) / Real.exp (k * s ^ 2)) by ring,
          ← Real.exp_sub]
        congr 2
        ring
  have hsq : Metric.infDist (g s) (frictionBall r) ^ 2 ≤
      d₀ ^ 2 * Real.exp (-k * (s ^ 2 - s₀ ^ 2)) := by
    rw [show Metric.infDist (g s) (frictionBall r) = max (‖g s‖ - r) 0 from
      infDist_frictionBall_eq r hr (g s)]
    rw [show d₀ = max (‖g s₀‖ - r) 0 by
      simp [d₀, infDist_frictionBall_eq r hr]]
    dsimp [E] at henergy
    nlinarith
  have hexp_sq : (d₀ * Real.exp (-μ * (s ^ 2 - s₀ ^ 2))) ^ 2 =
      d₀ ^ 2 * Real.exp (-k * (s ^ 2 - s₀ ^ 2)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp [μ]
    ring
  have hdist : Metric.infDist (g s) (frictionBall r) ≤
      d₀ * Real.exp (-μ * (s ^ 2 - s₀ ^ 2)) :=
    (sq_le_sq₀ Metric.infDist_nonneg
      (mul_nonneg Metric.infDist_nonneg (Real.exp_pos _).le)).mp (by rwa [hexp_sq])
  rw [hgradient]
  change Metric.infDist (g s) (frictionBall r) ≤ C * Real.exp (-μ * s ^ 2)
  calc
    Metric.infDist (g s) (frictionBall r) ≤
        d₀ * Real.exp (-μ * (s ^ 2 - s₀ ^ 2)) := hdist
    _ ≤ (d₀ + 1) * Real.exp (-μ * (s ^ 2 - s₀ ^ 2)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = C * Real.exp (-μ * s ^ 2) := by
      dsimp [C]
      rw [show Real.exp (-μ * (s ^ 2 - s₀ ^ 2)) =
        Real.exp (μ * s₀ ^ 2) * Real.exp (-μ * s ^ 2) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring

end AttouchAdlyDryFrictionDynamics2023
