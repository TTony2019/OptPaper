import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_3
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_thm_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_5
set_option maxHeartbeats 2000000
namespace Alvarez2002
open Filter

/-- The energy expression used below deliberately has no positivity side
condition on `ell`: one endpoint energy can have zero potential coefficient. -/
noncomputable def dinForwardEnergy {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β ell : ℝ)
    (x : ℝ → H) (t : ℝ) : ℝ :=
  ell * Φ (x t) + (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2

private noncomputable def gdinEnergy {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (Φ : H → ℝ) (a b ell : ℝ)
    (x y : H) : ℝ :=
  ell * Φ x + (1 / 2) * ‖a • x + b • y‖ ^ 2

/-- A `C¹` map with a Hessian bounded on each ball is Lipschitz on each ball.
This is the local estimate needed by the forward g-DIN theorem. -/
private theorem grad_lipschitz_on_ball_of_hessian {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (gradΦ : H → H) (hessΦ : H → H →L[ℝ] H)
    (hHessDeriv : ∀ x, HasFDerivAt gradΦ (hessΦ x) x)
    (hHessLip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ x y,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖hessΦ x - hessΦ y‖ ≤ L * ‖x - y‖) :
    ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖gradΦ x - gradΦ y‖ ≤ L * ‖x - y‖ := by
  intro R
  let R' : ℝ := max R 1 + 1
  have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 1]
  obtain ⟨K, hKpos, hK⟩ := hHessLip R' hR'
  let M : ℝ := K * R' + ‖hessΦ 0‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (mul_nonneg (le_of_lt hKpos) (le_of_lt hR')) (norm_nonneg _)
  refine ⟨M, ?_⟩
  intro x y hx hy
  have hx' : ‖x‖ ≤ R' := le_trans hx (by dsimp [R']; linarith [le_max_left R 1])
  have hy' : ‖y‖ ≤ R' := le_trans hy (by dsimp [R']; linarith [le_max_left R 1])
  have hbound : ∀ z ∈ Metric.closedBall (0 : H) R', ‖hessΦ z‖ ≤ M := by
    intro z hz
    have hz' : ‖z‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzero : ‖(0 : H)‖ ≤ R' := by simpa using le_of_lt hR'
    have hd := hK z 0 hz' hzero
    calc
      ‖hessΦ z‖ = ‖hessΦ z - hessΦ 0 + hessΦ 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖hessΦ z - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
      _ ≤ K * ‖z - 0‖ + ‖hessΦ 0‖ := by gcongr
      _ ≤ K * R' + ‖hessΦ 0‖ := by
        gcongr
        simpa using hz'
      _ = M := rfl
  have hderiv : ∀ z ∈ Metric.closedBall (0 : H) R', DifferentiableAt ℝ gradΦ z :=
    fun z _ => (hHessDeriv z).differentiableAt
  have hfd : ∀ z ∈ Metric.closedBall (0 : H) R',
      ‖fderiv ℝ gradΦ z‖ ≤ M := by
    intro z hz
    simpa [(hHessDeriv z).fderiv] using hbound z hz
  have hconv : Convex ℝ (Metric.closedBall (0 : H) R') := convex_closedBall _ _
  have hxball : x ∈ Metric.closedBall (0 : H) R' := by simpa [Metric.mem_closedBall, dist_zero_right] using hx'
  have hyball : y ∈ Metric.closedBall (0 : H) R' := by simpa [Metric.mem_closedBall, dist_zero_right] using hy'
  simpa [dist_eq_norm] using
    hconv.norm_image_sub_le_of_norm_fderiv_le hderiv hfd hyball hxball

private theorem din_endpoint_lower_coeff (α β a b : ℝ) (hα : 0 < α)
    (hβ : 0 < β) (hab : a + b = α) (hb : b = 1 / β) :
    β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 =
      (1 - Real.sqrt (α * β)) ^ 2 := by
  have hsβ : (Real.sqrt β) ^ 2 = β := Real.sq_sqrt hβ.le
  have hsβne : Real.sqrt β ≠ 0 := Real.sqrt_ne_zero'.mpr hβ
  rw [hab, hb, show 1 / β = β⁻¹ by ring, Real.sqrt_inv,
    Real.sqrt_mul hα.le]
  field_simp
  nlinarith

private theorem din_endpoint_upper_coeff (α β a b : ℝ) (hα : 0 < α)
    (hβ : 0 < β) (hab : a + b = α) (hb : b = 1 / β) :
    β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 =
      (1 + Real.sqrt (α * β)) ^ 2 := by
  have hsβ : (Real.sqrt β) ^ 2 = β := Real.sq_sqrt hβ.le
  have hsβne : Real.sqrt β ≠ 0 := Real.sqrt_ne_zero'.mpr hβ
  rw [hab, hb, show 1 / β = β⁻¹ by ring, Real.sqrt_inv,
    Real.sqrt_mul hα.le]
  field_simp
  nlinarith

private theorem bounded_clm_apply_tendsto_zero {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (q : ℝ → H →L[ℝ] H) (v : ℝ → H) (C : ℝ)
    (hC : ∀ᶠ t in atTop, ‖q t‖ ≤ C) (hv : Tendsto v atTop (nhds 0)) :
    Tendsto (fun t => q t (v t)) atTop (nhds 0) := by
  have hnorm : ∀ᶠ t in atTop, ‖q t (v t)‖ ≤ C * ‖v t‖ := by
    filter_upwards [hC] with t ht
    calc
      ‖q t (v t)‖ ≤ ‖q t‖ * ‖v t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖v t‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  apply squeeze_zero_norm' hnorm
  simpa using (tendsto_const_nhds.mul hv.norm :
    Tendsto (fun t : ℝ => C * ‖v t‖) atTop (nhds (C * ‖(0 : H)‖)))

private theorem contDiffOn_two_of_hasDerivAt_of_contDiffOn_one {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f f' : ℝ → H}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContDiffOn ℝ 1 f' s) :
    ContDiffOn ℝ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact hf'.congr (fun t ht => heq t ht)

private theorem din_hasDerivWithinAt_Ici_of_continuous_deriv
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f g : ℝ → H} {a : ℝ}
    (hcontf : ContinuousOn f (Set.Ici a))
    (hdiff : DifferentiableOn ℝ f (Set.Ioi a))
    (heq : ∀ t, t ∈ Set.Ioi a → deriv f t = g t)
    (hgcont : ContinuousOn g (Set.Ici a)) :
    HasDerivWithinAt f (g a) (Set.Ici a) a := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
    ((hcontf.continuousWithinAt (by simp)).mono Set.Ioi_subset_Ici_self)
    self_mem_nhdsWithin
  have hgt : Tendsto g (nhdsWithin a (Set.Ioi a)) (nhds (g a)) :=
    (hgcont.continuousWithinAt (by simp)).tendsto.mono_left
      (nhdsWithin_mono a Set.Ioi_subset_Ici_self)
  exact hgt.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht).symm)

private theorem din_piecewise_quadratic_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} {d e : H} {a : ℝ}
    (hr : HasDerivWithinAt f d (Set.Ici a) a) :
    HasDerivAt
      (fun t => if a ≤ t then f t
        else f a + (t - a) • d + ((1 / 2 : ℝ) * (t - a) ^ 2) • e)
      d a := by
  have hlin : HasDerivAt (fun t : ℝ => (t - a) • d) d a := by
    simpa using ((hasDerivAt_id a).sub_const a).smul_const d
  have hquad : HasDerivAt
      (fun t : ℝ => ((1 / 2 : ℝ) * (t - a) ^ 2) • e)
      0 a := by
    have hs : HasDerivAt (fun t : ℝ => (t - a) ^ 2) 0 a := by
      convert (((hasDerivAt_id a).sub_const a).pow 2) using 1; simp
    convert (hs.const_mul (1 / 2 : ℝ)).smul_const e using 1; simp
  have hleft : HasDerivAt
      (fun t : ℝ => f a + (t - a) • d +
        ((1 / 2 : ℝ) * (t - a) ^ 2) • e) d a := by
    have h := (hasDerivAt_const a (f a)).add hlin |>.add hquad
    convert h using 1; simp
  have hleft' : HasDerivWithinAt
      (fun t => if a ≤ t then f t
        else f a + (t - a) • d + ((1 / 2 : ℝ) * (t - a) ^ 2) • e)
      d (Set.Iic a) a := by
    apply hleft.hasDerivWithinAt.congr
    · intro t ht
      by_cases hta : t = a
      · simp [hta]
      · have hlt : t < a := lt_of_le_of_ne ht hta
        simp [not_le_of_gt hlt]
    · simp
  have hright' : HasDerivWithinAt
      (fun t => if a ≤ t then f t
        else f a + (t - a) • d + ((1 / 2 : ℝ) * (t - a) ^ 2) • e)
      d (Set.Ici a) a := by
    apply hr.congr
    · intro t ht
      have hta : a ≤ t := ht
      simp [hta]
    · simp
  have hu := hleft'.union hright'
  rw [← hasDerivWithinAt_univ]
  convert hu using 1
  ext t
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ]
  constructor
  · intro _
    exact le_total t a
  · intro _
    trivial

private theorem din_piecewise_quadratic_hasDerivAt_of_lt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : ℝ → H} {d e : H} {a t : ℝ} (ht : t < a) :
    HasDerivAt
      (fun s => if a ≤ s then f s
        else f a + (s - a) • d + ((1 / 2 : ℝ) * (s - a) ^ 2) • e)
      (d + (t - a) • e) t := by
  have hpoly := (by
    have hlin : HasDerivAt (fun s : ℝ => (s - a) • d) d t := by
      simpa using ((hasDerivAt_id t).sub_const a).smul_const d
    have hs : HasDerivAt (fun s : ℝ => (s - a) ^ 2)
        (2 * (t - a)) t := by
      convert (((hasDerivAt_id t).sub_const a).pow 2) using 1; simp
    have hquad : HasDerivAt
        (fun s : ℝ => ((1 / 2 : ℝ) * (s - a) ^ 2) • e)
        ((t - a) • e) t := by
      convert (hs.const_mul (1 / 2 : ℝ)).smul_const e using 1; simp
    have h := (hasDerivAt_const t (f a)).add hlin |>.add hquad
    convert h using 1; simp :
    HasDerivAt
      (fun s : ℝ => f a + (s - a) • d +
        ((1 / 2 : ℝ) * (s - a) ^ 2) • e)
      (d + (t - a) • e) t)
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  have hs' : s < a := hs
  simp [not_le_of_gt hs']

private theorem din_piecewise_quadratic_hasDerivAt_of_gt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f g : ℝ → H} {d e : H} {a t : ℝ}
    (ht : a < t) (hf : HasDerivAt f (g t) t) :
    HasDerivAt
      (fun s => if a ≤ s then f s
        else f a + (s - a) • d + ((1 / 2 : ℝ) * (s - a) ^ 2) • e)
      (g t) t := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [eventually_ge_nhds ht] with s hs
  simp [hs]

/-- Shared forward construction used by the three paper-facing DIN statements. -/
theorem din_forward_internal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ)
    (hΦ : AssumptionH H Φ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (x₀ v₀ : H) :
    ∃ x v acc : ℝ → H, x 0 = x₀ ∧ v 0 = v₀ ∧
      IsDINTrajectory H Φ α β x ∧
      (∀ x', x' 0 = x₀ → deriv x' 0 = v₀ →
        IsDINTrajectory H Φ α β x' →
        ContDiff ℝ 2 x' →
        ∀ t, 0 ≤ t → x' t = x t ∧ deriv x' t = v t) ∧
      (∀ ell : ℝ, (1 - Real.sqrt (α * β)) ^ 2 ≤ ell →
        ell ≤ (1 + Real.sqrt (α * β)) ^ 2 → ∃ l : ℝ,
          AntitoneOn (dinForwardEnergy Φ β ell x) (Set.Ici 0) ∧
          (∃ m : ℝ, ∀ t, 0 ≤ t → m ≤ dinForwardEnergy Φ β ell x t) ∧
          Tendsto (dinForwardEnergy Φ β ell x) atTop (nhds l)) ∧
      MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.MemLp (fun t => gradient Φ (x t)) 2
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      (∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l)) ∧
      Tendsto (fun t => v t + β • gradient Φ (x t)) atTop (nhds 0) ∧
      (Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) → Bornology.IsBounded (v '' Set.Ici (0 : ℝ)) ∧
        Bornology.IsBounded (acc '' Set.Ici (0 : ℝ)) ∧
        Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) ∧
        Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) ∧
        Tendsto v atTop (nhds 0) ∧ Tendsto acc atTop (nhds 0) ∧
        Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0)) ∧
      (∀ t, 0 ≤ t → deriv x t = v t) := by
  let gradΦ : H → H := gradient Φ
  let hessΦ : H → H →L[ℝ] H := fderiv ℝ (gradient Φ)
  have hΦC1 : ContDiff ℝ 1 Φ :=
    hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hgradF : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradΦ z)) z := by
    intro z
    simpa [innerSL, gradΦ] using
      ((hΦC1.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
    exact (contDiff_succ_iff_fderiv.mp
      (show ContDiff ℝ (1 + 1) Φ by
        simpa using hΦ.twice_continuously_differentiable)).2.2
  have hgradC1 : ContDiff ℝ 1 gradΦ := by
    simpa [gradΦ, gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradDiff : Differentiable ℝ gradΦ :=
    hgradC1.differentiable (by norm_num)
  have hgradDeriv : ∀ x, HasFDerivAt gradΦ (hessΦ x) x := by
    intro x
    simpa [hessΦ] using (hgradDiff x).hasFDerivAt
  have hhessLip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ p q,
      ‖p‖ ≤ R → ‖q‖ ≤ R → ‖hessΦ p - hessΦ q‖ ≤ L * ‖p - q‖ := by
    intro R hR
    simpa [hessΦ] using hΦ.hessian_lipschitz_on_bounded R hR
  have hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ p q, ‖p‖ ≤ R → ‖q‖ ≤ R →
      ‖gradΦ p - gradΦ q‖ ≤ L * ‖p - q‖ :=
    grad_lipschitz_on_ball_of_hessian gradΦ hessΦ hgradDeriv
      hhessLip
  let a : ℝ := α - 1 / β
  let b : ℝ := 1 / β
  have hb : 0 < b := by
    dsimp [b]
    exact one_div_pos.mpr hβ
  have hab_eq : a + b = α := by
    dsimp [a, b]
    field_simp [ne_of_gt hβ]
    ring
  have hab : 0 < b + a := by linarith [hab_eq, hα]
  have hab' : 0 < a + b := by simpa [add_comm] using hab
  have hbβ_eq : b * β = 1 := by
    dsimp [b]
    field_simp [ne_of_gt hβ]
  let y₀g : H := - (1 / b) • (v₀ + β • gradΦ x₀ + a • x₀)
  have hloclip_aabr :
      AlvarezAttouchBolteRedont.LipschitzOnBoundedSets gradΦ := by
    intro s hs
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨R, hR⟩
    let R' : ℝ := max R 0
    rcases hloclip R' with ⟨L, hL⟩
    let K : NNReal := ⟨max L 0, le_max_right L 0⟩
    refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro x hx y hy
    have hxR : ‖x‖ ≤ R' := (hR x hx).trans (le_max_left _ _)
    have hyR : ‖y‖ ≤ R' := (hR y hy).trans (le_max_left _ _)
    have hxy := hL x y hxR hyR
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hmain :=
    AlvarezAttouchBolteRedont.alvarez_attouch_bolte_redont_theorem_1_1
      Φ gradΦ β a b hΦC1 hgradF hΦ.bounded_below hloclip_aabr hβ hb hab'
  obtain ⟨sys, hsys, hsysuniq⟩ := hmain.1 x₀ y₀g
  have hlyap := hmain.2.1 x₀ y₀g sys hsys
  have henergy : ∀ ell : ℝ, (1 - Real.sqrt (α * β)) ^ 2 ≤ ell →
      ell ≤ (1 + Real.sqrt (α * β)) ^ 2 → ∃ l : ℝ,
        AntitoneOn (fun t => gdinEnergy Φ a b ell (sys.x t) (sys.y t)) (Set.Ici 0) ∧
        (∃ m : ℝ, ∀ t, 0 ≤ t → m ≤ gdinEnergy Φ a b ell (sys.x t) (sys.y t)) ∧
        Tendsto (fun t => gdinEnergy Φ a b ell (sys.x t) (sys.y t)) atTop (nhds l) := by
    intro ell hlow hhigh
    have hlow' : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell := by
      rw [din_endpoint_lower_coeff α β a b hα hβ hab_eq (by rfl)]
      exact hlow
    have hhigh' : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
      rw [din_endpoint_upper_coeff α β a b hα hβ hab_eq (by rfl)]
      exact hhigh
    obtain ⟨hanti, hlower, ⟨l, hlim⟩, -, -, -, -⟩ := hlyap ell hlow' hhigh'
    refine ⟨l, ?_, ?_, ?_⟩
    · simpa [gdinEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy] using hanti
    · simpa [gdinEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy] using hlower
    · simpa [gdinEnergy, AlvarezAttouchBolteRedont.LyapunovEnergy] using hlim
  have hmid_low : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ β * (a + 2 * b) := by
    have hs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab'.le
    have ht_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hprod : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hmid_high : β * (a + 2 * b) ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
    have hs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab'.le
    have ht_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hprod : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hlyap_mid := hlyap (β * (a + 2 * b)) hmid_low hmid_high
  have hvL2 : MeasureTheory.MemLp sys.xdot 2
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := by
    simpa [AlvarezAttouchBolteRedont.MemL2OnNonnegative] using hlyap_mid.2.2.2.1
  have hgradL2 : MeasureTheory.MemLp (fun t => gradΦ (sys.x t)) 2
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := by
    have hydotL2 : MeasureTheory.MemLp sys.ydot 2
        (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := by
      simpa [AlvarezAttouchBolteRedont.MemL2OnNonnegative] using
        hlyap_mid.2.2.2.2.2.1
    have hdiffL2 := hydotL2.sub hvL2
    have hscaledL2 := hdiffL2.const_smul (1 / β : ℝ)
    apply hscaledL2.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have hx := sys.equation_x t ht
    have hy := sys.equation_y t ht
    have hrel : sys.ydot t = sys.xdot t + β • gradΦ (sys.x t) := by
      calc
        sys.ydot t =
            (sys.ydot t + a • sys.x t + b • sys.y t) -
              (sys.xdot t + β • gradΦ (sys.x t) + a • sys.x t + b • sys.y t) +
                sys.xdot t + β • gradΦ (sys.x t) := by module
        _ = sys.xdot t + β • gradΦ (sys.x t) := by rw [hx, hy]; module
    change (1 / β) • (sys.ydot t - sys.xdot t) = gradΦ (sys.x t)
    rw [hrel, smul_sub, smul_add, smul_smul]
    field_simp [ne_of_gt hβ]
    module
  have hΦlim : ∃ l : ℝ, Tendsto (fun t => Φ (sys.x t)) atTop (nhds l) :=
    hlyap_mid.2.2.2.2.1
  have hshiftlim : Tendsto (fun t => sys.xdot t + β • gradΦ (sys.x t)) atTop (nhds 0) := by
    have hydotlim : Tendsto sys.ydot atTop (nhds 0) := hlyap_mid.2.2.2.2.2.2
    apply hydotlim.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    have hx := sys.equation_x t ht
    have hy := sys.equation_y t ht
    calc
      sys.ydot t =
          (sys.ydot t + a • sys.x t + b • sys.y t) -
            (sys.xdot t + β • gradΦ (sys.x t) + a • sys.x t + b • sys.y t) +
              sys.xdot t + β • gradΦ (sys.x t) := by module
      _ = sys.xdot t + β • gradΦ (sys.x t) := by rw [hx, hy]; module
  have hbounded :
      BoundedOnNonnegative sys.x →
        BoundedOnNonnegative sys.xdot ∧
        BoundedOnNonnegative (fun t => gradΦ (sys.x t)) ∧
        Tendsto sys.xdot atTop (nhds 0) ∧
        Tendsto (fun t => gradΦ (sys.x t)) atTop (nhds 0) := by
    intro hxbound
    rcases hmain.2.2 x₀ y₀g sys hsys hxbound with
      ⟨hgradbound, hvbound, hvlim, hgradlim⟩
    exact ⟨hvbound, hgradbound, hvlim, hgradlim⟩
  have hxdot_deriv : ∀ t, 0 < t → HasDerivAt sys.xdot
      (- α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)) t := by
    intro t ht
    have hxderiv := hsys.1.1 t ht
    have hyderiv := hsys.1.2 t ht
    have hgderiv : HasDerivAt (fun s => gradΦ (sys.x s))
        (hessΦ (sys.x t) (sys.xdot t)) t := by
      simpa [Function.comp_def] using
        (hgradDeriv (sys.x t)).comp_hasDerivAt t hxderiv
    have hrhs : HasDerivAt (fun s =>
        -β • gradΦ (sys.x s) - a • sys.x s - b • sys.y s)
        (-β • hessΦ (sys.x t) (sys.xdot t) - a • sys.xdot t - b • sys.ydot t) t := by
      simpa [sub_eq_add_neg] using
        ((hgderiv.const_smul (-β)).sub (hxderiv.const_smul a)).sub
          (hyderiv.const_smul b)
    have hevent : sys.xdot =ᶠ[nhds t] fun s =>
        -β • gradΦ (sys.x s) - a • sys.x s - b • sys.y s := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      have hx := sys.equation_x s hs.le
      calc
        sys.xdot s =
            (sys.xdot s + β • gradΦ (sys.x s) + a • sys.x s + b • sys.y s) -
              β • gradΦ (sys.x s) - a • sys.x s - b • sys.y s := by module
        _ = -β • gradΦ (sys.x s) - a • sys.x s - b • sys.y s := by
          rw [hx]
          module
    have hraw := hrhs.congr_of_eventuallyEq hevent
    have hrel : sys.ydot t = sys.xdot t + β • gradΦ (sys.x t) := by
      have hx := sys.equation_x t ht.le
      have hy := sys.equation_y t ht.le
      calc
        sys.ydot t =
            (sys.ydot t + a • sys.x t + b • sys.y t) -
              (sys.xdot t + β • gradΦ (sys.x t) + a • sys.x t + b • sys.y t) +
                sys.xdot t + β • gradΦ (sys.x t) := by module
        _ = sys.xdot t + β • gradΦ (sys.x t) := by rw [hx, hy]; module
    convert hraw using 1
    rw [hrel, ← hab_eq]
    simp only [smul_add, smul_smul]
    rw [hbβ_eq]
    module
  let acc : ℝ → H := fun t =>
    - α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)
  have hvcont : ContinuousOn sys.xdot (Set.Ici 0) := by
    have hgradx : ContinuousOn (fun t => gradΦ (sys.x t)) (Set.Ici 0) :=
      hgradC1.continuous.comp_continuousOn hsys.2.2.1
    have hform : ContinuousOn (fun t =>
        -β • gradΦ (sys.x t) - a • sys.x t - b • sys.y t) (Set.Ici 0) :=
      ((hgradx.const_smul (-β)).sub (hsys.2.2.1.const_smul a)).sub
        (hsys.2.2.2.const_smul b)
    refine hform.congr ?_
    intro t ht
    have hx := sys.equation_x t ht
    calc
      sys.xdot t =
          (sys.xdot t + β • gradΦ (sys.x t) + a • sys.x t + b • sys.y t) -
            β • gradΦ (sys.x t) - a • sys.x t - b • sys.y t := by module
      _ = -β • gradΦ (sys.x t) - a • sys.x t - b • sys.y t := by
        rw [hx]
        module
  have hhessCont : Continuous hessΦ := by
    have hlocal : LocallyLipschitz hessΦ := by
      intro z
      let R : ℝ := ‖z‖ + 1
      have hR : 0 < R := by
        dsimp [R]
        linarith [norm_nonneg z]
      obtain ⟨L, hLpos, hL⟩ := hhessLip R hR
      let K : NNReal := ⟨L, hLpos.le⟩
      refine ⟨K, Metric.closedBall z 1, Metric.closedBall_mem_nhds z zero_lt_one,
        LipschitzOnWith.of_dist_le_mul ?_⟩
      intro p hp q hq
      have hpR : ‖p‖ ≤ R := by
        calc
          ‖p‖ ≤ ‖p - z‖ + ‖z‖ := by
            calc
              ‖p‖ = ‖(p - z) + z‖ := by congr 1; module
              _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 1 + ‖z‖ := by
            gcongr
            simpa [Metric.mem_closedBall, dist_eq_norm] using hp
          _ = R := by dsimp [R]; ring
      have hqR : ‖q‖ ≤ R := by
        calc
          ‖q‖ ≤ ‖q - z‖ + ‖z‖ := by
            calc
              ‖q‖ = ‖(q - z) + z‖ := by congr 1; module
              _ ≤ ‖q - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 1 + ‖z‖ := by
            gcongr
            simpa [Metric.mem_closedBall, dist_eq_norm] using hq
          _ = R := by dsimp [R]; ring
      simpa [K, dist_eq_norm] using hL p q hpR hqR
    exact hlocal.continuous
  have hacccont : ContinuousOn acc (Set.Ici 0) := by
    have hgradx : ContinuousOn (fun t => gradΦ (sys.x t)) (Set.Ici 0) :=
      hgradC1.continuous.comp_continuousOn hsys.2.2.1
    have hhessx : ContinuousOn (fun t => hessΦ (sys.x t)) (Set.Ici 0) :=
      by simpa [Function.comp_def] using hhessCont.comp_continuousOn hsys.2.2.1
    have happly : ContinuousOn
        (fun t => hessΦ (sys.x t) (sys.xdot t)) (Set.Ici 0) :=
      hhessx.clm_apply hvcont
    dsimp [acc]
    exact ((hvcont.const_smul (-α)).sub
      ((happly.const_smul β))).sub hgradx
  have hxright : HasDerivWithinAt sys.x (sys.xdot 0) (Set.Ici 0) 0 :=
    din_hasDerivWithinAt_Ici_of_continuous_deriv hsys.2.2.1
      (fun t ht => (hsys.1.1 t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hsys.1.1 t ht).deriv) hvcont
  have hxdotright : HasDerivWithinAt sys.xdot (acc 0) (Set.Ici 0) 0 :=
    din_hasDerivWithinAt_Ici_of_continuous_deriv hvcont
      (fun t ht => (hxdot_deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => by simpa [acc] using (hxdot_deriv t ht).deriv) hacccont
  have hv0 : sys.xdot 0 = v₀ := by
    have hx := sys.equation_x 0 le_rfl
    rw [sys.initial_x, sys.initial_y] at hx
    dsimp [y₀g] at hx
    have hbne : b ≠ 0 := ne_of_gt hb
    have hbinv : b * (1 / b) = 1 := by field_simp [hbne]
    have hnegbinv : b * -(1 / b) = -1 := by
      calc
        b * -(1 / b) = -(b * (1 / b)) := by ring
        _ = -1 := by rw [hbinv]
    calc
      sys.xdot 0 =
          (sys.xdot 0 + β • gradΦ x₀ + a • x₀ +
            b • (-(1 / b) • (v₀ + β • gradΦ x₀ + a • x₀))) -
              β • gradΦ x₀ - a • x₀ -
                b • (-(1 / b) • (v₀ + β • gradΦ x₀ + a • x₀)) := by module
      _ = -β • gradΦ x₀ - a • x₀ -
            b • (-(1 / b) • (v₀ + β • gradΦ x₀ + a • x₀)) := by
          rw [hx]
          module
      _ = v₀ := by
        rw [smul_smul, hnegbinv]
        module
  let xext : ℝ → H := fun t =>
    if 0 ≤ t then sys.x t
    else sys.x 0 + t • sys.xdot 0 + ((1 / 2 : ℝ) * t ^ 2) • acc 0
  let vext : ℝ → H := fun t =>
    if 0 ≤ t then sys.xdot t else sys.xdot 0 + t • acc 0
  let accExt : ℝ → H := fun t => if 0 ≤ t then acc t else acc 0
  have hxext_eq : ∀ t, 0 ≤ t → xext t = sys.x t := by
    intro t ht
    simp [xext, ht]
  have hvext_eq : ∀ t, 0 ≤ t → vext t = sys.xdot t := by
    intro t ht
    simp [vext, ht]
  have haccExt_eq : ∀ t, 0 ≤ t → accExt t = acc t := by
    intro t ht
    simp [accExt, ht]
  have hderiv_xext : ∀ t, HasDerivAt xext (vext t) t := by
    intro t
    by_cases ht0 : t = 0
    · subst t
      simpa [xext, vext] using
        (din_piecewise_quadratic_hasDerivAt (f := sys.x) (d := sys.xdot 0)
          (e := acc 0) (a := 0) hxright)
    · by_cases htpos : 0 < t
      · have ht_nonneg : 0 ≤ t := le_of_lt htpos
        have h := din_piecewise_quadratic_hasDerivAt_of_gt (f := sys.x) (g := sys.xdot)
          (d := sys.xdot 0) (e := acc 0) (a := 0) (t := t) htpos
          (hsys.1.1 t htpos)
        convert h using 1 <;> simp [xext, vext, ht_nonneg]
      · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht0
        have h := din_piecewise_quadratic_hasDerivAt_of_lt (f := sys.x) (d := sys.xdot 0)
          (e := acc 0) (a := 0) (t := t) htneg
        convert h using 1 <;> simp [xext, vext, not_le.mpr htneg]
  have hderiv_vext : ∀ t, HasDerivAt vext (accExt t) t := by
    intro t
    by_cases ht0 : t = 0
    · subst t
      simpa [vext, accExt] using
        (din_piecewise_quadratic_hasDerivAt (f := sys.xdot) (d := acc 0)
          (e := (0 : H)) (a := 0) hxdotright)
    · by_cases htpos : 0 < t
      · have ht_nonneg : 0 ≤ t := le_of_lt htpos
        have h := din_piecewise_quadratic_hasDerivAt_of_gt (f := sys.xdot)
          (g := acc) (d := acc 0) (e := (0 : H)) (a := 0) (t := t) htpos
          (hxdot_deriv t htpos)
        convert h using 1 <;> simp [vext, accExt, acc, ht_nonneg]
      · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht0
        have h := din_piecewise_quadratic_hasDerivAt_of_lt (f := sys.xdot)
          (d := acc 0) (e := (0 : H)) (a := 0) (t := t) htneg
        convert h using 1 <;> simp [vext, accExt, not_le.mpr htneg]
  have hderiv_xext_eq : deriv xext = vext := by
    funext t
    exact (hderiv_xext t).deriv
  have hderiv_vext_eq : deriv vext = accExt := by
    funext t
    exact (hderiv_vext t).deriv
  have hxext0 : xext 0 = x₀ := by simp [xext, sys.initial_x]
  have hvext0 : vext 0 = v₀ := by simp [vext, hv0]
  have hforward_ext : IsDINTrajectory H Φ α β xext := by
    refine ⟨hα, hβ, ?_⟩
    intro t ht
    rw [hderiv_xext_eq, hderiv_vext_eq]
    have hacc := haccExt_eq t ht
    have hx := hxext_eq t ht
    have hv := hvext_eq t ht
    simp only [accExt, hacc, hx, hv, acc, gradΦ, hessΦ]
    module
  have hvL2ext : MeasureTheory.MemLp vext 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply (hvL2.mono_measure (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
      (Set.Ioi_subset_Ici le_rfl))).ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hvext_eq t ht.le).symm
  have hgradL2ext : MeasureTheory.MemLp (fun t => gradient Φ (xext t)) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply (hgradL2.mono_measure (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
      (Set.Ioi_subset_Ici le_rfl))).ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simp [hxext_eq t ht.le, gradΦ]
  have hΦlimext : ∃ l : ℝ, Tendsto (fun t => Φ (xext t)) atTop (nhds l) := by
    obtain ⟨l, hl⟩ := hΦlim
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [hxext_eq t ht]
  have hshiftlimext : Tendsto (fun t => vext t + β • gradient Φ (xext t))
      atTop (nhds 0) := by
    apply hshiftlim.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [hvext_eq t ht, hxext_eq t ht, gradΦ]
  refine ⟨xext, vext, accExt, hxext0, hvext0, ?_, ?_, ?_,
    hvL2ext, hgradL2ext, hΦlimext, hshiftlimext, ?_,
    fun t ht => (hderiv_xext t).deriv⟩
  · refine ⟨hα, hβ, ?_⟩
    exact hforward_ext.2.2
  /- · intro hxbound
    rcases hbounded hxbound with ⟨hvbound, hgradbound, hvlim, hgradlim⟩
    have hvbound' : Bornology.IsBounded (sys.xdot '' Set.Ici (0 : ℝ)) :=
      hvbound
    have hgradbound' : Bornology.IsBounded
        ((fun t => gradΦ (sys.x t)) '' Set.Ici (0 : ℝ)) := hgradbound
    rcases isBounded_iff_forall_norm_le.mp hxbound with ⟨R, hR⟩
    let R' : ℝ := max R 1 + 1
    have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 1]
    obtain ⟨L, hLpos, hL⟩ := hhessLip R' hR'
    let M : ℝ := L * R' + ‖hessΦ 0‖
    have hhessbound : Bornology.IsBounded
        ((fun t => hessΦ (sys.x t)) '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro q ⟨t, ht, rfl⟩
      have hxt : ‖sys.x t‖ ≤ R := hR _ ⟨t, ht, rfl⟩
      have hxt' : ‖sys.x t‖ ≤ R' := by
        dsimp [R']
        linarith [le_max_left R 1]
      have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
      have hd := hL (sys.x t) 0 hxt' hzero
      calc
        ‖hessΦ (sys.x t)‖ = ‖hessΦ (sys.x t) - hessΦ 0 + hessΦ 0‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖hessΦ (sys.x t) - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
        _ ≤ L * ‖sys.x t - 0‖ + ‖hessΦ 0‖ := by gcongr
        _ ≤ L * R' + ‖hessΦ 0‖ := by
          gcongr
          simpa using hxt'
        _ = M := rfl
    rcases isBounded_iff_forall_norm_le.mp hvbound' with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbound' with ⟨G, hG⟩
    rcases isBounded_iff_forall_norm_le.mp hhessbound with ⟨Q, hQ⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, by simp, rfl⟩)
    have haccbound : Bornology.IsBounded (acc '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨|α| * V + |β| * Q * V + G, ?_⟩
      rintro z ⟨t, ht, rfl⟩
      have hv : ‖sys.xdot t‖ ≤ V := hV _ ⟨t, ht, rfl⟩
      have hg : ‖gradΦ (sys.x t)‖ ≤ G := hG _ ⟨t, ht, rfl⟩
      have hq : ‖hessΦ (sys.x t)‖ ≤ Q := hQ _ ⟨t, ht, rfl⟩
      dsimp [acc]
      calc
        ‖-α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)‖ ≤
            ‖-α • sys.xdot t‖ + ‖β • hessΦ (sys.x t) (sys.xdot t)‖ +
              ‖gradΦ (sys.x t)‖ := by
              calc
                _ ≤ ‖-α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)‖ +
                    ‖gradΦ (sys.x t)‖ := norm_sub_le _ _
                _ ≤ ‖-α • sys.xdot t‖ + ‖β • hessΦ (sys.x t) (sys.xdot t)‖ +
                    ‖gradΦ (sys.x t)‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ |α| * V + |β| * Q * V + G := by
          rw [norm_smul, norm_neg, norm_smul]
          calc
            |α| * ‖sys.xdot t‖ + |β| * ‖hessΦ (sys.x t) (sys.xdot t)‖ +
                ‖gradΦ (sys.x t)‖ ≤
                |α| * V + |β| * (Q * V) + G := by
                  gcongr
                  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hq hv (norm_nonneg _) (norm_nonneg _))
            _ = |α| * V + |β| * Q * V + G := by ring
    have happlylim : Tendsto (fun t => hessΦ (sys.x t) (sys.xdot t)) atTop (nhds 0) := by
      apply bounded_clm_apply_tendsto_zero (fun t => hessΦ (sys.x t)) sys.xdot Q
      · filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => hQ _ ⟨t, ht, rfl⟩⟩] with t ht
        exact ht
      · exact hvlim
    have hacclim : Tendsto acc atTop (nhds 0) := by
      set_option maxHeartbeats 1000000 in
      change Tendsto (fun t => -α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)) atTop (nhds 0)
      have h1 : Tendsto (fun t => (-α) • sys.xdot t) atTop (nhds ((-α) • (0 : H))) :=
        hvlim.const_smul (-α)
      have h2 : Tendsto (fun t => β • hessΦ (sys.x t) (sys.xdot t))
          atTop (nhds (β • (0 : H))) :=
        happlylim.const_smul β
      have h3 : Tendsto
          (fun t => (-α) • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)) atTop
          (nhds ((-α) • (0 : H) - β • (0 : H))) := by
        set_option maxHeartbeats 1000000 in
        exact Filter.Tendsto.sub (G := H) (α := ℝ) h1 h2
      have h3' : Tendsto
          (fun t => (-α) • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)) atTop
          (nhds (0 : H)) := by simpa using h3
      have h4 := Filter.Tendsto.sub (G := H) (α := ℝ) h3' hgradlim
      simpa using h4
    exact ⟨hvbound', haccbound, hgradbound', hhessbound, hvlim, hacclim, hgradlim⟩ -/
  · intro x' hx0 hv0 htr hxreg
    have hxC2 : ContDiff ℝ (1 + 1) x' := by simpa using hxreg
    have hxdata := contDiff_succ_iff_deriv.mp hxC2
    have hxC1 : ContDiffOn ℝ 1 x' (Set.Ici 0) :=
      (hxreg.of_le (by norm_num)).contDiffOn
    have hvC1 : ContDiff ℝ 1 (deriv x') := by simpa using hxdata.2.2
    have hvdata := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (0 + 1) (deriv x') by simpa using hvC1)
    have hgradCompC1 : ContDiff ℝ 1 (fun t => gradΦ (x' t)) := by
      simpa [Function.comp_def] using hgradC1.comp (hxreg.of_le (by norm_num))
    let y' : ℝ → H := fun t =>
      -(1 / b) • (deriv x' t + β • gradΦ (x' t) + a • x' t)
    let ydot' : ℝ → H := fun t => deriv x' t + β • gradΦ (x' t)
    have hFderiv : ∀ t, 0 ≤ t → HasDerivAt y'
        (deriv x' t + β • gradΦ (x' t)) t := by
      intro t ht
      have hxAt : HasDerivAt x' (deriv x' t) t := (hxdata.1 t).hasDerivAt
      have hvAt : HasDerivAt (deriv x') (deriv (deriv x') t) t :=
        (hvdata.1 t).hasDerivAt
      have hgAt : HasDerivAt (fun s => gradΦ (x' s))
          ((hessΦ (x' t)) (deriv x' t)) t := by
        simpa [Function.comp_def] using
          (hgradDeriv (x' t)).comp_hasDerivAt t hxAt
      have hraw := (hvAt.add (hgAt.const_smul β)).add
        (hxAt.const_smul a)
      have hscaled := hraw.const_smul (-(1 / b))
      dsimp [y']
      convert hscaled using 1
      have heq := htr.2.2 t ht
      rw [show -(1 / b) = -β by dsimp [b]; field_simp [ne_of_gt hβ]]
      simp only [smul_add, smul_smul, neg_smul]
      rw [show deriv (deriv x') t =
          -(α • deriv x' t + β • (fderiv ℝ (gradient Φ) (x' t))
            (deriv x' t) + gradient Φ (x' t)) by
        exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using heq)]
      rw [← hab_eq]
      have hβb : β * b = 1 := by rw [mul_comm, hbβ_eq]
      simp [smul_add, smul_smul, mul_add, hβb]
      module
    have hyC2 : ContDiffOn ℝ 2 y' (Set.Ici 0) := by
      apply contDiffOn_two_of_hasDerivAt_of_contDiffOn_one (uniqueDiffOn_Ici 0)
      · intro t ht
        simpa [y', ydot', a, b] using hFderiv t ht
      · simpa [Function.comp_def] using
          (hvC1.add (hgradCompC1.const_smul β)).contDiffOn
    have hbne : b ≠ 0 := ne_of_gt hb
    have hbinv : b * (1 / b) = 1 := by field_simp [hbne]
    have hnegbinv : b * -(1 / b) = -1 := by rw [mul_neg, hbinv]
    let sys' : AlvarezAttouchBolteRedont.NonnegativeDissipativeSystem H gradΦ β a b x₀ y₀g :=
      { x := x'
        y := y'
        xdot := deriv x'
        ydot := ydot'
        beta_pos := hβ
        b_pos := hb
        a_add_b_pos := by linarith [hab_eq, hα]
        initial_x := hx0
        initial_y := by simp [y', y₀g, hx0, hv0]
        equation_x := by
          intro t ht
          dsimp [y']
          rw [smul_smul, hnegbinv]
          module
        equation_y := by
          intro t ht
          dsimp [ydot', y']
          rw [smul_smul, hnegbinv]
          module }
    have hsys' : AlvarezAttouchBolteRedont.IsSolutionOnNonnegative sys' := by
      have hdx : ∀ t, 0 ≤ t → HasDerivAt x' (deriv x' t) t :=
        fun t ht => (hxdata.1 t).hasDerivAt
      have hdy : ∀ t, 0 ≤ t → HasDerivAt y' (ydot' t) t := by
        intro t ht
        simpa [y', ydot', a, b] using hFderiv t ht
      refine ⟨⟨fun t ht => hdx t ht.le, fun t ht => hdy t ht.le⟩, ⟨hxC1, hyC2⟩,
        ⟨hxC1.continuousOn, hyC2.continuousOn⟩⟩
    have hsame := hsysuniq sys' hsys'
    intro t ht
    have h := hsame t ht
    exact ⟨h.1.trans (hxext_eq t ht).symm,
      h.2.2.1.trans (hvext_eq t ht).symm⟩
  · intro ell hlow hhigh
    have hlower_coeff : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 =
        (1 - Real.sqrt (α * β)) ^ 2 :=
      din_endpoint_lower_coeff α β a b hα hβ hab_eq (by rfl)
    have hupper_coeff : β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 =
        (1 + Real.sqrt (α * β)) ^ 2 :=
      din_endpoint_upper_coeff α β a b hα hβ hab_eq (by rfl)
    obtain ⟨l, hanti, hlower, hlim⟩ := henergy ell
      (by simpa [hlower_coeff] using hlow)
      (by simpa [hupper_coeff] using hhigh)
    have heq : ∀ t, 0 ≤ t →
        gdinEnergy Φ a b ell (sys.x t) (sys.y t) =
          dinForwardEnergy Φ β ell xext t := by
      intro t ht
      have hx := sys.equation_x t ht
      have hdx : deriv xext t = vext t := (hderiv_xext t).deriv
      have hq : a • sys.x t + b • sys.y t =
          -(sys.xdot t + β • gradΦ (sys.x t)) := by
        calc
          a • sys.x t + b • sys.y t =
              (sys.xdot t + β • gradΦ (sys.x t) + a • sys.x t + b • sys.y t) -
                (sys.xdot t + β • gradΦ (sys.x t)) := by module
          _ = -(sys.xdot t + β • gradΦ (sys.x t)) := by rw [hx]; module
      simp only [gdinEnergy, dinForwardEnergy, gradΦ, hq, norm_neg, hdx,
        hxext_eq t ht, hvext_eq t ht]
    refine ⟨l, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      rw [← heq s hs, ← heq t ht]
      exact hanti hs ht hst
    · obtain ⟨m, hm⟩ := hlower
      exact ⟨m, fun t ht => by rw [← heq t ht]; exact hm t ht⟩
    · apply hlim.congr'
      filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => heq t ht⟩] with t ht
      exact ht
  · intro hxbound
    have hxbound_sys : BoundedOnNonnegative sys.x := by
      unfold BoundedOnNonnegative
      apply hxbound.subset
      intro z hz
      rcases hz with ⟨t, ht, rfl⟩
      exact ⟨t, ht, hxext_eq t ht⟩
    rcases hbounded hxbound_sys with ⟨hvbound, hgradbound, hvlim, hgradlim⟩
    have hvbound' : Bornology.IsBounded (sys.xdot '' Set.Ici (0 : ℝ)) := hvbound
    have hgradbound' : Bornology.IsBounded ((fun t => gradΦ (sys.x t)) '' Set.Ici (0 : ℝ)) := hgradbound
    rcases isBounded_iff_forall_norm_le.mp hxbound_sys with ⟨R, hR⟩
    let R' : ℝ := max R 1 + 1
    have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 1]
    obtain ⟨L, hLpos, hL⟩ := hhessLip R' hR'
    let M : ℝ := L * R' + ‖hessΦ 0‖
    have hhessbound : Bornology.IsBounded ((fun t => hessΦ (sys.x t)) '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro q ⟨t, ht, rfl⟩
      have hxt : ‖sys.x t‖ ≤ R := hR _ ⟨t, ht, rfl⟩
      have hxt' : ‖sys.x t‖ ≤ R' := by dsimp [R']; linarith [le_max_left R 1]
      have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
      have hd := hL (sys.x t) 0 hxt' hzero
      calc
        ‖hessΦ (sys.x t)‖ = ‖hessΦ (sys.x t) - hessΦ 0 + hessΦ 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖hessΦ (sys.x t) - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
        _ ≤ L * ‖sys.x t - 0‖ + ‖hessΦ 0‖ := by gcongr
        _ ≤ L * R' + ‖hessΦ 0‖ := by gcongr; simpa using hxt'
        _ = M := rfl
    rcases isBounded_iff_forall_norm_le.mp hvbound' with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbound' with ⟨G, hG⟩
    rcases isBounded_iff_forall_norm_le.mp hhessbound with ⟨Q, hQ⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, by simp, rfl⟩)
    have haccbound : Bornology.IsBounded (acc '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨|α| * V + |β| * Q * V + G, ?_⟩
      rintro z ⟨t, ht, rfl⟩
      have hv : ‖sys.xdot t‖ ≤ V := hV _ ⟨t, ht, rfl⟩
      have hg : ‖gradΦ (sys.x t)‖ ≤ G := hG _ ⟨t, ht, rfl⟩
      have hq : ‖hessΦ (sys.x t)‖ ≤ Q := hQ _ ⟨t, ht, rfl⟩
      dsimp [acc]
      calc
        ‖-α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)‖ ≤
            ‖-α • sys.xdot t‖ + ‖β • hessΦ (sys.x t) (sys.xdot t)‖ + ‖gradΦ (sys.x t)‖ := by
              calc
                _ ≤ ‖-α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)‖ + ‖gradΦ (sys.x t)‖ := norm_sub_le _ _
                _ ≤ ‖-α • sys.xdot t‖ + ‖β • hessΦ (sys.x t) (sys.xdot t)‖ + ‖gradΦ (sys.x t)‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ |α| * V + |β| * Q * V + G := by
          rw [norm_smul, norm_neg, norm_smul]
          calc
            |α| * ‖sys.xdot t‖ + |β| * ‖hessΦ (sys.x t) (sys.xdot t)‖ + ‖gradΦ (sys.x t)‖ ≤ |α| * V + |β| * (Q * V) + G := by
              have hqv : ‖hessΦ (sys.x t) (sys.xdot t)‖ ≤ Q * V :=
                (ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul hq hv (norm_nonneg _) hQnonneg)
              have hαv : |α| * ‖sys.xdot t‖ ≤ |α| * V :=
                mul_le_mul_of_nonneg_left hv (abs_nonneg α)
              have hβqv : |β| * ‖hessΦ (sys.x t) (sys.xdot t)‖ ≤
                  |β| * (Q * V) :=
                mul_le_mul_of_nonneg_left hqv (abs_nonneg β)
              exact add_le_add (add_le_add hαv hβqv) (hG _ ⟨t, ht, rfl⟩)
            _ = |α| * V + |β| * Q * V + G := by ring
    have happlylim : Tendsto (fun t => hessΦ (sys.x t) (sys.xdot t)) atTop (nhds 0) := by
      apply bounded_clm_apply_tendsto_zero (fun t => hessΦ (sys.x t)) sys.xdot Q
      filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => hQ _ ⟨t, ht, rfl⟩⟩] with t ht
      exact ht
      exact hvlim
    have hacclim : Tendsto acc atTop (nhds 0) := by
      set_option maxHeartbeats 1000000 in
      change Tendsto (fun t => -α • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t) - gradΦ (sys.x t)) atTop (nhds 0)
      have h1 : Tendsto (fun t => (-α) • sys.xdot t) atTop (nhds ((-α) • (0 : H))) :=
        hvlim.const_smul (-α)
      have h2 : Tendsto (fun t => β • hessΦ (sys.x t) (sys.xdot t))
          atTop (nhds (β • (0 : H))) :=
        happlylim.const_smul β
      have h3 : Tendsto
          (fun t => (-α) • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)) atTop
          (nhds ((-α) • (0 : H) - β • (0 : H))) := by
        set_option maxHeartbeats 1000000 in
        exact Filter.Tendsto.sub (G := H) (α := ℝ) h1 h2
      have h3' : Tendsto
          (fun t => (-α) • sys.xdot t - β • hessΦ (sys.x t) (sys.xdot t)) atTop
          (nhds (0 : H)) := by simpa using h3
      have h4 := Filter.Tendsto.sub (G := H) (α := ℝ) h3' hgradlim
      simpa using h4
    have hvbound_ext : Bornology.IsBounded (vext '' Set.Ici (0 : ℝ)) := by
      apply hvbound'.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hvext_eq t ht).symm⟩
    have haccbound_ext : Bornology.IsBounded (accExt '' Set.Ici (0 : ℝ)) := by
      apply haccbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (haccExt_eq t ht).symm⟩
    have hgradbound_ext : Bornology.IsBounded
        ((fun t => gradient Φ (xext t)) '' Set.Ici (0 : ℝ)) := by
      apply hgradbound'.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [hxext_eq t ht, gradΦ]⟩
    have hhessbound_ext : Bornology.IsBounded
        ((fun t => fderiv ℝ (gradient Φ) (xext t)) '' Set.Ici (0 : ℝ)) := by
      apply hhessbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [hxext_eq t ht, hessΦ]⟩
    have hvlim_ext : Tendsto vext atTop (nhds 0) := by
      apply hvlim.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact (hvext_eq t ht).symm
    have hacclim_ext : Tendsto accExt atTop (nhds 0) := by
      apply hacclim.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact (haccExt_eq t ht).symm
    have hgradlim_ext : Tendsto (fun t => gradient Φ (xext t)) atTop (nhds 0) := by
      apply hgradlim.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      simp [hxext_eq t ht, gradΦ]
    exact ⟨hvbound_ext, haccbound_ext, hgradbound_ext, hhessbound_ext,
      hvlim_ext, hacclim_ext, hgradlim_ext⟩

/-- Theorem 2.1(i): global existence and uniqueness of a forward solution. -/
theorem din_global_properties_part_i {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ)
    (hΦ : AssumptionH H Φ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (x₀ v₀ : H) :
    ∃ x v : ℝ → H, x 0 = x₀ ∧ v 0 = v₀ ∧
      IsDINTrajectory H Φ α β x ∧
      (∀ x', x' 0 = x₀ → deriv x' 0 = v₀ →
        IsDINTrajectory H Φ α β x' →
        ContDiff ℝ 2 x' →
        ∀ t, 0 ≤ t → x' t = x t ∧ deriv x' t = v t) := by
  rcases din_forward_internal Φ hΦ α β hα hβ x₀ v₀ with
    ⟨x, v, acc, hx0, hv0, hforward, huniq, -, -, -, -, -, -, -⟩
  refine ⟨x, v, hx0, hv0, hforward, ?_⟩
  intro x' hx0' hv0' htr hxreg
  exact huniq x' hx0' hv0' htr hxreg

/-- Theorem 2.1(ii): energy decay and the associated asymptotic properties. -/
theorem din_global_properties_part_ii {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ)
    (hΦ : AssumptionH H Φ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (x₀ v₀ : H) (x : ℝ → H)
    (hx0 : x 0 = x₀) (hv0 : deriv x 0 = v₀)
    (hforward : IsDINTrajectory H Φ α β x)
    (hxreg : ContDiff ℝ 2 x) :
    (∀ ell : ℝ, (1 - Real.sqrt (α * β)) ^ 2 ≤ ell →
      ell ≤ (1 + Real.sqrt (α * β)) ^ 2 → ∃ l : ℝ,
          AntitoneOn (dinForwardEnergy Φ β ell x) (Set.Ici 0) ∧
          (∃ m : ℝ, ∀ t, 0 ≤ t → m ≤ dinForwardEnergy Φ β ell x t) ∧
          Tendsto (dinForwardEnergy Φ β ell x) atTop (nhds l)) ∧
    MeasureTheory.MemLp (deriv x) 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    MeasureTheory.MemLp (fun t => gradient Φ (x t)) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    (∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l)) ∧
    Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
  have hxC2 : ContDiff ℝ (1 + 1) x := by simpa using hxreg
  have hxdata := contDiff_succ_iff_deriv.mp hxC2
  rcases din_forward_internal Φ hΦ α β hα hβ x₀ v₀ with
    ⟨xg, vg, accg, hxg0, hvg0, hforwardg, huniq, henergy, hvl2, hgl2, hphil, hres, -, hderivg⟩
  have hsame := huniq x hx0 hv0 hforward hxreg
  have hx_eq : ∀ t, 0 ≤ t → x t = xg t := fun t ht => (hsame t ht).1
  have hv_eq : ∀ t, 0 ≤ t → deriv x t = vg t := fun t ht => (hsame t ht).2
  have henergy' : ∀ ell : ℝ, (1 - Real.sqrt (α * β)) ^ 2 ≤ ell →
      ell ≤ (1 + Real.sqrt (α * β)) ^ 2 → ∃ l : ℝ,
        AntitoneOn (dinForwardEnergy Φ β ell x) (Set.Ici 0) ∧
        (∃ m : ℝ, ∀ t, 0 ≤ t → m ≤ dinForwardEnergy Φ β ell x t) ∧
        Tendsto (dinForwardEnergy Φ β ell x) atTop (nhds l) := by
    intro ell hlow hhigh
    obtain ⟨l, hanti, hlower, hlim⟩ := henergy ell hlow hhigh
    have heq : ∀ t, 0 ≤ t → (dinForwardEnergy Φ β ell x) t =
        (dinForwardEnergy Φ β ell xg) t := by
      intro t ht
      have hdxg : deriv xg t = vg t := hderivg t ht
      simp [dinForwardEnergy, hx_eq t ht, hv_eq t ht, hdxg]
    refine ⟨l, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      rw [heq s hs, heq t ht]
      exact hanti hs ht hst
    · obtain ⟨m, hm⟩ := hlower
      exact ⟨m, fun t ht => by rw [heq t ht]; exact hm t ht⟩
    · apply hlim.congr'
      filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => heq t ht⟩] with t ht
      exact ht.symm
  have hvl2' : MeasureTheory.MemLp (deriv x) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply hvl2.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hv_eq t ht.le).symm
  have hgl2' : MeasureTheory.MemLp (fun t => gradient Φ (x t)) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply hgl2.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simp [hx_eq t ht.le]
  have hphil' : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
    obtain ⟨l, hl⟩ := hphil
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [hx_eq t ht]
  have hres' : Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
    apply hres.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [hv_eq t ht, hx_eq t ht]
  exact ⟨henergy', hvl2', hgl2', hphil', hres'⟩

/-- Theorem 2.1(iii): bounded trajectories have bounded derivatives and decay. -/
theorem din_global_properties_part_iii {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ)
    (hΦ : AssumptionH H Φ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (x₀ v₀ : H) (x : ℝ → H)
    (hx0 : x 0 = x₀) (hv0 : deriv x 0 = v₀)
    (hforward : IsDINTrajectory H Φ α β x)
    (hxreg : ContDiff ℝ 2 x) :
    Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) →
      Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧ Tendsto (deriv (deriv x)) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
  intro hxbound
  have hxC2 : ContDiff ℝ (1 + 1) x := by simpa using hxreg
  have hxdata := contDiff_succ_iff_deriv.mp hxC2
  rcases din_forward_internal Φ hΦ α β hα hβ x₀ v₀ with
    ⟨xg, vg, accg, hxg0, hvg0, hforwardg, huniq, -, -, -, -, -, hboundedg, hderivg⟩
  have hsame := huniq x hx0 hv0 hforward hxreg
  have hx_eq : ∀ t, 0 ≤ t → x t = xg t := fun t ht => (hsame t ht).1
  have hv_eq : ∀ t, 0 ≤ t → deriv x t = vg t := fun t ht => (hsame t ht).2
  have hxgbound : Bornology.IsBounded (xg '' Set.Ici (0 : ℝ)) := by
    rcases isBounded_iff_forall_norm_le.mp hxbound with ⟨R, hR⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    rw [← hx_eq t ht]
    exact hR _ ⟨t, ht, rfl⟩
  rcases hboundedg hxgbound with
    ⟨hvboundg, haccboundg, hgradboundg, hhessboundg, hvlimg, hacclimg, hgradlimg⟩
  have hacc_formula : ∀ t, 0 ≤ t →
      deriv (deriv x) t = -(α • deriv x t +
        β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)) := by
    intro t ht
    have he := hforward.2.2 t ht
    exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using he)
  have hvbound : Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) := by
    have himage : (deriv x) '' Set.Ici (0 : ℝ) = vg '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => hv_eq t ht)
    rw [himage]
    exact hvboundg
  have hgradbound : Bornology.IsBounded
      ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) := by
    have himage : (fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ) =
        (fun t => gradient Φ (xg t)) '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => by simp [hx_eq t ht])
    rw [himage]
    exact hgradboundg
  have hhessbound : Bornology.IsBounded
      ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) := by
    have himage : (fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ) =
        (fun t => fderiv ℝ (gradient Φ) (xg t)) '' Set.Ici (0 : ℝ) :=
      Set.image_congr (fun t ht => by simp [hx_eq t ht])
    rw [himage]
    exact hhessboundg
  rcases isBounded_iff_forall_norm_le.mp hhessbound with ⟨Q, hQ⟩
  have haccbound : Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) := by
    rcases isBounded_iff_forall_norm_le.mp hvbound with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbound with ⟨G, hG⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, by simp, rfl⟩)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|α| * V + |β| * Q * V + G, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hv : ‖deriv x t‖ ≤ V := hV _ ⟨t, ht, rfl⟩
    have hg : ‖gradient Φ (x t)‖ ≤ G := hG _ ⟨t, ht, rfl⟩
    have hq : ‖fderiv ℝ (gradient Φ) (x t)‖ ≤ Q := hQ _ ⟨t, ht, rfl⟩
    rw [hacc_formula t ht]
    calc
      ‖-(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t))‖ ≤
          ‖α • deriv x t‖ + ‖β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖ := by
            rw [norm_neg]
            calc
              ‖α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t)‖ ≤
                  ‖α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖ := norm_add_le _ _
              _ ≤ ‖α • deriv x t‖ + ‖β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ |α| * V + |β| * Q * V + G := by
        rw [norm_smul, norm_smul]
        calc
          ‖α‖ * ‖deriv x t‖ + ‖β‖ * ‖(fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ +
              ‖gradient Φ (x t)‖ ≤
              ‖α‖ * V + ‖β‖ * (Q * V) + G := by
                gcongr
                exact (ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul hq hv (norm_nonneg _) hQnonneg)
          _ = |α| * V + |β| * Q * V + G := by
            simp only [Real.norm_eq_abs]
            ring
  have hvlim : Tendsto (deriv x) atTop (nhds 0) := by
    apply hvlimg.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    exact (hv_eq t ht).symm
  have hgradlim : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
    apply hgradlimg.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => ht⟩] with t ht
    simp [hx_eq t ht]
  have hacclim : Tendsto (deriv (deriv x)) atTop (nhds 0) := by
    have hvlim' : Tendsto (deriv x) atTop (nhds 0) := hvlim
    have hgradlim' : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := hgradlim
    have hesslim : Tendsto (fun t => (fderiv ℝ (gradient Φ) (x t)) (deriv x t)) atTop (nhds 0) := by
      apply bounded_clm_apply_tendsto_zero (fun t => fderiv ℝ (gradient Φ) (x t)) (deriv x) Q
      · filter_upwards [Filter.eventually_atTop.2 ⟨0, fun t ht => hQ _ ⟨t, ht, rfl⟩⟩] with t ht
        exact ht
      · exact hvlim'
    have hsumlim : Tendsto
        (fun t => -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
          gradient Φ (x t))) atTop (nhds 0) := by
      simpa using (((hvlim'.const_smul α).add (hesslim.const_smul β)).add hgradlim').neg
    apply hsumlim.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hacc_formula t ht).symm
  exact ⟨hvbound, haccbound, hgradbound, hhessbound, hvlim, hacclim, hgradlim⟩
end Alvarez2002
