import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_3
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_thm_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_4
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
  have hxball : x ∈ Metric.closedBall (0 : H) R' := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx'
  have hyball : y ∈ Metric.closedBall (0 : H) R' := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy'
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
  have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
    exact (contDiff_succ_iff_fderiv.mp
      (show ContDiff ℝ (1 + 1) Φ by
        simpa using hΦ.twice_continuously_differentiable)).2.2
  have hgradC1 : ContDiff ℝ 1 gradΦ := by
    simpa [gradΦ, gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradDeriv : ∀ z, HasFDerivAt gradΦ (hessΦ z) z := by
    intro z
    simpa [hessΦ] using (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  have hhessLip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ p q,
      ‖p‖ ≤ R → ‖q‖ ≤ R → ‖hessΦ p - hessΦ q‖ ≤ L * ‖p - q‖ := by
    intro R hR
    simpa [hessΦ] using hΦ.hessian_lipschitz_on_bounded R hR
  have hgradLipBall : ∀ R : ℝ, ∃ L : ℝ, ∀ p q,
      ‖p‖ ≤ R → ‖q‖ ≤ R → ‖gradΦ p - gradΦ q‖ ≤ L * ‖p - q‖ :=
    grad_lipschitz_on_ball_of_hessian gradΦ hessΦ hgradDeriv hhessLip
  have hloclip : LipschitzOnBoundedSets gradΦ := by
    intro s hs
    rcases isBounded_iff_forall_norm_le.mp hs with ⟨R, hR⟩
    let R' : ℝ := max R 0
    rcases hgradLipBall R' with ⟨L, hL⟩
    let K : NNReal := ⟨max L 0, le_max_right L 0⟩
    refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro p hp q hq
    have hpR : ‖p‖ ≤ R' := (hR p hp).trans (le_max_left _ _)
    have hqR : ‖q‖ ≤ R' := (hR q hq).trans (le_max_left _ _)
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      (hL p q hpR hqR).trans
        (mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg _))
  let a : ℝ := α - 1 / β
  let b : ℝ := 1 / β
  have hb : 0 < b := by
    dsimp [b]
    exact one_div_pos.mpr hβ
  have hab_eq : a + b = α := by
    dsimp [a, b]
    field_simp [ne_of_gt hβ]
    ring
  have hab : 0 < a + b := by simpa [hab_eq] using hα
  have hbβ : b * β = 1 := by
    dsimp [b]
    field_simp [ne_of_gt hβ]
  let y₀g : H :=
    -(β • v₀ + (β ^ 2) • gradΦ x₀ + (β * a) • x₀)
  obtain ⟨xg, yg, hsol, hxgC1, hygC2, huniq⟩ :=
    gdin_existence_uniqueness Φ β a b hΦC1 hΦ.bounded_below hloclip
      hβ hb hab x₀ y₀g
  let vel : ℝ → H := fun t =>
    -β • gradΦ (xg t) - a • xg t - b • yg t
  have hvel_eq (t : ℝ) (ht : 0 ≤ t) : deriv xg t = vel t := by
    calc
      deriv xg t = -(β • gradΦ (xg t) + a • xg t + b • yg t) :=
        eq_neg_iff_add_eq_zero.mpr (by
          simpa [gradΦ, add_assoc] using hsol.1 t ht)
      _ = vel t := by dsimp [vel]; module
  have hyg_eq (t : ℝ) (ht : 0 ≤ t) :
      deriv yg t = -a • xg t - b • yg t := by
    calc
      deriv yg t = -(a • xg t + b • yg t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.2.1 t ht)
      _ = -a • xg t - b • yg t := by module
  have hyg_vel_eq (t : ℝ) (ht : 0 ≤ t) :
      deriv yg t = vel t + β • gradΦ (xg t) := by
    rw [hyg_eq t ht]
    dsimp [vel]
    module
  have hgradx : ∀ t, 0 < t → HasDerivAt (fun s => gradΦ (xg s))
      (hessΦ (xg t) (vel t)) t := by
    intro t ht
    have hxAt : HasDerivAt xg (vel t) t := by
      have hd := (hxgC1.differentiableOn (by norm_num) t ht.le).differentiableAt
        (Ici_mem_nhds ht)
      convert hd.hasDerivAt using 1
      exact (hvel_eq t ht.le).symm
    simpa [Function.comp_def] using
      (hgradDeriv (xg t)).comp_hasDerivAt t hxAt
  let acc : ℝ → H := fun t =>
    -α • vel t - β • hessΦ (xg t) (vel t) - gradΦ (xg t)
  have hxg_deriv (t : ℝ) (ht : 0 < t) : HasDerivAt xg (vel t) t := by
    have hd := (hxgC1.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht)
    convert hd.hasDerivAt using 1
    exact (hvel_eq t ht.le).symm
  have hvel_deriv (t : ℝ) (ht : 0 < t) : HasDerivAt vel (acc t) t := by
    have hyAt : HasDerivAt yg (deriv yg t) t :=
      (hygC2.differentiableOn (by norm_num) t ht.le).differentiableAt
        (Ici_mem_nhds ht) |>.hasDerivAt
    have hraw : HasDerivAt vel
        (-β • hessΦ (xg t) (vel t) - a • vel t - b • deriv yg t) t := by
      change HasDerivAt
        (fun s => -β • gradΦ (xg s) - a • xg s - b • yg s)
        (-β • hessΦ (xg t) (vel t) - a • vel t - b • deriv yg t) t
      convert (((hgradx t ht).const_smul (-β)).sub
        ((hxg_deriv t ht).const_smul a)).sub (hyAt.const_smul b) using 1
    convert hraw using 1
    dsimp [acc]
    rw [hyg_vel_eq t ht.le, ← hab_eq]
    simp only [smul_add, smul_smul]
    rw [hbβ]
    module
  have hgradxCont : ContinuousOn (fun t => gradΦ (xg t)) (Set.Ici 0) :=
    hgradC1.continuous.comp_continuousOn hxgC1.continuousOn
  have hvelCont : ContinuousOn vel (Set.Ici 0) := by
    dsimp [vel]
    exact ((hgradxCont.const_smul (-β)).sub (hxgC1.continuousOn.const_smul a)).sub
      (hygC2.continuousOn.const_smul b)
  have hhessCont : Continuous hessΦ := by
    simpa [hessΦ] using hgradC1.continuous_fderiv one_ne_zero
  have haccCont : ContinuousOn acc (Set.Ici 0) := by
    have hhessx : ContinuousOn (fun t => hessΦ (xg t)) (Set.Ici 0) := by
      simpa [Function.comp_def] using hhessCont.comp_continuousOn hxgC1.continuousOn
    have happly : ContinuousOn (fun t => hessΦ (xg t) (vel t)) (Set.Ici 0) :=
      hhessx.clm_apply hvelCont
    dsimp [acc]
    exact ((hvelCont.const_smul (-α)).sub (happly.const_smul β)).sub hgradxCont
  have hxright : HasDerivWithinAt xg (vel 0) (Set.Ici 0) 0 :=
    din_hasDerivWithinAt_Ici_of_continuous_deriv hxgC1.continuousOn
      (fun t ht => (hxg_deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hxg_deriv t ht).deriv) hvelCont
  have hvelright : HasDerivWithinAt vel (acc 0) (Set.Ici 0) 0 :=
    din_hasDerivWithinAt_Ici_of_continuous_deriv hvelCont
      (fun t ht => (hvel_deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hvel_deriv t ht).deriv) haccCont
  have hvel0 : vel 0 = v₀ := by
    have hbβsq : b * β ^ 2 = β := by rw [show β ^ 2 = β * β by ring, ← mul_assoc, hbβ, one_mul]
    have hbβa : b * (β * a) = a := by rw [← mul_assoc, hbβ, one_mul]
    dsimp [vel]
    rw [hsol.2.2.1, hsol.2.2.2]
    dsimp [y₀g]
    simp only [smul_neg, smul_add, smul_smul]
    rw [hbβ, hbβsq, hbβa]
    module
  let xext : ℝ → H := fun t =>
    if 0 ≤ t then xg t
    else xg 0 + t • vel 0 + ((1 / 2 : ℝ) * t ^ 2) • acc 0
  let vext : ℝ → H := fun t => if 0 ≤ t then vel t else vel 0 + t • acc 0
  let accExt : ℝ → H := fun t => if 0 ≤ t then acc t else acc 0
  have hxext_eq (t : ℝ) (ht : 0 ≤ t) : xext t = xg t := by simp [xext, ht]
  have hvext_eq (t : ℝ) (ht : 0 ≤ t) : vext t = vel t := by simp [vext, ht]
  have haccExt_eq (t : ℝ) (ht : 0 ≤ t) : accExt t = acc t := by
    simp [accExt, ht]
  have hderiv_xext (t : ℝ) : HasDerivAt xext (vext t) t := by
    by_cases ht0 : t = 0
    · subst t
      simpa [xext, vext] using
        (din_piecewise_quadratic_hasDerivAt (f := xg) (d := vel 0)
          (e := acc 0) (a := 0) hxright)
    · by_cases htpos : 0 < t
      · have h := din_piecewise_quadratic_hasDerivAt_of_gt (f := xg) (g := vel)
          (d := vel 0) (e := acc 0) (a := 0) (t := t) htpos (hxg_deriv t htpos)
        convert h using 1 <;> simp [xext, vext, htpos.le]
      · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht0
        have h := din_piecewise_quadratic_hasDerivAt_of_lt (f := xg) (d := vel 0)
          (e := acc 0) (a := 0) (t := t) htneg
        convert h using 1 <;> simp [xext, vext, not_le.mpr htneg]
  have hderiv_vext (t : ℝ) : HasDerivAt vext (accExt t) t := by
    by_cases ht0 : t = 0
    · subst t
      simpa [vext, accExt] using
        (din_piecewise_quadratic_hasDerivAt (f := vel) (d := acc 0)
          (e := (0 : H)) (a := 0) hvelright)
    · by_cases htpos : 0 < t
      · have h := din_piecewise_quadratic_hasDerivAt_of_gt (f := vel) (g := acc)
          (d := acc 0) (e := (0 : H)) (a := 0) (t := t) htpos
          (hvel_deriv t htpos)
        convert h using 1 <;> simp [vext, accExt, htpos.le]
      · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht0
        have h := din_piecewise_quadratic_hasDerivAt_of_lt (f := vel) (d := acc 0)
          (e := (0 : H)) (a := 0) (t := t) htneg
        convert h using 1 <;> simp [vext, accExt, not_le.mpr htneg]
  have hderiv_xext_eq : deriv xext = vext := funext fun t => (hderiv_xext t).deriv
  have hderiv_vext_eq : deriv vext = accExt := funext fun t => (hderiv_vext t).deriv
  have hxext0 : xext 0 = x₀ := by simp [xext, hsol.2.2.1]
  have hvext0 : vext 0 = v₀ := by simp [vext, hvel0]
  have hforward : IsDINTrajectory H Φ α β xext := by
    refine ⟨hα, hβ, ?_⟩
    intro t ht
    rw [hderiv_xext_eq, hderiv_vext_eq]
    rw [haccExt_eq t ht, hvext_eq t ht, hxext_eq t ht]
    dsimp [acc, gradΦ, hessΦ]
    module
  have henergy : ∀ ell : ℝ, (1 - Real.sqrt (α * β)) ^ 2 ≤ ell →
      ell ≤ (1 + Real.sqrt (α * β)) ^ 2 → ∃ l : ℝ,
        AntitoneOn (dinForwardEnergy Φ β ell xext) (Set.Ici 0) ∧
        (∃ m : ℝ, ∀ t, 0 ≤ t → m ≤ dinForwardEnergy Φ β ell xext t) ∧
        Tendsto (dinForwardEnergy Φ β ell xext) atTop (nhds l) := by
    intro ell hlow hhigh
    have hlow' : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell := by
      rw [din_endpoint_lower_coeff α β a b hα hβ hab_eq (by rfl)]
      exact hlow
    have hhigh' : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
      rw [din_endpoint_upper_coeff α β a b hα hβ hab_eq (by rfl)]
      exact hhigh
    obtain ⟨hanti, hlower, l, hlim⟩ :=
      gdin_lyapunov_energy_properties Φ β a b hΦC1 hΦ.bounded_below
        hβ hb hab x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol ell hlow' hhigh'
    have heq (t : ℝ) (ht : 0 ≤ t) :
        LyapunovEnergy Φ a b ell (xg t) (yg t) =
          dinForwardEnergy Φ β ell xext t := by
      have hq : a • xg t + b • yg t = -(vel t + β • gradΦ (xg t)) := by
        dsimp [vel]
        module
      unfold LyapunovEnergy dinForwardEnergy
      rw [(hderiv_xext t).deriv, hxext_eq t ht, hvext_eq t ht]
      simp only [gradΦ, hq, norm_neg]
    refine ⟨l, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      rw [← heq s hs, ← heq t ht]
      exact hanti hs ht hst
    · obtain ⟨m, hm⟩ := hlower
      exact ⟨m, fun t ht => by rw [← heq t ht]; exact hm t ht⟩
    · apply hlim.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact heq t ht
  have hvL2base : MeasureTheory.MemLp vel 2
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := by
    have h := gdin_x_derivative_memL2 Φ β a b hΦC1 hΦ.bounded_below
      hβ hb hab x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol
    unfold MemL2OnNonnegative at h
    apply h.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact hvel_eq t ht
  have hvL2 : MeasureTheory.MemLp vext 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply (hvL2base.mono_measure (MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume Set.Ioi_subset_Ici_self)).ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hvext_eq t ht.le).symm
  have hgradL2base : MeasureTheory.MemLp (fun t => gradΦ (xg t)) 2
      (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) := by
    simpa [MemL2OnNonnegative] using
      (gdin_gradient_memL2 Φ β a b hΦC1 hΦ.bounded_below hβ hb hab
        x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol)
  have hgradL2 : MeasureTheory.MemLp (fun t => gradient Φ (xext t)) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply (hgradL2base.mono_measure (MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume Set.Ioi_subset_Ici_self)).ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simp [hxext_eq t ht.le, gradΦ]
  have hΦlim : ∃ l : ℝ, Tendsto (fun t => Φ (xext t)) atTop (nhds l) := by
    obtain ⟨l, hl⟩ := gdin_phi_limit Φ β a b hΦC1 hΦ.bounded_below
      hβ hb hab x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [hxext_eq t ht]
  have hres : Tendsto (fun t => vext t + β • gradient Φ (xext t)) atTop (nhds 0) := by
    have hr := gdin_residual_limit Φ β a b hΦC1 hΦ.bounded_below
      hβ hb hab x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol
    apply hr.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hvel_eq t ht]
    simp [hvext_eq t ht, hxext_eq t ht]
  have hbounded : Bornology.IsBounded (xext '' Set.Ici (0 : ℝ)) →
      Bornology.IsBounded (vext '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded (accExt '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => gradient Φ (xext t)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (xext t)) '' Set.Ici (0 : ℝ)) ∧
      Tendsto vext atTop (nhds 0) ∧ Tendsto accExt atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (xext t)) atTop (nhds 0) := by
    intro hxbound
    have hxgbound : BoundedOnNonnegative xg := by
      unfold BoundedOnNonnegative
      apply hxbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, hxext_eq t ht⟩
    rcases gdin_bounded_asymptotics Φ β a b hΦC1 hΦ.bounded_below hloclip
      hβ hb hab x₀ y₀g xg yg ⟨hxgC1, hygC2⟩ hsol hxgbound with
      ⟨hvgbound, hgradbound, hvglim, hgradlim⟩
    have hvelbound : Bornology.IsBounded (vel '' Set.Ici (0 : ℝ)) := by
      have himage : vel '' Set.Ici (0 : ℝ) = (deriv xg) '' Set.Ici (0 : ℝ) :=
        Set.image_congr (fun t ht => (hvel_eq t ht).symm)
      rw [himage]
      exact hvgbound
    rcases isBounded_iff_forall_norm_le.mp hxgbound with ⟨R, hR⟩
    let R' : ℝ := max R 1 + 1
    have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 1]
    obtain ⟨L, hLpos, hL⟩ := hhessLip R' hR'
    let M : ℝ := L * R' + ‖hessΦ 0‖
    have hhessbound : Bornology.IsBounded
        ((fun t => hessΦ (xg t)) '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨M, ?_⟩
      rintro q ⟨t, ht, rfl⟩
      have hxt : ‖xg t‖ ≤ R := hR _ ⟨t, ht, rfl⟩
      have hxt' : ‖xg t‖ ≤ R' := by
        dsimp [R']
        linarith [le_max_left R 1]
      have hzero : ‖(0 : H)‖ ≤ R' := by simpa using hR'.le
      have hd := hL (xg t) 0 hxt' hzero
      calc
        ‖hessΦ (xg t)‖ = ‖hessΦ (xg t) - hessΦ 0 + hessΦ 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖hessΦ (xg t) - hessΦ 0‖ + ‖hessΦ 0‖ := norm_add_le _ _
        _ ≤ L * ‖xg t - 0‖ + ‖hessΦ 0‖ := by gcongr
        _ ≤ L * R' + ‖hessΦ 0‖ := by gcongr; simpa using hxt'
        _ = M := rfl
    rcases isBounded_iff_forall_norm_le.mp hvelbound with ⟨V, hV⟩
    rcases isBounded_iff_forall_norm_le.mp hgradbound with ⟨G, hG⟩
    rcases isBounded_iff_forall_norm_le.mp hhessbound with ⟨Q, hQ⟩
    have hQnonneg : 0 ≤ Q := le_trans (norm_nonneg _) (hQ _ ⟨0, by simp, rfl⟩)
    have haccbound : Bornology.IsBounded (acc '' Set.Ici (0 : ℝ)) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨|α| * V + |β| * Q * V + G, ?_⟩
      rintro z ⟨t, ht, rfl⟩
      have hv : ‖vel t‖ ≤ V := hV _ ⟨t, ht, rfl⟩
      have hg : ‖gradΦ (xg t)‖ ≤ G := hG _ ⟨t, ht, rfl⟩
      have hq : ‖hessΦ (xg t)‖ ≤ Q := hQ _ ⟨t, ht, rfl⟩
      dsimp [acc]
      calc
        ‖-α • vel t - β • hessΦ (xg t) (vel t) - gradΦ (xg t)‖ ≤
            ‖-α • vel t‖ + ‖β • hessΦ (xg t) (vel t)‖ + ‖gradΦ (xg t)‖ := by
          calc
            _ ≤ ‖-α • vel t - β • hessΦ (xg t) (vel t)‖ + ‖gradΦ (xg t)‖ :=
              norm_sub_le _ _
            _ ≤ ‖-α • vel t‖ + ‖β • hessΦ (xg t) (vel t)‖ + ‖gradΦ (xg t)‖ := by
              gcongr
              exact norm_sub_le _ _
        _ ≤ |α| * V + |β| * Q * V + G := by
          rw [norm_smul, norm_neg, norm_smul]
          have hqv : ‖hessΦ (xg t) (vel t)‖ ≤ Q * V :=
            (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hq hv (norm_nonneg _) hQnonneg)
          calc
            |α| * ‖vel t‖ + |β| * ‖hessΦ (xg t) (vel t)‖ + ‖gradΦ (xg t)‖ ≤
                |α| * V + |β| * (Q * V) + G := by gcongr
            _ = |α| * V + |β| * Q * V + G := by ring
    have hvlim : Tendsto vel atTop (nhds 0) := by
      apply hvglim.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hvel_eq t ht
    have happlylim : Tendsto (fun t => hessΦ (xg t) (vel t)) atTop (nhds 0) := by
      apply bounded_clm_apply_tendsto_zero (fun t => hessΦ (xg t)) vel Q
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact hQ _ ⟨t, ht, rfl⟩
      · exact hvlim
    have hacclim : Tendsto acc atTop (nhds 0) := by
      have h1 : Tendsto (fun t => (-α) • vel t) atTop (nhds 0) := by
        simpa using hvlim.const_smul (-α)
      have h2 : Tendsto (fun t => β • hessΦ (xg t) (vel t)) atTop (nhds 0) := by
        simpa using happlylim.const_smul β
      have h3 : Tendsto
          (fun t => (-α) • vel t - β • hessΦ (xg t) (vel t)) atTop (nhds 0) := by
        simpa using h1.sub h2
      dsimp [acc]
      simpa using h3.sub hgradlim
    have hvbound_ext : Bornology.IsBounded (vext '' Set.Ici (0 : ℝ)) := by
      apply hvelbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hvext_eq t ht).symm⟩
    have haccbound_ext : Bornology.IsBounded (accExt '' Set.Ici (0 : ℝ)) := by
      apply haccbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (haccExt_eq t ht).symm⟩
    have hgradbound_ext : Bornology.IsBounded
        ((fun t => gradient Φ (xext t)) '' Set.Ici (0 : ℝ)) := by
      apply hgradbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [hxext_eq t ht]⟩
    have hhessbound_ext : Bornology.IsBounded
        ((fun t => fderiv ℝ (gradient Φ) (xext t)) '' Set.Ici (0 : ℝ)) := by
      apply hhessbound.subset
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [hxext_eq t ht, hessΦ]⟩
    have hvlim_ext : Tendsto vext atTop (nhds 0) := by
      apply hvlim.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (hvext_eq t ht).symm
    have hacclim_ext : Tendsto accExt atTop (nhds 0) := by
      apply hacclim.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (haccExt_eq t ht).symm
    have hgradlim_ext : Tendsto (fun t => gradient Φ (xext t)) atTop (nhds 0) := by
      apply hgradlim.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [hxext_eq t ht]
    exact ⟨hvbound_ext, haccbound_ext, hgradbound_ext, hhessbound_ext,
      hvlim_ext, hacclim_ext, hgradlim_ext⟩
  have hunique : ∀ x', x' 0 = x₀ → deriv x' 0 = v₀ →
      IsDINTrajectory H Φ α β x' → ContDiff ℝ 2 x' →
      ∀ t, 0 ≤ t → x' t = xext t ∧ deriv x' t = vext t := by
    intro x' hx0' hv0' htr hxreg
    have hy0compat : y₀g =
        -(β • deriv x' 0 + (β ^ 2) • gradient Φ (x' 0) + (β * a) • x' 0) := by
      simp [y₀g, gradΦ, hx0', hv0']
    obtain ⟨y', hy'C2, hsol'⟩ :=
      (din_iff_gdin Φ α β a b x' x₀ y₀g
        hΦ.twice_continuously_differentiable hxreg hα hβ rfl rfl hx0' hy0compat).mp htr
    have hsame := huniq x' y' hsol'
      ⟨(hxreg.of_le (by norm_num)).contDiffOn, hy'C2⟩
    intro t ht
    have hpair := hsame t ht
    have hderivsame : deriv x' t = deriv xg t := by
      have hxEq := hsol'.1 t ht
      have hgEq := hsol.1 t ht
      rw [← hpair.1, ← hpair.2] at hxEq
      have hxneg : deriv x' t =
          -(β • gradient Φ (xg t) + a • xg t + b • yg t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hxEq)
      have hgneg : deriv xg t =
          -(β • gradient Φ (xg t) + a • xg t + b • yg t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hgEq)
      exact hxneg.trans hgneg.symm
    exact ⟨hpair.1.symm.trans (hxext_eq t ht).symm,
      hderivsame.trans ((hvel_eq t ht).trans (hvext_eq t ht).symm)⟩
  exact ⟨xext, vext, accExt, hxext0, hvext0, hforward, hunique, henergy,
    hvL2, hgradL2, hΦlim, hres, hbounded, fun t _ => (hderiv_xext t).deriv⟩


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
              ‖α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ + ‖gradient Φ (x t)‖
                := norm_add_le _ _
            _ ≤ ‖α • deriv x t‖ + ‖β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t)‖ +
              ‖gradient Φ (x t)‖ := by gcongr; exact norm_add_le _ _
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
