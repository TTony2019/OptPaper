import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.thm_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.thm_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_4
import Foundation.Projection.BestApproximation
import Foundation.Hilbert.WeakTopology

set_option maxHeartbeats 800000

namespace Alvarez2000

open Filter
open MeasureTheory
open scoped InnerProductSpace

/-- A pointwise estimate on a Chebyshev set specializes to its metric projection. -/
theorem projection_metric_estimate_of_pointwise {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {S : Set H} (hS_cheb : IsChebyshev S) {y uhat : H} {d : ℝ}
    (hestimate : ∀ z ∈ S, ‖uhat - z‖ ≤ ‖y - z‖ + d) :
    ‖uhat - projectionPoint S hS_cheb y‖ ≤ Metric.infDist y S + d := by
  let p := projectionPoint S hS_cheb y
  have hp : p ∈ S := projectionPoint_mem S hS_cheb y
  have hbest : dist y p = Metric.infDist y S :=
    (projectionPoint_isBestApproximation S hS_cheb y).2
  have hpoint := hestimate p hp
  rw [← hbest]
  simpa only [dist_eq_norm] using hpoint

/-- A positive self-adjoint quadratic potential is even. -/
theorem quadratic_potential_isEven {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Phi : H → ℝ} (A : H →L[ℝ] H)
    (hPhiA : ∀ q : H, Phi q = (1 / 2 : ℝ) * ⟪A q, q⟫_ℝ) :
    IsEvenFunction Phi := by
  intro q
  rw [hPhiA, hPhiA]
  simp

/-- At a minimizer, the squared-distance differential inequality has no
potential remainder.  This is the local differential input for (2.11). -/
theorem scalar_distance_damped_ineq_at_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {x : H}
    (hx : x ∈ argmin Phi (potential_range_bddBelow hPhi)) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2)) t +
        gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2) t ≤
      ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : H := fderiv ℝ v t 1
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2
  have hu : HasDerivAt sys.u (v t) t := by
    simpa only [v] using (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
  have hv : HasDerivAt v a t := by
    simpa only [v, a] using dissipativeSystem_velocity_hasDerivAt_pos sys ht
  have hphi : HasDerivAt phi ⟪v t, sys.u t - x⟫_ℝ t := by
    have hsub : HasDerivAt (fun s => sys.u s - x) (v t) t := by
      simpa only using hu.sub_const x
    have hsq := (hasDerivAt_const t (1 / 2 : ℝ)).mul hsub.norm_sq
    convert hsq using 1 <;> simp [real_inner_comm]
  have hfirst : ∀ᶠ s in nhds t,
      deriv phi s = ⟪v s, sys.u s - x⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hus : HasDerivAt sys.u (v s) s := by
      simpa only [v] using (dissipativeSystem_differentiableAt_pos sys hs).hasDerivAt
    have hsubs : HasDerivAt (fun r => sys.u r - x) (v s) s := by
      simpa only using hus.sub_const x
    have hsqs := (hasDerivAt_const s (1 / 2 : ℝ)).mul hsubs.norm_sq
    have hderiv : HasDerivAt phi ⟪v s, sys.u s - x⟫_ℝ s := by
      convert hsqs using 1 <;> simp [real_inner_comm]
    exact hderiv.deriv
  have hinner : HasDerivAt (fun s => ⟪v s, sys.u s - x⟫_ℝ)
      (⟪a, sys.u t - x⟫_ℝ + ⟪v t, v t⟫_ℝ) t := by
    simpa only [add_comm] using hv.inner ℝ (hu.sub_const x)
  have hsecond : deriv (deriv phi) t =
      ⟪a, sys.u t - x⟫_ℝ + ‖v t‖ ^ 2 := by
    rw [show deriv (deriv phi) t = deriv (fun s => ⟪v s, sys.u s - x⟫_ℝ) t by
      exact Filter.EventuallyEq.deriv_eq hfirst]
    simpa only [real_inner_self_eq_norm_sq] using hinner.deriv
  have heq := sys.equation t (le_of_lt ht)
  have hinnerEq := congrArg (fun z : H => ⟪z, sys.u t - x⟫_ℝ) heq
  have hsupp := scalar_convex_gradient_support hPhi.convex sys.is_gradient (sys.u t) x
  have hmin : Phi x ≤ Phi (sys.u t) := by
    rw [show Phi x = sInf (Set.range Phi) from hx]
    exact potential_sInf_le hPhi _
  change deriv (deriv phi) t + gamma * deriv phi t ≤ _
  rw [hsecond, hphi.deriv]
  simp only [v, a] at hinnerEq ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left] at hinnerEq
  simp only [inner_zero_left] at hinnerEq
  have hneg : ⟪gradPhi (sys.u t), x - sys.u t⟫_ℝ =
      -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    rw [show x - sys.u t = -(sys.u t - x) by abel, inner_neg_right]
  have hgrad : Phi (sys.u t) - Phi x ≤ ⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    rw [hneg] at hsupp
    linarith
  have hdamped :
      ⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, sys.u t - x⟫_ℝ +
          gamma * ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ ≤ Phi x - Phi (sys.u t) := by
    linarith [hinnerEq, hgrad]
  linarith

private theorem scalar_damped_energy_from_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel0 : Tendsto (fun s => fderiv ℝ sys.u s 1) (nhdsWithin 0 (Set.Ioi 0))
      (nhds v0)) {t : ℝ} (ht : 0 ≤ t) :
    ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) +
        gamma * (∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2) =
      (1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [sys.initial_position, sys.initial_velocity]
  let E : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 + Phi (sys.u s)
  let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2
  have hu0 : Tendsto sys.u (nhdsWithin 0 (Set.Ioi 0)) (nhds u0) := by
    have hcont : ContinuousWithinAt sys.u (Set.Ici 0) 0 :=
      sys.contDiff.continuousOn 0 (by simp)
    have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 (Set.Ici 0) :=
      nhdsWithin_mono 0 Set.Ioi_subset_Ici_self
    simpa [sys.initial_position] using hcont.tendsto.mono_left hsub
  have hE0 : Tendsto E (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0)) := by
    have hv := (hvel0.norm.pow 2).const_mul (1 / 2 : ℝ)
    have hp := (hPhi.contDiff.continuous.tendsto u0).comp hu0
    simpa [E] using hv.add hp
  have hdiff : ∀ ⦃s : ℝ⦄, 0 < s → DifferentiableAt ℝ E s := by
    intro s hs
    have hv : ContDiffAt ℝ 1 (fun r => fderiv ℝ sys.u r 1) s :=
      ((sys.contDiff.contDiffAt (Ici_mem_nhds hs)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
    have hu := (sys.contDiff.contDiffAt (Ici_mem_nhds hs)).differentiableAt (by norm_num)
    have hp := (hPhi.contDiff.differentiable (by norm_num)).differentiableAt.comp s hu
    exact ((contDiffAt_const (c := (1 / 2 : ℝ)).mul (ContDiffAt.norm_sq ℝ hv)).differentiableAt
      (by norm_num)).add hp
  have hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt E (-gamma * q s) s := by
    intro s hs
    convert (hdiff hs.1).hasDerivAt using 1
    simpa [E, q] using (scalar_damped_energy_deriv_pos sys hs.1).symm
  have hqOn : IntegrableOn q (Set.Icc 0 t) := by
    simpa only [q] using
      (scalar_damped_minimizing_property hPhi sys).1.mono_set Set.Icc_subset_Ici_self
  have hq : IntervalIntegrable q volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.le).mpr hqOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht hderiv
    (hq.const_mul (-gamma)) hE0
    ((hdiff ht).continuousAt.tendsto.mono_left inf_le_left)
  change E t + gamma * (∫ s in 0..t, q s) = _
  rw [show (∫ s in 0..t, -gamma * q s) = -gamma * ∫ s in 0..t, q s by
    rw [← intervalIntegral.integral_const_mul]] at hFTC
  linarith

/-- The evenness forced by a quadratic potential supplies the strong-limit
alternative from Theorem 2.4.  This is kept public because the same reduction
is useful for later quadratic items. -/
theorem quadratic_scalar_damped_has_strong_minimizer_limit {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 uhat : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hhat : uhat ∈ argmin Phi (potential_range_bddBelow hPhi))
    (A : H →L[ℝ] H)
    (hPhiA : ∀ q : H, Phi q = (1 / 2 : ℝ) * ⟪A q, q⟫_ℝ) :
    ∃ w ∈ argmin Phi (potential_range_bddBelow hPhi),
      Tendsto sys.u atTop (nhds w) := by
  exact scalar_damped_strong_convergence hPhi sys
    (Or.inl ⟨⟨uhat, hhat⟩, quadratic_potential_isEven A hPhiA⟩)

/-- In the quadratic case, the strong minimizer limit is forced to be the
already specified weak limit. -/
private theorem quadratic_scalar_damped_tendsto_weak_limit {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 uhat : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hhat : uhat ∈ argmin Phi (potential_range_bddBelow hPhi))
    (hWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
      (nhds (toWeakSpace ℝ H uhat)))
    (A : H →L[ℝ] H)
    (hPhiA : ∀ q : H, Phi q = (1 / 2 : ℝ) * ⟪A q, q⟫_ℝ) :
    Tendsto sys.u atTop (nhds uhat) := by
  obtain ⟨w, hw, hstrong⟩ :=
    quadratic_scalar_damped_has_strong_minimizer_limit hPhi sys hhat A hPhiA
  have hweakStrong : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
      (nhds (toWeakSpace ℝ H w)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto w).comp hstrong
  have hw_eq : w = uhat :=
    (toWeakSpace ℝ H).injective (tendsto_nhds_unique hweakStrong hWeak)
  simpa [hw_eq] using hstrong

/-- Exact energy balance on a positive compact time interval.  This endpoint-free
version is useful independently of Proposition 2.5. -/
theorem scalar_damped_energy_interval_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u b 1‖ ^ 2 + Phi (sys.u b)) +
        gamma * (∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2) =
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u a 1‖ ^ 2 + Phi (sys.u a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let E : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 + Phi (sys.u s)
  have hu : ContDiffOn ℝ 2 sys.u (Set.Icc a b) :=
    sys.contDiff.mono (fun s hs => le_trans (le_of_lt ha) hs.1)
  have hv : ContDiffOn ℝ 1 (fun s => fderiv ℝ sys.u s 1) (Set.Icc a b) := by
    intro s hs
    have hlocal := sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le ha hs.1))
    exact ((hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
  have hE : ContDiffOn ℝ 1 E (Set.Icc a b) := by
    apply ContDiffOn.add
    · exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hv)
    · simpa only [Function.comp_apply] using
        hPhi.contDiff.contDiffOn.comp (hu.of_le (by norm_num)) (fun _ _ => Set.mem_univ _)
  have hderivInt : IntervalIntegrable (deriv E) volume a b := by
    have hcont :=
      (hE.derivWithin (m := 0) (uniqueDiffOn_Icc hab) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hab.le).congr_ae
    simp only [hab.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hFTC : E b - E a = ∫ t in a..b, deriv E t := by
    simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hE hab.le).symm
  have hderiv : ∀ t ∈ Set.Ioc a b, deriv E t = -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    exact scalar_damped_energy_deriv_pos sys (lt_of_lt_of_le ha (le_of_lt ht.1))
  have hint : (∫ t in a..b, deriv E t) =
      ∫ t in a..b, -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    simp only [Set.uIoc_of_le hab.le] at ht
    exact hderiv t ht
  have henergy : E b - E a = -gamma * (∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2) := by
    rw [hFTC, hint, ← intervalIntegral.integral_const_mul]
  change E b + gamma * (∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2) = E a
  linarith

/-- Weak convergence preserves every eventual upper bound on the distance to a
fixed point.  This is the concrete lower-semicontinuity form needed when the
finite-time scalar comparison is sent to infinity. -/
private theorem weak_norm_sub_le_of_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {u : ℝ → H} {uhat x : H}
    (hweak : Tendsto (fun t => toWeakSpace ℝ H (u t)) atTop
      (nhds (toWeakSpace ℝ H uhat))) {B : ℝ}
    (hB : ∀ᶠ t in atTop, ‖u t - x‖ ≤ B) :
    ‖uhat - x‖ ≤ B := by
  have hlsc : LowerSemicontinuous
      (fun y : WeakSpace ℝ H ↦ dist x ((toWeakSpace ℝ H).symm y)) := by
    have hrepr :
        (fun y : WeakSpace ℝ H ↦ dist x ((toWeakSpace ℝ H).symm y)) =
          fun y : WeakSpace ℝ H ↦
            ⨆ z : weakClosedUnitBall H,
              |inner ℝ ((toWeakSpace ℝ H).symm z)
                (x - ((toWeakSpace ℝ H).symm y))| := by
      funext y
      calc
        dist x ((toWeakSpace ℝ H).symm y) = ‖x - ((toWeakSpace ℝ H).symm y)‖ := by
          rw [dist_eq_norm]
        _ = ‖evalOnWeakClosedUnitBall H (x - ((toWeakSpace ℝ H).symm y))‖ := by
          rw [evalOnWeakClosedUnitBall_norm_eq]
        _ = ⨆ z : weakClosedUnitBall H,
            ‖evalOnWeakClosedUnitBall H (x - ((toWeakSpace ℝ H).symm y)) z‖ := by
          rw [ContinuousMap.norm_eq_iSup_norm]
        _ = _ := rfl
    rw [hrepr]
    refine lowerSemicontinuous_ciSup ?_ ?_
    · intro y
      refine ⟨‖x - ((toWeakSpace ℝ H).symm y)‖, ?_⟩
      rintro _ ⟨z, rfl⟩
      calc
        |inner ℝ ((toWeakSpace ℝ H).symm z) (x - ((toWeakSpace ℝ H).symm y))|
            ≤ ‖(toWeakSpace ℝ H).symm z‖ * ‖x - ((toWeakSpace ℝ H).symm y)‖ :=
              abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖x - ((toWeakSpace ℝ H).symm y)‖ := by
          gcongr
          exact weakClosedUnitBall_norm_le_one z
        _ = ‖x - ((toWeakSpace ℝ H).symm y)‖ := by ring
    · intro z
      have hcont : Continuous fun y : WeakSpace ℝ H ↦
          inner ℝ ((toWeakSpace ℝ H).symm z) ((toWeakSpace ℝ H).symm y) := by
        simpa [real_inner_comm] using
          (weakSpace_continuous_inner_right ((toWeakSpace ℝ H).symm z))
      have hcoord : Continuous fun y : WeakSpace ℝ H ↦
          inner ℝ ((toWeakSpace ℝ H).symm z) x -
            inner ℝ ((toWeakSpace ℝ H).symm z) ((toWeakSpace ℝ H).symm y) :=
        continuous_const.sub hcont
      convert hcoord.abs.lowerSemicontinuous using 1
      ext y
      rw [inner_sub_right]
  by_contra hle
  have hlt : B < dist x uhat := by
    simpa only [dist_eq_norm, norm_sub_rev] using lt_of_not_ge hle
  have hnhds : ∀ᶠ y : WeakSpace ℝ H in nhds (toWeakSpace ℝ H uhat),
      B < dist x ((toWeakSpace ℝ H).symm y) :=
    hlsc (toWeakSpace ℝ H uhat) B (by simpa using hlt)
  have hlarge : ∀ᶠ t in atTop, B < dist x (u t) := by
    filter_upwards [hweak.eventually hnhds] with t ht
    simpa using ht
  rcases (hB.and hlarge).exists with ⟨t, htB, htlarge⟩
  exact (not_lt_of_ge (by simpa [dist_eq_norm, norm_sub_rev] using htB)) htlarge

/-- The trajectory has the source-prescribed right endpoint value.  This is
kept separate because the differential identities below are valid only away
from zero, while the paper takes their limits as the left endpoint tends to
zero through positive times. -/
private theorem dissipativeSystem_tendsto_initial_position_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    Tendsto sys.u (nhdsWithin 0 (Set.Ioi 0)) (nhds u0) := by
  have hcont : ContinuousWithinAt sys.u (Set.Ici 0) 0 :=
    sys.contDiff.continuousOn 0 (by simp)
  have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 (Set.Ici 0) :=
    nhdsWithin_mono 0 Set.Ioi_subset_Ici_self
  simpa [sys.initial_position] using hcont.tendsto.mono_left hsub

/-- The squared distance and its first derivative have the expected right
limits at the initial endpoint.  The differential comparisons below are only
available at positive times, so this packages the endpoint data separately. -/
private theorem scalar_distance_initial_right_limits
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v0)) :
    Tendsto (fun t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2)) ∧
    Tendsto (fun t => deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2) t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ⟪v0, u0 - x⟫_ℝ) := by
  let p : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2
  have hu0 := dissipativeSystem_tendsto_initial_position_right sys
  have hp0 : Tendsto p (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2)) := by
    have hsub := hu0.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x))
    simpa [p] using (hsub.norm.pow 2).const_mul (1 / 2 : ℝ)
  have hpderiv : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      deriv p t = ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ := by
    filter_upwards [show Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) from
      self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
      (dissipativeSystem_differentiableAt_pos sys htpos).hasDerivAt
    have hsub : HasDerivAt (fun s => sys.u s - x) (fderiv ℝ sys.u t 1) t :=
      hu.sub_const x
    have hsq := (hasDerivAt_const t (1 / 2 : ℝ)).mul hsub.norm_sq
    convert hsq.deriv using 1 <;> simp [p, real_inner_comm]
  have hinner : Tendsto (fun t => ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ⟪v0, u0 - x⟫_ℝ) := by
    exact Filter.Tendsto.inner hvel0 (hu0.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x)))
  refine ⟨hp0, ?_⟩
  apply hinner.congr'
  filter_upwards [hpderiv] with t ht
  exact ht.symm

/-! Integrating the minimizing distance inequality once is enough for the
localization estimate.  The initial endpoint is supplied by the one-sided
limits packaged above. -/
private theorem scalar_damped_distance_integrated_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (hgamma : 0 < gamma)
    (hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v0))
    (hx : x ∈ argmin Phi (potential_range_bddBelow hPhi))
    (hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0)) :
    ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2) t +
          gamma * ((1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2) ≤
        ⟪v0, u0 - x⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2) +
          ∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2 := by
  intro t ht
  let p : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2
  let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2
  let F : ℝ → ℝ := fun s => deriv p s + gamma * p s
  have hright := scalar_distance_initial_right_limits (x := x) sys hvel0
  have hFright : Tendsto F (nhdsWithin 0 (Set.Ioi 0))
      (nhds (⟪v0, u0 - x⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2))) := by
    have hgamma_lim : Tendsto (fun _ : ℝ => gamma)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds gamma) := tendsto_const_nhds
    have hsum := hright.2.add (hgamma_lim.mul hright.1)
    simpa [F, p, add_comm, add_left_comm, add_assoc] using hsum
  have hcombined : ∀ {a b : ℝ}, 0 < a → a ≤ b →
      F b ≤ F a + ∫ s in a..b, q s := by
    intro a b ha hab
    rcases hab.eq_or_lt with rfl | hab
    · simp
    let hp : ContDiffOn ℝ 2 p (Set.Icc a b) := by
      exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ
        ((sys.contDiff.mono (fun s hs => le_trans (le_of_lt ha) hs.1)).sub contDiffOn_const))
    have hpd : ContDiffOn ℝ 1 (deriv p) (Set.Icc a b) := by
      have hw := hp.derivWithin (m := 1) (uniqueDiffOn_Icc hab) (by norm_num)
      refine hw.congr ?_
      intro s hs
      rw [deriv, derivWithin,
        fderivWithin_eq_fderiv ((uniqueDiffOn_Icc hab) s hs)]
      have hu : DifferentiableAt ℝ sys.u s :=
        dissipativeSystem_differentiableAt_pos sys (lt_of_lt_of_le ha hs.1)
      exact (differentiableAt_const (c := (1 / 2 : ℝ))).mul
        ((hu.sub_const x).norm_sq ℝ)
    have hFdiff : ContDiffOn ℝ 1 F (Set.Icc a b) := by
      exact hpd.add (contDiffOn_const.mul (hp.of_le (by norm_num)))
    have hqcont : ContinuousOn q (Set.Icc a b) := by
      intro s hs
      have hu := sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le ha hs.1))
      have hv : ContDiffAt ℝ 1 (fun r => fderiv ℝ sys.u r 1) s :=
        (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))
      exact (ContDiffAt.norm_sq ℝ hv).continuousAt.continuousWithinAt
    have hFint : IntervalIntegrable (deriv F) volume a b := by
      have hc := (hFdiff.derivWithin (m := 0) (uniqueDiffOn_Icc hab) (by simp)).continuousOn
      apply (hc.intervalIntegrable_of_Icc hab.le).congr_ae
      simp only [hab.le, Set.uIoc_of_le]
      rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
    have hqint : IntervalIntegrable q volume a b :=
      hqcont.intervalIntegrable_of_Icc hab.le
    have hderiv : ∀ s ∈ Set.Ioo a b, deriv F s ≤ q s := by
      intro s hs
      have hpderiv : HasDerivAt p (deriv p s) s := by
        exact (hp.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt
          (by norm_num) |>.hasDerivAt
      have hFderiv : HasDerivAt F (deriv (deriv p) s + gamma * deriv p s) s := by
        have hpp := (hpd.contDiffAt (Icc_mem_nhds hs.1 hs.2)).differentiableAt
          (by norm_num) |>.hasDerivAt
        convert hpp.add ((hasDerivAt_const s gamma).mul hpderiv) using 1 <;>
          simp [F]
      have hineq := scalar_distance_damped_ineq_at_argmin hPhi sys hx
        (lt_trans ha hs.1)
      rw [hFderiv.deriv]
      simpa [p, q] using hineq
    have hFTC : F b - F a = ∫ s in a..b, deriv F s := by
      simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hFdiff hab.le).symm
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab.le hFint hqint hderiv
    rw [← hFTC] at hmono
    linarith
  have hevent : ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0),
      F t ≤ F a + ∫ s in 0..t, q s := by
    have hlat0 : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), a < t :=
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
        (Iio_mem_nhds ht)
    filter_upwards [self_mem_nhdsWithin, hlat0] with a ha hlat
    have hba := hcombined (a := a) (b := t) ha hlat.le
    have hq0 : IntervalIntegrable q volume 0 a := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le ha.le).2
      simpa [q] using hvel.mono_set Set.Icc_subset_Ici_self
    have hqAT : IntervalIntegrable q volume a t := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hlat.le).2
      apply hvel.mono_set
      intro s hs
      exact le_trans (le_of_lt ha) hs.1
    have hadd := intervalIntegral.integral_add_adjacent_intervals hq0 hqAT
    have hqnonneg : 0 ≤ ∫ s in 0..a, q s := by
      apply intervalIntegral.integral_nonneg ha.le
      intro s hs
      positivity
    have hqle : (∫ s in 0..a, q s) ≤ ∫ s in 0..t, q s := by
      calc
        (∫ s in 0..a, q s) ≤ (∫ s in 0..a, q s) + ∫ s in a..t, q s :=
          le_add_of_nonneg_right (intervalIntegral.integral_nonneg hlat.le (by
            intro s hs
            positivity))
        _ = ∫ s in 0..t, q s := hadd
    linarith [hba, hqle]
  have hRlim : Tendsto (fun a => F a + ∫ s in 0..t, q s)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (⟪v0, u0 - x⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2) +
        ∫ s in 0..t, q s)) := by
    have hconstlim : Tendsto (fun _ : ℝ => ∫ s in 0..t, q s)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ s in 0..t, q s)) := tendsto_const_nhds
    have hsum : Tendsto (fun a => F a + ∫ s in 0..t, q s)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (⟪v0, u0 - x⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - x‖ ^ 2) +
          ∫ s in 0..t, q s)) := hFright.add hconstlim
    simpa [add_assoc] using hsum
  have hfinal := ge_of_tendsto hRlim hevent
  simpa [F, p, q] using hfinal

/-- Proposition 2.5: the weak limit obeys the paper's projection estimate (2.10). -/
theorem projection_estimate_for_scalar_damped_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 uhat : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hgamma : 0 < gamma)
    (hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v0))
    (hhat : uhat ∈ argmin Phi (potential_range_bddBelow hPhi))
    (hWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) Filter.atTop
      (nhds (toWeakSpace ℝ H uhat)))
    (hS_cheb : IsChebyshev (argmin Phi (potential_range_bddBelow hPhi)))
    (x : H) (hx : x ∈ argmin Phi (potential_range_bddBelow hPhi)) :
    ‖uhat - x‖ ≤ ‖u0 + gamma⁻¹ • v0 - x‖ +
      gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ∧
    ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
        (u0 + gamma⁻¹ • v0)‖ ≤
      Metric.infDist (u0 + gamma⁻¹ • v0) (argmin Phi (potential_range_bddBelow hPhi)) +
        gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ∧
    ((∃ L : AffineSubspace ℝ H,
        (argmin Phi (potential_range_bddBelow hPhi) : Set H) = L) →
      ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0)‖ ≤
        gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))))) ∧
    ((∃ A : H →L[ℝ] H, IsSelfAdjoint A ∧ (∀ x : H, 0 ≤ ⟪A x, x⟫_ℝ) ∧
        (∀ x : H, Phi x = (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)) →
      Tendsto sys.u Filter.atTop
        (nhds (projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0)))) := by
  have hu0 := dissipativeSystem_tendsto_initial_position_right sys
  have hgap : 0 ≤ Phi u0 - sInf (Set.range Phi) :=
    sub_nonneg.mpr (potential_sInf_le hPhi u0)
  have hvelocity_integrable :
      IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    (scalar_damped_minimizing_property hPhi sys).1
  have henergy_from_zero : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) +
          gamma * (∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2) =
        (1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 := by
    intro t ht
    exact scalar_damped_energy_from_zero hPhi sys hvel0 ht
  have hprojection_step :
      (∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
        ‖uhat - z‖ ≤ ‖u0 + gamma⁻¹ • v0 - z‖ +
          gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) →
      ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0)‖ ≤
        Metric.infDist (u0 + gamma⁻¹ • v0) (argmin Phi (potential_range_bddBelow hPhi)) +
          gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
    intro hpointwise
    exact projection_metric_estimate_of_pointwise hS_cheb hpointwise
  have hscalar := scalar_damped_minimizing_property hPhi sys
  have hvelocity_zero : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) :=
    hscalar.2.1
  have hdistance_limit : ∃ l : ℝ,
      Tendsto (fun t => ‖sys.u t - x‖) atTop (nhds l) :=
    scalar_distance_to_minimizer_converges hPhi sys hvelocity_integrable x hx
  obtain ⟨distanceLimit, hdistanceLimit⟩ := hdistance_limit
  let p : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2
  have hpderiv_event : ∀ᶠ t in atTop,
      deriv p t = ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
      (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
    have hs := (hasDerivAt_const t (1 / 2 : ℝ)).mul (hu.sub_const x).norm_sq
    convert hs.deriv using 1 <;> simp [p, real_inner_comm]
  have hpderiv_zero : Tendsto (fun t => deriv p t) atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hdistanceLimit) 1 (by norm_num)
    let M : ℝ := |distanceLimit| + 1
    have hM : ∀ᶠ t in atTop, ‖sys.u t - x‖ ≤ M := by
      filter_upwards [eventually_ge_atTop N] with t ht
      have hdist := hN t ht
      rw [Real.dist_eq] at hdist
      have hlt : ‖sys.u t - x‖ < distanceLimit + 1 := by
        linarith [abs_lt.mp hdist |>.2]
      dsimp [M]
      linarith [le_abs_self distanceLimit]
    have hprod : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖ * M) atTop (nhds 0) := by
      simpa using hvelocity_zero.norm.mul_const M
    have habs : Tendsto (fun t => |deriv p t|) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun _ : ℝ => 0) (f := fun t => |deriv p t|)
        (h := fun t => ‖fderiv ℝ sys.u t 1‖ * M)
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) hprod ?_ ?_
      · filter_upwards [hpderiv_event] with t ht
        rw [ht]
        positivity
      · filter_upwards [hpderiv_event, hM] with t ht hMt
        rw [ht]
        exact (abs_real_inner_le_norm _ _).trans (by
          gcongr)
    have habs' : Tendsto (fun t => |deriv p t|) atTop (nhds 0) := habs
    have habs_norm : Tendsto (fun t => ‖deriv p t‖) atTop (nhds 0) := by
      simpa only [Real.norm_eq_abs] using habs'
    exact tendsto_zero_iff_norm_tendsto_zero.mpr habs_norm
  have hdist_integrated := scalar_damped_distance_integrated_bound hPhi sys hgamma hvel0 hx
    hvelocity_integrable
  have hq_bound : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      ∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2 ≤
        gamma⁻¹ * ((1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi)) := by
    intro t ht
    have henergy := henergy_from_zero ht
    have hpot := potential_sInf_le hPhi (sys.u t)
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by positivity
    have hqnonneg : 0 ≤ ∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2 := by
      apply intervalIntegral.integral_nonneg ht
      intro s hs
      positivity
    have hgamma' : 0 < gamma := hgamma
    have hmul : (∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2) * gamma ≤
        (1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi) := by
      linarith
    have hdiv := (le_div_iff₀ hgamma').2 hmul
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hpointwise : ∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
      ‖uhat - z‖ ≤ ‖u0 + gamma⁻¹ • v0 - z‖ +
        gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
    intro z hz
    have hdist_integrated_z := scalar_damped_distance_integrated_bound hPhi sys hgamma hvel0 hz
      hvelocity_integrable
    obtain ⟨lz, hlz⟩ := scalar_distance_to_minimizer_converges hPhi sys hvelocity_integrable z hz
    let pz : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u t - z‖ ^ 2
    have hpz_event : ∀ᶠ t in atTop,
        deriv pz t = ⟪fderiv ℝ sys.u t 1, sys.u t - z⟫_ℝ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
        (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
      convert ((hasDerivAt_const t (1 / 2 : ℝ)).mul (hu.sub_const z).norm_sq).deriv
        using 1 <;> simp [pz, real_inner_comm]
    have hpz_zero : Tendsto (fun t => deriv pz t) atTop (nhds 0) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlz) 1 (by norm_num)
      let M : ℝ := |lz| + 1
      have hM : ∀ᶠ t in atTop, ‖sys.u t - z‖ ≤ M := by
        filter_upwards [eventually_ge_atTop N] with t ht
        have hdist := hN t ht
        rw [Real.dist_eq] at hdist
        have hlt : ‖sys.u t - z‖ < lz + 1 := by
          linarith [abs_lt.mp hdist |>.2]
        dsimp [M]
        linarith [le_abs_self lz]
      have hprod : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖ * M) atTop (nhds 0) := by
        simpa using hvelocity_zero.norm.mul_const M
      have habs : Tendsto (fun t => |deriv pz t|) atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (g := fun _ : ℝ => 0) (f := fun t => |deriv pz t|)
          (h := fun t => ‖fderiv ℝ sys.u t 1‖ * M)
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) hprod ?_ ?_
        · filter_upwards [hpz_event] with t ht
          rw [ht]
          positivity
        · filter_upwards [hpz_event, hM] with t ht hMt
          rw [ht]
          exact (abs_real_inner_le_norm _ _).trans (by gcongr)
      have habs_norm : Tendsto (fun t => ‖deriv pz t‖) atTop (nhds 0) := by
        simpa only [Real.norm_eq_abs] using habs
      exact tendsto_zero_iff_norm_tendsto_zero.mpr habs_norm
    let K : ℝ := (1 / 2 : ℝ) * ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 +
      (gamma⁻¹) ^ 2 * (Phi u0 - sInf (Set.range Phi))
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hnorm_eps : ∀ ⦃ε : ℝ⦄, 0 < ε →
        ‖uhat - z‖ ≤ Real.sqrt (2 * (K + ε)) := by
      intro ε hε
      have hevent : ∀ᶠ t in atTop, pz t ≤ K + ε := by
        have hpze := hpz_zero.eventually (Metric.ball_mem_nhds 0 (by
          exact mul_pos hgamma hε))
        filter_upwards [eventually_gt_atTop (0 : ℝ), hpze] with t ht htp
        have hi := hdist_integrated_z ht
        have hq := hq_bound (le_of_lt ht)
        have hsmall : -deriv pz t ≤ gamma * ε := by
          have habs_le : |deriv pz t| < gamma * ε := by
            simpa [Metric.mem_ball, Real.dist_eq] using htp
          exact le_trans (neg_le_abs _) (le_of_lt habs_le)
        dsimp [pz, K] at *
        have hgam : 0 < gamma := hgamma
        have hginv : gamma * gamma⁻¹ = 1 := by
          field_simp
        have hy_sq : ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 =
            ‖u0 - z‖ ^ 2 + 2 * gamma⁻¹ * ⟪v0, u0 - z⟫_ℝ +
              gamma⁻¹ ^ 2 * ‖v0‖ ^ 2 := by
          have hrew : u0 + gamma⁻¹ • v0 - z =
              (u0 - z) + gamma⁻¹ • v0 := by abel
          rw [hrew, norm_add_sq_real, real_inner_smul_right, norm_smul]
          simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgamma)]
          rw [real_inner_comm]
          ring
        have hrewrite :
            ⟪v0, u0 - z⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - z‖ ^ 2) +
                gamma⁻¹ * ((1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi)) +
                gamma * ε =
              gamma * ((1 / 2 : ℝ) * ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 +
                gamma⁻¹ ^ 2 * (Phi u0 - sInf (Set.range Phi)) + ε) := by
          rw [hy_sq]
          have hgn : gamma ≠ 0 := ne_of_gt hgamma
          field_simp [hgn]
          ring
        nlinarith [hi, hq, hsmall, hrewrite]
      have hnorm_event : ∀ᶠ t in atTop, ‖sys.u t - z‖ ≤ Real.sqrt (2 * (K + ε)) := by
        filter_upwards [hevent] with t ht
        dsimp [pz] at ht
        have hnonneg : 0 ≤ ‖sys.u t - z‖ := norm_nonneg _
        have hsqrt : 0 ≤ Real.sqrt (2 * (K + ε)) := Real.sqrt_nonneg _
        have harg : 0 ≤ 2 * (K + ε) := by
          nlinarith [hKnonneg, hε]
        apply (Real.le_sqrt hnonneg harg).2
        have hsqrt_sq : (Real.sqrt (2 * (K + ε))) ^ 2 = 2 * (K + ε) :=
          Real.sq_sqrt harg
        nlinarith [ht, hsqrt_sq]
      exact weak_norm_sub_le_of_tendsto hWeak hnorm_event
    have hsqrt_lim : Tendsto (fun ε : ℝ => Real.sqrt (2 * (K + ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt (2 * K))) := by
      have harglim : Tendsto (fun ε : ℝ => 2 * (K + ε))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * K)) := by
        have hKlim : Tendsto (fun _ : ℝ => K)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds K) := tendsto_const_nhds
        have hidlim : Tendsto (fun ε : ℝ => ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        simpa [add_comm, add_left_comm, add_assoc] using (hKlim.add hidlim).const_mul 2
      exact Real.continuous_sqrt.continuousAt.tendsto.comp harglim
    have hsqK : Real.sqrt (2 * K) ≤
        ‖u0 + gamma⁻¹ • v0 - z‖ + gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · dsimp [K]
        have hgap' : 0 ≤ Phi u0 - sInf (Set.range Phi) := hgap
        have hsqrt : 0 ≤ Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := Real.sqrt_nonneg _
        have hsqroot : (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ^ 2 =
            2 * (Phi u0 - sInf (Set.range Phi)) := by
          exact Real.sq_sqrt (by positivity)
        have hgamma0 : 0 ≤ gamma⁻¹ := le_of_lt (inv_pos.mpr hgamma)
        nlinarith [sq_nonneg ‖u0 + gamma⁻¹ • v0 - z‖,
          mul_nonneg (norm_nonneg (u0 + gamma⁻¹ • v0 - z)) (mul_nonneg hgamma0 hsqrt)]
    have hsq_lim := ge_of_tendsto hsqrt_lim (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hnorm_eps hε)
    exact le_trans hsq_lim hsqK
  have hfirst := hpointwise x hx
  refine ⟨hfirst, hprojection_step hpointwise, ?_⟩
  constructor
  · intro hAffine
    rcases hAffine with ⟨L, hL⟩
    let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
    let y : H := u0 + gamma⁻¹ • v0
    let p : H := projectionPoint S hS_cheb y
    let e : H := uhat - p
    let d : ℝ := Metric.infDist y S
    let c : ℝ := gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))
    have hSclosed : IsClosed S := isClosed_of_isChebyshev hS_cheb
    have hLclosed : IsClosed (L : Set H) := by
      rw [← hL]
      exact hSclosed
    have hpS : p ∈ S := by
      exact projectionPoint_mem S hS_cheb y
    have hpL : p ∈ (L : Set H) := by
      rw [← hL]
      exact hpS
    have huL : uhat ∈ (L : Set H) := by
      rw [← hL]
      exact hhat
    have hLnonempty : (L : Set H).Nonempty := ⟨p, hpL⟩
    let hchebL : IsChebyshev (L : Set H) :=
      isChebyshev_of_nonempty_isClosed_convex hLnonempty hLclosed L.convex
    have hp_eq : p = projectionPoint (L : Set H) hchebL y := by
      simpa [p, S, hL] using
        (show projectionPoint S hS_cheb y = projectionPoint S hS_cheb y from rfl)
    have hchar :=
      (eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
        hLnonempty hLclosed (x := y) (p := p)).mp hp_eq
    have horth : ⟪e, y - p⟫_ℝ = 0 := by
      dsimp [e]
      simpa [e] using hchar.2 uhat huL p hpL
    have hbest : ‖y - p‖ = d := by
      have hb := (projectionPoint_isBestApproximation S hS_cheb y).2
      simpa [d, dist_eq_norm] using hb
    have hd : 0 ≤ d := by
      dsimp [d]
      exact Metric.infDist_nonneg
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    by_cases he_zero : e = 0
    · have hebound : ‖e‖ ≤ c := by rw [he_zero]; simp; exact hc
      simpa [e, p, S, y, c] using hebound
    · have he_ne : e ≠ 0 := he_zero
      have he_norm : 0 < ‖e‖ := norm_pos_iff.mpr he_ne
      have he_dir : e ∈ L.direction := by
        dsimp [e]
        simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction huL hpL
      have hunit_norm : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he_norm)]
        field_simp
      have hunit_vec : ‖e‖ • (‖e‖⁻¹ • e) = e := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt he_norm), one_smul]
      have hxr : ∀ r : ℝ, p - (r * d) • (‖e‖⁻¹ • e) ∈ S := by
        intro r
        have hscaled : -(r * d) • (‖e‖⁻¹ • e) ∈ L.direction := by
          apply L.direction.smul_mem
          apply L.direction.smul_mem
          exact he_dir
        have hvadd := AffineSubspace.vadd_mem_of_mem_direction hscaled hpL
        dsimp [S]
        rw [hL]
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hvadd
      have hnorm_y : ∀ r : ℝ, ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ =
          Real.sqrt (1 + r ^ 2) * d := by
        intro r
        have hcross : ⟪y - p, (r * d) • (‖e‖⁻¹ • e)⟫_ℝ = 0 := by
          rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
          rw [horth]
          ring
        have hsq : ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ ^ 2 =
            d ^ 2 + (r * d) ^ 2 := by
          have hrewrite : y - (p - (r * d) • (‖e‖⁻¹ • e)) =
              (y - p) + (r * d) • (‖e‖⁻¹ • e) := by abel
          rw [hrewrite, norm_add_sq_real, hcross, norm_smul, hunit_norm]
          rw [hbest]
          simp only [mul_one]
          have hnorm_sq : ‖r * d‖ ^ 2 = (r * d) ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
          rw [hnorm_sq]
          ring
        have hsqrt : 0 ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_nonneg _
        have harg : 0 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
        have hsqrt_sq := Real.sq_sqrt harg
        have hright : 0 ≤ Real.sqrt (1 + r ^ 2) * d := mul_nonneg hsqrt hd
        have hleft : 0 ≤ ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ := norm_nonneg _
        nlinarith
      have hnorm_e : ∀ r : ℝ, 0 ≤ r →
          ‖uhat - (p - (r * d) • (‖e‖⁻¹ • e))‖ = ‖e‖ + r * d := by
        intro r hr
        have hrewrite : uhat - (p - (r * d) • (‖e‖⁻¹ • e)) =
            (‖e‖ + r * d) • (‖e‖⁻¹ • e) := by
          rw [add_smul, hunit_vec]
          dsimp [e]
          abel
        rw [hrewrite, norm_smul, hunit_norm]
        have : 0 ≤ ‖e‖ + r * d := by
          positivity
        rw [Real.norm_eq_abs, abs_of_nonneg this]
        ring
      have hray : ∀ r : ℝ, 0 ≤ r →
          ‖e‖ ≤ (Real.sqrt (1 + r ^ 2) - r) * d + c := by
        intro r hr
        have hp' := hpointwise (p - (r * d) • (‖e‖⁻¹ • e))
          (by simpa [S] using hxr r)
        have hp'' : ‖uhat - (p - (r * d) • (‖e‖⁻¹ • e))‖ ≤
            ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ + c := by
          simpa [y, c] using hp'
        rw [hnorm_e r hr, hnorm_y r] at hp''
        linarith
      have hden_tendsto : Tendsto (fun n : ℕ =>
          Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) atTop atTop := by
        apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
        nlinarith [Real.sqrt_nonneg (1 + (n : ℝ) ^ 2)]
      have hfactor : Tendsto (fun n : ℕ =>
          Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) atTop (nhds 0) := by
        have hinv := tendsto_inv_atTop_zero.comp hden_tendsto
        apply hinv.congr'
        filter_upwards with n
        have hsq := Real.sq_sqrt (show 0 ≤ 1 + (n : ℝ) ^ 2 by positivity)
        have hden : Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ) ≠ 0 := by
          nlinarith [Real.sqrt_nonneg (1 + (n : ℝ) ^ 2)]
        have hidentity :
            (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))⁻¹ =
              Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) := by
          calc
            (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))⁻¹ =
                1 / (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) := by rw [one_div]
            _ = Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) := by
              apply (div_eq_iff hden).2
              nlinarith
        simpa only [Function.comp_apply] using hidentity
      have hterm : Tendsto (fun n : ℕ =>
          (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d) atTop (nhds 0) := by
        simpa only [zero_mul] using hfactor.mul_const d
      have hlim : Tendsto (fun n : ℕ =>
          (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d + c) atTop (nhds c) := by
        simpa using hterm.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
      have hev : ∀ᶠ n : ℕ in atTop,
          ‖e‖ ≤ (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d + c := by
        filter_upwards [Filter.Eventually.of_forall (fun n => hray n (by positivity))] with n hn
        simpa using hn
      have hebound : ‖e‖ ≤ c := ge_of_tendsto hlim hev
      simpa [e, p, S, y, c] using hebound
  · intro hQuadratic
    rcases hQuadratic with ⟨A, hAself, hApos, hPhiA⟩
    have hquad := quadratic_scalar_damped_tendsto_weak_limit hPhi sys hhat hWeak A hPhiA
    have hgradA : ∀ q : H, gradPhi q = A q := by
      intro q
      have hqstrict := hAself.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf q
      have hqscaled := hqstrict.const_mul (1 / 2 : ℝ)
      have hqderiv : HasFDerivAt (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
          (innerSL ℝ (A q)) q := by
        have hs : HasStrictFDerivAt (fun x : H =>
            (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
            ((1 / 2 : ℝ) • (2 • (innerSL ℝ) (A q))) q := by
          simpa [ContinuousLinearMap.reApplyInnerSelf] using hqscaled
        convert hs.hasFDerivAt using 1
        ext v
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        norm_num
        ring
      have hg : HasFDerivAt (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
          (InnerProductSpace.toDual ℝ H (gradPhi q)) q := by
        have hfun : Phi = (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ) :=
          funext hPhiA
        rw [← hfun]
        exact (sys.is_gradient q).hasFDerivAt
      have hdual := hg.unique hqderiv
      apply (InnerProductSpace.toDual ℝ H).injective
      ext y
      simpa [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
        congrArg (fun f => f y) hdual
    have hAzero : ∀ z : H, z ∈ argmin Phi (potential_range_bddBelow hPhi) → A z = 0 := by
      intro z hz
      have hmin : IsMinOn Phi Set.univ z := by
        intro y hy
        rw [show Phi z = sInf (Set.range Phi) from hz]
        exact potential_sInf_le hPhi y
      have hfderiv : fderiv ℝ Phi z = 0 :=
        (hmin.isLocalMin (by simp : Set.univ ∈ nhds z)).fderiv_eq_zero
      have hgradzero : gradPhi z = 0 := by
        have hinner : ⟪gradPhi z, gradPhi z⟫_ℝ = 0 := by
          rw [← (sys.is_gradient z).fderiv_apply, hfderiv]
          simp
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp
          (by simpa only [real_inner_self_eq_norm_sq] using hinner))
      rw [← hgradA z]
      exact hgradzero
    let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
    let y : H := u0 + gamma⁻¹ • v0
    have hSclosed : IsClosed S := isClosed_of_isChebyshev hS_cheb
    have hSconv : Convex ℝ S := by
      intro a ha b hb α β hα hβ hab
      change Phi (α • a + β • b) = sInf (Set.range Phi)
      change Phi a = sInf (Set.range Phi) at ha
      change Phi b = sInf (Set.range Phi) at hb
      have hle := hPhi.convex.2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hab
      rw [ha, hb] at hle
      apply le_antisymm
      · calc
          Phi (α • a + β • b) ≤ α * sInf (Set.range Phi) + β * sInf (Set.range Phi) := hle
          _ = sInf (Set.range Phi) := by rw [← add_mul, hab, one_mul]
      · exact potential_sInf_le hPhi _
    have horth_proj : ∀ z : H, z ∈ S →
        ⟪uhat - y, z⟫_ℝ = 0 := by
      intro z hz
      let hgfun : ℝ → ℝ := fun t =>
        ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ + gamma * ⟪sys.u t - u0, z⟫_ℝ
      have hg_deriv : ∀ ⦃t : ℝ⦄, 0 < t →
          HasDerivAt hgfun
            (⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, z⟫_ℝ +
              gamma * ⟪fderiv ℝ sys.u t 1, z⟫_ℝ) t := by
        intro t ht
        have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
          (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
        have hv : HasDerivAt (fun s => fderiv ℝ sys.u s 1)
            (fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1) t :=
          dissipativeSystem_velocity_hasDerivAt_pos sys ht
        have h1 := (hv.sub_const v0).inner ℝ (hasDerivAt_const t z)
        have h2 := (hu.sub_const u0).inner ℝ (hasDerivAt_const t z)
        have hsum := h1.add ((hasDerivAt_const t gamma).mul h2)
        simpa [hgfun] using hsum
      have hg_zero_deriv : ∀ ⦃t : ℝ⦄, 0 < t → deriv hgfun t = 0 := by
        intro t ht
        have heq := sys.equation t (le_of_lt ht)
        have hinner := congrArg (fun w : H => ⟪w, z⟫_ℝ) heq
        have hAz := hAzero z hz
        have horth : ⟪gradPhi (sys.u t), z⟫_ℝ = 0 := by
          calc
            ⟪gradPhi (sys.u t), z⟫_ℝ = ⟪A (sys.u t), z⟫_ℝ := by rw [hgradA]
            _ = ⟪sys.u t, A z⟫_ℝ := hAself.isSymmetric _ _
            _ = 0 := by rw [hAz]; simp
        rw [(hg_deriv ht).deriv]
        have hinner' :
            ⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, z⟫_ℝ +
              gamma * ⟪fderiv ℝ sys.u t 1, z⟫_ℝ +
              ⟪gradPhi (sys.u t), z⟫_ℝ = 0 := by
          simpa [inner_add_left, inner_smul_left] using hinner
        linarith
      have hg_diff : DifferentiableOn ℝ hgfun (Set.Ioi 0) := by
        intro t ht
        exact (hg_deriv ht).differentiableAt.differentiableWithinAt
      have hg_fderiv_zero : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioi 0 →
          fderivWithin ℝ hgfun (Set.Ioi 0) t = 0 := by
        intro t ht
        rw [fderivWithin_of_isOpen isOpen_Ioi ht]
        rw [← toSpanSingleton_deriv]
        simp [hg_zero_deriv ht]
      have hg_const : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioi 0 → b ∈ Set.Ioi 0 →
          hgfun a = hgfun b := by
        intro a b ha hb
        exact (convex_Ioi (0 : ℝ)).is_const_of_fderivWithin_eq_zero
          hg_diff hg_fderiv_zero ha hb
      have hg_right : Tendsto hgfun (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hvlim : Tendsto (fun t => fderiv ℝ sys.u t 1 - v0)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : H)) := by
          simpa using hvel0.sub (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => v0) (nhdsWithin 0 (Set.Ioi 0)) (nhds v0))
        have hulim : Tendsto (fun t => sys.u t - u0)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : H)) := by
          simpa using hu0.sub (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => u0) (nhdsWithin 0 (Set.Ioi 0)) (nhds u0))
        have h1 : Tendsto (fun t : ℝ =>
            ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          simpa using Filter.Tendsto.inner (𝕜 := ℝ) hvlim (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds z))
        have h2 : Tendsto (fun t : ℝ =>
            ⟪sys.u t - u0, z⟫_ℝ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          simpa using Filter.Tendsto.inner (𝕜 := ℝ) hulim (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds z))
        have hsum := h1.add ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => gamma) (nhdsWithin 0 (Set.Ioi 0)) (nhds gamma)).mul h2)
        simpa [hgfun] using hsum
      have hg_zero : ∀ t : ℝ, 0 < t → hgfun t = 0 := by
        intro t ht
        have hev : ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0), hgfun a = hgfun t := by
          filter_upwards [self_mem_nhdsWithin] with a ha
          exact hg_const ha ht
        have hlim : Tendsto (fun _ : ℝ => hgfun t)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hg_right.congr' hev
        exact tendsto_nhds_unique tendsto_const_nhds hlim
      have hconst : Tendsto hgfun atTop (nhds 0) := by
        apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)).congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        exact (hg_zero t ht).symm
      have hvweak := hvel0
      have hv_atTop : Tendsto (fun t => fderiv ℝ sys.u t 1 - v0)
          atTop (nhds (-v0)) := by
        simpa using hvelocity_zero.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => v0) atTop (nhds v0))
      have huweak : Tendsto (fun t => ⟪sys.u t - u0, z⟫_ℝ)
          atTop (nhds ⟪uhat - u0, z⟫_ℝ) := by
        have hw := (weakSpace_continuous_inner_right z).tendsto
          (toWeakSpace ℝ H uhat) |>.comp hWeak
        simpa [inner_sub_right, real_inner_comm] using hw.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => ⟪u0, z⟫_ℝ) atTop (nhds ⟪u0, z⟫_ℝ))
      have hvinner : Tendsto
          (fun t : ℝ => ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ)
          atTop (nhds ⟪-v0, z⟫_ℝ) := by
        exact Filter.Tendsto.inner (𝕜 := ℝ) hv_atTop
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) atTop (nhds z))
      have hglim := hvinner.add ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => gamma) atTop (nhds gamma)).mul huweak)
      have hglim' : Tendsto hgfun atTop
          (nhds (⟪-v0, z⟫_ℝ + gamma * ⟪uhat - u0, z⟫_ℝ)) := by
        simpa [hgfun] using hglim
      have hzero_eq := tendsto_nhds_unique hconst hglim'
      rw [sub_eq_add_neg, inner_add_left, real_inner_comm] at hzero_eq
      rw [inner_neg_right, inner_neg_left] at hzero_eq
      have hzero_eq' : gamma * (⟪uhat, z⟫_ℝ - ⟪u0, z⟫_ℝ) = ⟪v0, z⟫_ℝ := by
        have hzero_eq'' : 0 = -⟪v0, z⟫_ℝ +
            gamma * (⟪uhat, z⟫_ℝ - ⟪u0, z⟫_ℝ) := by
          simpa [real_inner_comm] using hzero_eq
        linarith [hzero_eq'']
      dsimp [y]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      field_simp [hgamma.ne']
      nlinarith [hzero_eq']
    have hproj : uhat = projectionPoint S hS_cheb y := by
      apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hS_cheb hSconv).mpr
      refine ⟨hhat, ?_⟩
      intro z hz
      have hzorth := horth_proj z hz
      have huorth := horth_proj uhat hhat
      have hz' : ⟪z, y⟫_ℝ - ⟪z, uhat⟫_ℝ = 0 := by
        have hz'' : ⟪uhat, z⟫_ℝ - ⟪z, y⟫_ℝ = 0 := by
          simpa [inner_sub_left, real_inner_comm] using hzorth
        have hcomm : ⟪uhat, z⟫_ℝ = ⟪z, uhat⟫_ℝ := real_inner_comm _ _
        linarith
      have hu' : ⟪uhat, y⟫_ℝ - ⟪uhat, uhat⟫_ℝ = 0 := by
        have hu'' : ‖uhat‖ ^ 2 - ⟪uhat, y⟫_ℝ = 0 := by
          simpa [inner_sub_left, real_inner_comm] using huorth
        nlinarith [real_inner_self_eq_norm_sq uhat]
      have hzero : ⟪z - uhat, y - uhat⟫_ℝ = 0 := by
        simp only [inner_sub_left, inner_sub_right]
        nlinarith [hz', hu']
      exact hzero.le
    simpa [hproj, S, y] using hquad

end Alvarez2000
