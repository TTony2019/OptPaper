import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.lem_8
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.lem_9
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.lem_5
import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory Filter

private theorem prop212_integrableOn_Ici_of_nonneg_interval_bound
    {g : ℝ → ℝ} {a C : ℝ}
    (hlocal : ∀ T, IntegrableOn g (Set.Ioc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s)
    (hbound : ∀ T, a ≤ T → ∫ s in a..T, g s ≤ C) :
    IntegrableOn g (Set.Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded C a hlocal
    Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop a] with T hT
  have hnorm : (∫ s in a..T, ‖g s‖) = ∫ s in a..T, g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hT] at hs
    exact Real.norm_of_nonneg (hnonneg s hs.1.le)
  rw [hnorm]
  exact hbound T hT

private theorem prop212_sqdist_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H} {a b : ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b) (z : H) :
    AbsolutelyContinuousOnInterval (fun t => (1 / 2 : ℝ) * ‖x t - z‖ ^ 2) a b := by
  have hsub : AbsolutelyContinuousOnInterval (fun t => x t - z) a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
      contDiffOn_const.absolutelyContinuousOnInterval
    exact hx.sub hconst
  have hnorm : AbsolutelyContinuousOnInterval (fun t => ‖x t - z‖) a b := by
    rw [absolutelyContinuousOnInterval_iff] at hsub ⊢
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hsub ε hε
    refine ⟨δ, hδ, ?_⟩
    intro E hE hsum
    refine lt_of_le_of_lt ?_ (hbound _ hE hsum)
    apply Finset.sum_le_sum
    intro i hi
    simpa [Real.norm_eq_abs, dist_eq_norm] using
      (abs_norm_sub_norm_le (x (E.2 i).1 - z) (x (E.2 i).2 - z))
  have hsq : AbsolutelyContinuousOnInterval
      (fun t => ‖x t - z‖ * ‖x t - z‖) a b := hnorm.mul hnorm
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq.const_mul (1 / 2 : ℝ)

private theorem prop212_inner_const_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H} {a b : ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b) (z : H) :
    AbsolutelyContinuousOnInterval (fun t => inner ℝ z (x t)) a b := by
  have hinner : AbsolutelyContinuousOnInterval (fun t => inner ℝ (x t) z) a b := by
    unfold AbsolutelyContinuousOnInterval at hx ⊢
    apply squeeze_zero (fun E => ?_) (fun E => ?_)
      (by simpa using hx.const_mul ‖z‖)
    · exact Finset.sum_nonneg fun _ _ => dist_nonneg
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.dist_eq, ← inner_sub_left]
      calc
        |inner ℝ (x (E.2 i).1 - x (E.2 i).2) z| ≤
            ‖x (E.2 i).1 - x (E.2 i).2‖ * ‖z‖ := abs_real_inner_le_norm _ _
        _ = ‖z‖ * dist (x (E.2 i).1) (x (E.2 i).2) := by
          rw [dist_eq_norm_sub, mul_comm]
  simpa only [real_inner_comm] using hinner

private theorem prop212_inner_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : ℝ → H} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => inner ℝ (f t) (g t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using (hg.const_mul C).add (hf.const_mul D))
  · exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  · rw [Filter.eventually_inf_principal]
    filter_upwards with E hE
    simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_setOf_eq] at hE
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hleft := hE.left i hi
    rw [Real.dist_eq]
    calc
      |inner ℝ (f (E.2 i).1) (g (E.2 i).1) -
          inner ℝ (f (E.2 i).2) (g (E.2 i).2)| =
          |inner ℝ (f (E.2 i).1) (g (E.2 i).1 - g (E.2 i).2) +
            inner ℝ (f (E.2 i).1 - f (E.2 i).2) (g (E.2 i).2)| := by
          congr 1
          rw [inner_sub_right, inner_sub_left]
          ring
      _ ≤ |inner ℝ (f (E.2 i).1) (g (E.2 i).1 - g (E.2 i).2)| +
          |inner ℝ (f (E.2 i).1 - f (E.2 i).2) (g (E.2 i).2)| := abs_add_le _ _
      _ ≤ C * dist (g (E.2 i).1) (g (E.2 i).2) +
          D * dist (f (E.2 i).1) (f (E.2 i).2) := by
        gcongr
        · calc
            |inner ℝ (f (E.2 i).1) (g (E.2 i).1 - g (E.2 i).2)| ≤
                ‖f (E.2 i).1‖ * ‖g (E.2 i).1 - g (E.2 i).2‖ :=
              abs_real_inner_le_norm _ _
            _ ≤ C * dist (g (E.2 i).1) (g (E.2 i).2) := by
              rw [dist_eq_norm_sub]
              exact mul_le_mul_of_nonneg_right (hC _ hleft.left) (norm_nonneg _)
        · calc
            |inner ℝ (f (E.2 i).1 - f (E.2 i).2) (g (E.2 i).2)| ≤
                ‖f (E.2 i).1 - f (E.2 i).2‖ * ‖g (E.2 i).2‖ :=
              abs_real_inner_le_norm _ _
            _ ≤ D * dist (f (E.2 i).1) (f (E.2 i).2) := by
              rw [dist_eq_norm_sub, mul_comm]
              exact mul_le_mul_of_nonneg_right (hD _ hleft.right) (norm_nonneg _)
    

private theorem prop212_orbit_inner_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam mu : ℝ) (hmu_lam : mu * lam = 1) (a dx dv q : H)
    (horb : lam • dx + dv + q = 0) :
    inner ℝ a dx + mu * inner ℝ a (dv + q) = 0 := by
  have hs := congrArg (fun y : H => inner ℝ a y) horb
  have hs' : lam * inner ℝ a dx + (inner ℝ a dv + inner ℝ a q) = 0 := by
    dsimp only at hs
    rw [inner_add_right, inner_add_right] at hs
    rw [real_inner_smul_right] at hs
    simpa [add_assoc] using hs
  rw [inner_add_right]
  calc
    inner ℝ a dx + mu * (inner ℝ a dv + inner ℝ a q) =
        (mu * lam) * inner ℝ a dx + mu * (inner ℝ a dv + inner ℝ a q) := by
          rw [hmu_lam]
          ring
    _ = mu * (lam * inner ℝ a dx + (inner ℝ a dv + inner ℝ a q)) := by ring
    _ = 0 := by rw [hs', mul_zero]

private theorem prop212_inner_deriv_nonneg_of_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} {x v dx dv : ℝ → H}
    (hT : T.IsMonotone) (hmem : ∀ s : ℝ, 0 ≤ s → v s ∈ T (x s))
    {t : ℝ} (ht : 0 < t) (hxd : HasDerivAt x (dx t) t)
    (hvd : HasDerivAt v (dv t) t) : 0 ≤ inner ℝ (dx t) (dv t) := by
  let qx : ℝ → H := fun h => h⁻¹ • (x (t + h) - x t)
  let qv : ℝ → H := fun h => h⁻¹ • (v (t + h) - v t)
  have hqx : Filter.Tendsto qx (nhdsWithin 0 {0}ᶜ) (nhds (dx t)) :=
    hxd.tendsto_slope_zero
  have hqv : Filter.Tendsto qv (nhdsWithin 0 {0}ᶜ) (nhds (dv t)) :=
    hvd.tendsto_slope_zero
  have hlim : Filter.Tendsto (fun h => inner ℝ (qx h) (qv h))
      (nhdsWithin 0 {0}ᶜ) (nhds (inner ℝ (dx t) (dv t))) := hqx.inner hqv
  rw [← neg_nonpos]
  apply le_of_tendsto hlim.neg
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ⟨t, ht, ?_⟩
  intro h hh hne
  have hth : 0 ≤ t + h := by
    rw [Real.dist_eq] at hh
    nlinarith [abs_lt.mp hh]
  have hmono := hT (v (t + h)) (hmem (t + h) hth) (v t) (hmem t ht.le)
  dsimp only [qx, qv]
  rw [real_inner_smul_left, inner_smul_right]
  have hrewrite : h⁻¹ * (h⁻¹ * inner ℝ (x (t + h) - x t) (v (t + h) - v t)) =
      (h⁻¹ * h⁻¹) * inner ℝ (v (t + h) - v t) (x (t + h) - x t) := by
    rw [real_inner_comm]
    ring
  rw [hrewrite]
  exact neg_nonpos.mpr (mul_nonneg (mul_self_nonneg _) hmono)

private theorem prop212_dissipation_on_Ici
    {F q : ℝ → ℝ} {L : ℝ}
    (hF_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval F 0 T)
    (hq_local : ∀ T, 0 < T → IntegrableOn q (Set.Ioc 0 T))
    (hq_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hF_lower : ∀ t, 0 ≤ t → L ≤ F t)
    (hderiv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), deriv F t + q t ≤ 0) :
    AntitoneOn F (Set.Ici 0) ∧ (∃ l, Tendsto F atTop (nhds l)) ∧
      IntegrableOn q (Set.Ici 0) := by
  have hanti : AntitoneOn F (Set.Ici 0) := by
    intro s hs t ht hst
    by_cases hzero : t = 0
    · subst t
      have hs0 : s = 0 := le_antisymm hst hs
      subst s
      rfl
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hac : AbsolutelyContinuousOnInterval F s t :=
      (hF_ac t htpos).mono (by
        rw [Set.uIcc_of_le hst, Set.uIcc_of_le (show 0 ≤ t from ht)]
        exact Set.Icc_subset_Icc hs le_rfl)
    have hderiv' : ∀ᵐ u ∂volume.restrict (Set.Icc s t), deriv F u ≤ 0 := by
      filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc s t ⊆ Set.Icc 0 t from Set.Icc_subset_Icc hs le_rfl)
        (hderiv t htpos), ae_restrict_mem measurableSet_Icc] with u hu humem
      have hqu : 0 ≤ q u := hq_nonneg u (le_trans hs humem.1)
      linarith
    have hint := intervalIntegral.integral_mono_ae_restrict hst
      hac.intervalIntegrable_deriv intervalIntegrable_const hderiv'
    rw [intervalIntegral.integral_const, smul_zero] at hint
    rw [hac.integral_deriv_eq_sub] at hint
    linarith
  have hq_bound : ∀ T, 0 < T → (∫ s in 0..T, q s) ≤ F 0 - L := by
    intro T hT
    have hqint : IntervalIntegrable q volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hq_local T hT)
    have hFint : IntervalIntegrable (fun s => -deriv F s) volume 0 T :=
      (hF_ac T hT).intervalIntegrable_deriv.neg
    have hpoint : ∀ᵐ s ∂volume.restrict (Set.Icc 0 T),
        q s ≤ -deriv F s := by
      filter_upwards [hderiv T hT] with s hs
      linarith
    have hint := intervalIntegral.integral_mono_ae_restrict hT.le hqint hFint hpoint
    rw [intervalIntegral.integral_neg] at hint
    rw [(hF_ac T hT).integral_deriv_eq_sub] at hint
    have hlow : L ≤ F T := hF_lower T hT.le
    linarith
  have hqint : IntegrableOn q (Set.Ici 0) := by
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound (C := F 0 - L)
      (hlocal := fun T => by
        by_cases hT : 0 < T
        · exact hq_local T hT
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty)
      (hnonneg := hq_nonneg)
    intro T hT
    rcases hT.eq_or_lt with rfl | hT
    · have hC : 0 ≤ F 0 - L := by linarith [hF_lower 0 le_rfl]
      simpa using hC
    · exact hq_bound T hT
  have hGanti : Antitone (fun t => F (max t 0)) := by
    intro s t hst
    exact hanti (le_max_right s 0) (le_max_right t 0)
      (max_le_max_right 0 hst)
  have hGbelow : BddBelow (Set.range (fun t => F (max t 0))) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hF_lower _ (le_max_right t 0)
  refine ⟨hanti, ?_, hqint⟩
  refine ⟨⨅ t, F (max t 0), ?_⟩
  apply (tendsto_atTop_ciInf hGanti hGbelow).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [max_eq_left ht]

private theorem prop212_augmented_dissipation_algebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam mu beta dGamma dPhi dInner : ℝ) (dx dv vv bx bz : H)
    (hmu_lam : mu * lam = 1) (hbeta : 0 ≤ beta)
    (hinner : 0 ≤ inner ℝ dx dv)
    (horbit : lam • dx + dv + vv + bx = 0)
    (hphi : dPhi = inner ℝ dx vv)
    (hinnerB : dInner = inner ℝ dx bz)
    (hgamma : dGamma + mu * beta * ‖bx - bz‖ ^ 2 ≤ 0) :
    dGamma + 2 * beta * (dPhi + dInner) + beta * lam * ‖dx‖ ^ 2 +
        mu * beta * ‖dv + vv + bz‖ ^ 2 ≤ 0 := by
  let r : H := dv + vv + bz
  have hzero : (lam • dx + dv + vv) + bx = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using horbit
  have hbx : bx = -(lam • dx + dv + vv) := eq_neg_of_add_eq_zero_right hzero
  have hres : bx - bz = -(lam • dx + r) := by
    dsimp [r]
    rw [hbx]
    abel
  have hexpand : ‖bx - bz‖ ^ 2 = lam ^ 2 * ‖dx‖ ^ 2 +
      2 * lam * inner ℝ dx r + ‖r‖ ^ 2 := by
    rw [hres, norm_neg, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left]
    rw [mul_pow, sq_abs]
    ring
  have hlsq : mu * beta * lam ^ 2 = beta * lam := by
    calc
      mu * beta * lam ^ 2 = beta * (mu * lam) * lam := by ring
      _ = beta * lam := by rw [hmu_lam]; ring
  have hcross : 2 * mu * beta * lam * inner ℝ dx r =
      2 * beta * inner ℝ dx dv +
        2 * beta * (inner ℝ dx vv + inner ℝ dx bz) := by
    dsimp [r]
    rw [inner_add_right, inner_add_right]
    calc
      2 * mu * beta * lam * (inner ℝ dx dv + inner ℝ dx vv + inner ℝ dx bz) =
          2 * beta * (mu * lam) * (inner ℝ dx dv + inner ℝ dx vv + inner ℝ dx bz) := by ring
      _ = 2 * beta * inner ℝ dx dv +
          2 * beta * (inner ℝ dx vv + inner ℝ dx bz) := by rw [hmu_lam]; ring
  have hmain : dGamma + 2 * beta * (dPhi + dInner) + beta * lam * ‖dx‖ ^ 2 +
      mu * beta * ‖r‖ ^ 2 =
      dGamma + mu * beta * ‖bx - bz‖ ^ 2 - 2 * beta * inner ℝ dx dv := by
    rw [hexpand, hphi, hinnerB]
    calc
      dGamma + 2 * beta * (inner ℝ dx vv + inner ℝ dx bz) +
          beta * lam * ‖dx‖ ^ 2 + mu * beta * ‖r‖ ^ 2 =
          dGamma + beta * lam * ‖dx‖ ^ 2 +
            2 * mu * beta * lam * inner ℝ dx r + mu * beta * ‖r‖ ^ 2 -
            2 * beta * inner ℝ dx dv := by rw [hcross]; ring
      _ = dGamma + mu * beta * (lam ^ 2 * ‖dx‖ ^ 2 +
            2 * lam * inner ℝ dx r + ‖r‖ ^ 2) -
            2 * beta * inner ℝ dx dv := by
              rw [← hlsq]
              ring
  rw [hmain]
  have hnonneg : 0 ≤ 2 * beta * inner ℝ dx dv :=
    mul_nonneg (mul_nonneg (by positivity) hbeta) hinner
  linarith

set_option maxHeartbeats 1000000 in
-- This proof needs a large heartbeat budget for its inequality chains.
private theorem prop212_residual_endpoint_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {v r : ℝ → H} {b : H} {T : ℝ} (hT : 0 < T)
    (hv_ac : AbsolutelyContinuousOnInterval v 0 T)
    (hv_deriv : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      HasDerivAt v (deriv v t) t)
    (hderivv_sq : IntegrableOn (fun t ↦ ‖deriv v t‖ ^ 2) (Set.Icc 0 T))
    (hr_sq : IntegrableOn (fun t ↦ ‖r t‖ ^ 2) (Set.Icc 0 T))
    (hr_eq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      r t = deriv v t + v t + b) :
    (∫ t in (0 : ℝ)..T, ‖deriv v t‖ ^ 2) + ‖v T + b‖ ^ 2 ≤
      (∫ t in (0 : ℝ)..T, ‖r t‖ ^ 2) + ‖v 0 + b‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖v t - (-b)‖ ^ 2
  have hF_ac : AbsolutelyContinuousOnInterval F 0 T := by
    simpa [F] using prop212_sqdist_absolutelyContinuousOnInterval hv_ac (-b)
  have hdv_int : IntervalIntegrable (fun t => ‖deriv v t‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (hderivv_sq.mono_set Set.Ioc_subset_Icc_self)
  have hr_int : IntervalIntegrable (fun t => ‖r t‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (hr_sq.mono_set Set.Ioc_subset_Icc_self)
  have hF_int : IntervalIntegrable (deriv F) volume 0 T :=
    hF_ac.intervalIntegrable_deriv
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      ‖deriv v t‖ ^ 2 + 2 * deriv F t ≤ ‖r t‖ ^ 2 := by
    filter_upwards [hv_deriv, hr_eq, ae_restrict_mem measurableSet_Icc] with t hvt hrt ht
    have hF' : HasDerivAt F (inner ℝ (v t + b) (deriv v t)) t := by
      have h := ((hvt.sub_const (-b)).norm_sq.const_mul (1 / 2 : ℝ))
      simpa [F, sub_eq_add_neg, neg_neg, one_div, real_inner_comm] using h
    rw [hF'.deriv]
    rw [hrt, show deriv v t + v t + b = deriv v t + (v t + b) by abel,
      norm_add_sq_real]
    rw [real_inner_comm]
    nlinarith [sq_nonneg ‖v t + b‖]
  have hleft : IntervalIntegrable (fun t => ‖deriv v t‖ ^ 2 + 2 * deriv F t)
      volume 0 T := hdv_int.add (hF_int.const_mul 2)
  have hint := intervalIntegral.integral_mono_ae_restrict hT.le hleft hr_int hpoint
  rw [intervalIntegral.integral_add hdv_int (hF_int.const_mul 2),
    intervalIntegral.integral_const_mul] at hint
  rw [hF_ac.integral_deriv_eq_sub] at hint
  dsimp [F] at hint
  have hnormT : ‖v T - -b‖ ^ 2 = ‖v T + b‖ ^ 2 := by congr 1; abel_nf
  have hnorm0 : ‖v 0 - -b‖ ^ 2 = ‖v 0 + b‖ ^ 2 := by congr 1; abel_nf
  nlinarith [hint, hnormT, hnorm0]

set_option maxHeartbeats 1000000 in
-- This proof needs a large heartbeat budget for its inequality chains.
/-- Proposition 2.12: Lyapunov monotonicity and its seven consequences for an orbit. -/
theorem proposition_2_12 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (_ : S.Nonempty) (hz : z ∈ S)
    (hlam : 0 < lam) (hmu : 0 < mu) (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi) :
    AntitoneOn (fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))) (Set.Ici 0) ∧
    (∃ l, Tendsto (fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))) atTop (nhds l)) ∧
    Integrable (fun t ↦ ‖B (x t) - B z‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ C) ∧
    Integrable (fun t ↦ ‖deriv x t‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    Integrable (fun t ↦ ‖deriv v t + v t + B z‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    Integrable (fun t ↦ ‖deriv v t‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → ‖v t‖ ≤ C) ∧
    ∃ l, Tendsto (fun t ↦ (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop (nhds l) := by
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := hsolution z hz
  have hzdom : z ∈ ERealFunction.effectiveDomain Phi := hdom.2 z hz
  have hgap_nonneg : ∀ t, 0 ≤ t →
      0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t) := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) hzdom
    rw [real_inner_comm] at hineq
    linarith
  have hphi_chain : ∀ T, 0 < T →
      AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (Phi (x s) : EReal).toReal) t =
          inner ℝ (v t) (deriv x t) := by
    intro T hT
    apply subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hsubgradient t ht.1
    · intro t ht
      exact hdom.1 t ht.1
    · exact hx_deriv T hT
    · exact hvL2 T hT
    · exact hdxL2 T hT
  have hlyap : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
          mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
            inner ℝ (z - x s) (v s))) t +
          mu * beta * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hderiv_inner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hmonoSub : SetValuedOperator.IsMonotone
          (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
        ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      have htemp : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hv_deriv T hT), ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop212_inner_deriv_nonneg_of_monotone hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at htemp
      exact htemp
    have horbT : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        v t ∈ ERealFunction.subdifferential Phi (x t) ∧
          lam • deriv x t + deriv v t + v t + B (x t) = 0 := by
      have h := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      exact h
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hderiv_inner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt] with
      t hxt hvt hphit hinner horb ht hphid
    have hphi : HasDerivAt (fun s ↦ (Phi (x s) : EReal).toReal)
        (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t) t :=
      (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1;
        simp [inner_sub_left, real_inner_comm]; ring
    have hterm : HasDerivAt (fun s ↦ mu * ((Phi z : EReal).toReal -
        (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s)))
        (-mu * (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t +
          (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)))) t := by
      have hraw :=
        ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi).sub hin).const_mul mu)
      convert hraw using 1; simp [sub_eq_add_neg]; ring
    have hG : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s)))
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      convert hsq.add hterm using 1
      rw [hphit]
      simp [inner_sub_left, real_inner_comm]; ring
    have hmono := ERealFunction.isMonotone_subdifferential
      (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      (v t) (horb.1) (-B z) hzsub
    have hmono' : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      rw [real_inner_comm]
      simpa [inner_sub_right, inner_add_right, inner_neg_right] using hmono
    have hcoco := hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
        inner ℝ (x t - z) (B (x t) - B z) := hcoco
    rw [show deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s))) t =
        inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) by
      exact hG.deriv]
    have horb' := prop212_orbit_inner_identity lam mu hmu_lam (x t - z)
      (deriv x t) (deriv v t) (v t + B (x t)) (by simpa [add_assoc] using horb.2)
    rw [inner_sub_right] at hcoco'
    rw [inner_add_right] at hmono'
    have hsplit : inner ℝ (x t - z) (v t + B (x t)) =
        inner ℝ (x t - z) (v t + B z) +
          inner ℝ (x t - z) (B (x t) - B z) := by
      rw [show B (x t) = B z + (B (x t) - B z) by abel]
      simp only [inner_add_right]
      abel_nf
    have horb_scalar : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * inner ℝ (x t - z) (v t + B (x t)) = 0 := by
      rw [inner_add_right] at horb'
      simpa [mul_add, add_assoc] using horb'
    rw [hsplit] at horb_scalar
    have hmono_exp : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      simpa [inner_add_right] using hmono'
    have hmono_mu : 0 ≤ mu * inner ℝ (x t - z) (v t + B z) :=
      mul_nonneg hmu.le hmono_exp
    have hcoco_mu := mul_le_mul_of_nonneg_left hcoco' hmu.le
    have hcoco_mu' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * (inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z)) := by
      simpa [mul_assoc] using hcoco_mu
    have hinnerB : inner ℝ (x t - z) (B (x t) - B z) =
        inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z) := by
      rw [inner_sub_right]
    have hcoco_mu'' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * inner ℝ (x t - z) (B (x t) - B z) := by
      rw [hinnerB]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcoco' hmu.le
    linarith [horb_scalar, hmono_mu, hcoco_mu'', hinnerB]
  let Gamma : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))
  have hBcont : Continuous B :=
    (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hGamma_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval (Gamma) 0 T := by
    intro T hT
    have hx0 : AbsolutelyContinuousOnInterval x 0 T := hx_ac T hT
    have hv0 : AbsolutelyContinuousOnInterval v 0 T := hv_ac T hT
    have hconstx : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hconstp : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hi : AbsolutelyContinuousOnInterval
        (fun t => inner ℝ (z - x t) (v t)) 0 T := by
      have hi' := prop212_inner_absolutelyContinuousOnInterval (hx0.sub hconstx) hv0
      convert hi'.neg using 1
      funext t
      simp [inner_sub_left]
    have ht : AbsolutelyContinuousOnInterval
        (fun t => (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (z - x t) (v t)) 0 T :=
      (hconstp.sub (hphi_chain T hT).1).sub hi
    simpa [Gamma] using
      (prop212_sqdist_absolutelyContinuousOnInterval hx0 z).add (ht.const_mul mu)
  have hq_local : ∀ T, 0 < T →
      IntegrableOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbc : ContinuousOn (fun t => B (x t)) (Set.Icc 0 T) :=
      hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)
    have hqc : ContinuousOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2)
        (Set.Icc 0 T) :=
      continuousOn_const.mul ((hbc.sub continuousOn_const).norm.pow 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (hqc.intervalIntegrable_of_Icc hT.le)
  have hGamma_pkg := prop212_dissipation_on_Ici
    (F := Gamma) (q := fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (L := 0)
    hGamma_ac hq_local
    (fun t ht => mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _))
    (fun t ht => by
      have hg := hgap_nonneg t ht
      dsimp [Gamma]
      nlinarith [sq_nonneg (‖x t - z‖)])
    (fun T hT => by simpa [Gamma] using hlyap T hT)
  have hGamma_anti : AntitoneOn Gamma (Set.Ici 0) := hGamma_pkg.1
  have hGamma_lim : ∃ l, Tendsto Gamma atTop (nhds l) := hGamma_pkg.2.1
  have hBsq : Integrable (fun t => ‖B (x t) - B z‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    have h := hGamma_pkg.2.2
    have h' := h.const_mul (mu * beta)⁻¹
    change Integrable (fun t => (mu * beta)⁻¹ *
      (mu * beta * ‖B (x t) - B z‖ ^ 2)) (volume.restrict (Set.Ici 0)) at h'
    convert h' using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hmu.ne' hbeta.ne'), one_mul]
  have hx_bound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ C := by
    refine ⟨‖z‖ + 2 * Gamma 0 + 1, ?_⟩
    intro t ht
    have hanti := hGamma_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hdist : ‖x t - z‖ ^ 2 ≤ 2 * Gamma 0 := by
      have hgap := hgap_nonneg t ht
      dsimp [Gamma] at hanti
      dsimp [Gamma]
      nlinarith [sq_nonneg (‖x t - z‖), sq_nonneg (‖x 0 - z‖)]
    have hdist' : ‖x t - z‖ ≤ 2 * Gamma 0 + 1 := by
      nlinarith [norm_nonneg (x t - z), sq_nonneg (‖x t - z‖)]
    calc
      ‖x t‖ ≤ ‖x t - z‖ + ‖z‖ := by
        calc
          ‖x t‖ = ‖(x t - z) + z‖ := by congr 1; abel
          _ ≤ ‖x t - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 2 * Gamma 0 + 1 := by linarith
  let E : ℝ → ℝ := fun t => Gamma t +
      2 * beta * ((Phi (x t) : EReal).toReal + inner ℝ (x t) (B z))
  have hE_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval E 0 T := by
    intro T hT
    have hi := prop212_inner_const_absolutelyContinuousOnInterval (hx_ac T hT) (B z)
    have hp := (hphi_chain T hT).1
    convert (hGamma_ac T hT).add ((hp.add hi).const_mul (2 * beta)) using 1;
      simp only [E, Gamma, real_inner_comm, add_comm]
    · funext t
      dsimp
      ring
  have hE_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv E t + beta * lam * ‖deriv x t‖ ^ 2 +
          mu * beta * ‖deriv v t + v t + B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hderiv_inner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hmonoSub : SetValuedOperator.IsMonotone
          (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
        ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      have htemp : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hv_deriv T hT), ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop212_inner_deriv_nonneg_of_monotone hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at htemp
      exact htemp
    have horbT : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        v t ∈ ERealFunction.subdifferential Phi (x t) ∧
          lam • deriv x t + deriv v t + v t + B (x t) = 0 :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hderiv_inner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt,
      hlyap T hT] with
      t hxt hvt hphit hinner horb ht hphid hgamma
    have hphi' : HasDerivAt (fun s ↦ (Phi (x s) : EReal).toReal)
        (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t) t :=
      (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1;
        simp [inner_sub_left, real_inner_comm]; ring
    have hG0 : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s)))
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      have hterm :=
        ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi').sub hin).const_mul mu)
      convert hsq.add hterm using 1
      simp only [sub_eq_add_neg, inner_add_right, inner_neg_right, real_inner_comm, hphit]
      ring
    have hG : HasDerivAt Gamma
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      simpa [Gamma] using hG0
    have hI : HasDerivAt (fun s ↦ inner ℝ (x s) (B z))
        (inner ℝ (deriv x t) (B z)) t :=
      by simpa using hxt.inner ℝ (hasDerivAt_const (x := t) (B z))
    have hGd' : deriv Gamma t =
        inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) := hG.deriv
    have hId' : deriv (fun s ↦ inner ℝ (x s) (B z)) t =
        inner ℝ (deriv x t) (B z) := hI.deriv
    have haug := prop212_augmented_dissipation_algebra lam mu beta
      (deriv Gamma t) (inner ℝ (deriv x t) (v t))
      (inner ℝ (deriv x t) (B z)) (deriv x t) (deriv v t) (v t) (B (x t)) (B z)
      hmu_lam hbeta.le hinner horb.2 rfl rfl hgamma
    have hEhas : HasDerivAt E
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) +
          2 * beta *
            (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t +
              inner ℝ (deriv x t) (B z))) t := by
      have hh := hG.add ((hphi'.add hI).const_mul (2 * beta))
      convert hh using 1
    rw [hEhas.deriv]
    rw [hGd'] at haug
    have hphit' : inner ℝ (deriv x t) (v t) = deriv (fun s ↦ (Phi (x s) : EReal).toReal) t := by
      rw [real_inner_comm, hphit]
    rw [hphit'] at haug
    simpa [real_inner_comm, add_assoc, add_left_comm, add_comm] using haug
  let r : ℝ → H := fun t => deriv v t + v t + B z
  let q : ℝ → ℝ := fun t => beta * lam * ‖deriv x t‖ ^ 2 + mu * beta * ‖r t‖ ^ 2
  have hq_local : ∀ T, 0 < T → IntegrableOn q (Set.Ioc 0 T) := by
    intro T hT
    have hdx_sq : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbdc : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hbd_sq : IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      hbdc.integrableOn_Icc
    have hbdv : AEStronglyMeasurable (fun t => B (x t) - B z)
        (volume.restrict (Set.Icc 0 T)) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).aestronglyMeasurable measurableSet_Icc
    let R : ℝ → H := fun t => -(lam • deriv x t + (B (x t) - B z))
    have hR_sq : IntegrableOn (fun t => ‖R t‖ ^ 2) (Set.Icc 0 T) := by
      apply Integrable.mono' ((hdx_sq.const_mul (2 * lam ^ 2)).add
        (hbd_sq.const_mul 2))
      · exact (((hdxL2 T hT).aestronglyMeasurable.const_smul lam).add hbdv).neg.norm.pow 2
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        dsimp [R]
        rw [norm_neg]
        have h := norm_add_le (lam • deriv x t) (B (x t) - B z)
        rw [abs_of_nonneg (sq_nonneg _)]
        have hs : ‖lam • deriv x t‖ = lam * ‖deriv x t‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        rw [hs] at h
        have hsquare := (sq_le_sq₀ (norm_nonneg (lam • deriv x t + (B (x t) - B z)))
          (by positivity)).mpr h
        have hbound : (lam * ‖deriv x t‖ + ‖B (x t) - B z‖) ^ 2 ≤
            2 * lam ^ 2 * ‖deriv x t‖ ^ 2 + 2 * ‖B (x t) - B z‖ ^ 2 := by
          nlinarith [sq_nonneg (lam * ‖deriv x t‖ - ‖B (x t) - B z‖)]
        exact hsquare.trans hbound
    have hreq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        ‖r t‖ ^ 2 = ‖R t‖ ^ 2 := by
      have ho := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      filter_upwards [ho] with t ht
      have hzero : (lam • deriv x t + deriv v t + v t) + B (x t) = 0 := by
        simpa [add_assoc] using ht.2
      have hbx : B (x t) = -(lam • deriv x t + deriv v t + v t) :=
        eq_neg_of_add_eq_zero_right hzero
      dsimp [r, R]
      rw [hbx]
      congr 1
      abel_nf
    have hres_sq : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) := by
      apply hR_sq.congr
      filter_upwards [hreq] with t ht
      exact ht.symm
    have hqIcc : IntegrableOn q (Set.Icc 0 T) := by
      dsimp [q]
      exact (hdx_sq.const_mul (beta * lam)).add (hres_sq.const_mul (mu * beta))
    exact hqIcc.mono_set Set.Ioc_subset_Icc_self
  have hres_local : ∀ T, 0 < T →
      IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hdx_sq : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbdc : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hbd_sq : IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      hbdc.integrableOn_Icc
    have hbdv : AEStronglyMeasurable (fun t => B (x t) - B z)
        (volume.restrict (Set.Icc 0 T)) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).aestronglyMeasurable measurableSet_Icc
    let R : ℝ → H := fun t => -(lam • deriv x t + (B (x t) - B z))
    have hR_sq : IntegrableOn (fun t => ‖R t‖ ^ 2) (Set.Icc 0 T) := by
      apply Integrable.mono' ((hdx_sq.const_mul (2 * lam ^ 2)).add
        (hbd_sq.const_mul 2))
      · exact (((hdxL2 T hT).aestronglyMeasurable.const_smul lam).add hbdv).neg.norm.pow 2
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        dsimp [R]
        rw [norm_neg]
        have h := norm_add_le (lam • deriv x t) (B (x t) - B z)
        rw [abs_of_nonneg (sq_nonneg _)]
        have hs : ‖lam • deriv x t‖ = lam * ‖deriv x t‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        rw [hs] at h
        have hsquare := (sq_le_sq₀ (norm_nonneg (lam • deriv x t + (B (x t) - B z)))
          (by positivity)).mpr h
        have hbound : (lam * ‖deriv x t‖ + ‖B (x t) - B z‖) ^ 2 ≤
            2 * lam ^ 2 * ‖deriv x t‖ ^ 2 + 2 * ‖B (x t) - B z‖ ^ 2 := by
          nlinarith [sq_nonneg (lam * ‖deriv x t‖ - ‖B (x t) - B z‖)]
        exact hsquare.trans hbound
    have hreq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        ‖r t‖ ^ 2 = ‖R t‖ ^ 2 := by
      have ho := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      filter_upwards [ho] with t ht
      have hzero : (lam • deriv x t + deriv v t + v t) + B (x t) = 0 := by
        simpa [add_assoc] using ht.2
      have hbx : B (x t) = -(lam • deriv x t + deriv v t + v t) :=
        eq_neg_of_add_eq_zero_right hzero
      dsimp [r, R]
      rw [hbx]
      congr 1
      abel_nf
    have hres_sq : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) := by
      apply hR_sq.congr
      filter_upwards [hreq] with t ht
      exact ht.symm
    exact hres_sq.mono_set Set.Ioc_subset_Icc_self
  have hq_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t := by
    intro t ht
    dsimp [q]
    positivity
  have hE_pkg := prop212_dissipation_on_Ici
    (F := E) (q := q)
    (L := 2 * beta * ((Phi z : EReal).toReal + inner ℝ z (B z)))
    hE_ac hq_local hq_nonneg
    (fun t ht => by
      dsimp [E, Gamma]
      have hg := hgap_nonneg t ht
      have hminor := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi hzsub
        (hdom.1 t ht)
      have hminor' : (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z) ≥
          (Phi z : EReal).toReal + inner ℝ z (B z) := by
        rw [real_inner_comm] at hminor
        simp only [inner_neg_right] at hminor
        simp only [real_inner_comm, inner_sub_right] at hminor ⊢
        linarith
      nlinarith [sq_nonneg (‖x t - z‖)])
    (by simpa [q, r, add_assoc] using hE_deriv)
  have hE_lim : ∃ l, Tendsto E atTop (nhds l) := hE_pkg.2.1
  have hq_int : Integrable q (volume.restrict (Set.Ici 0)) := hE_pkg.2.2
  have hq_integral_nonneg : 0 ≤ ∫ t in Set.Ici 0, q t := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hq_nonneg t ht
  have hq_global : ∀ T, 0 < T →
      (∫ t in Set.Ioc 0 T, q t) ≤ ∫ t in Set.Ici 0, q t := by
    intro T hT
    apply MeasureTheory.setIntegral_mono_set hq_int
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hq_nonneg t ht
    · exact Filter.Eventually.of_forall (fun t ht => ht.1.le)
  have hdx_int : Integrable (fun t => ‖deriv x t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, q t) / (beta * lam))
    · intro T
      by_cases hT : 0 < T
      · have hdxIcc : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
          (memLp_two_iff_integrable_sq_norm
            (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
        exact hdxIcc.mono_set Set.Ioc_subset_Icc_self
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact div_nonneg hq_integral_nonneg (le_of_lt (mul_pos hbeta hlam))
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hdxIcc : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
        (memLp_two_iff_integrable_sq_norm
          (hdxL2 T hTpos).aestronglyMeasurable).mp (hdxL2 T hTpos)
      have hdxIoc := hdxIcc.mono_set Set.Ioc_subset_Icc_self
      have hqIoc := hq_local T hTpos
      have hcmp : ∫ t in Set.Ioc 0 T, (beta * lam) * ‖deriv x t‖ ^ 2 ≤
          ∫ t in Set.Ioc 0 T, q t := by
        apply MeasureTheory.integral_mono_ae (hdxIoc.const_mul (beta * lam)) hqIoc
        filter_upwards with t
        dsimp [q]
        have hn : 0 ≤ mu * beta * ‖r t‖ ^ 2 :=
          mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _)
        linarith
      have hc : 0 < beta * lam := mul_pos hbeta hlam
      have hmul : (beta * lam) * (∫ t in Set.Ioc 0 T, ‖deriv x t‖ ^ 2) ≤
          ∫ t in Set.Ici 0, q t := by
        rw [← MeasureTheory.integral_const_mul]
        exact hcmp.trans (hq_global T hTpos)
      have hdiv : (∫ t in Set.Ioc 0 T, ‖deriv x t‖ ^ 2) ≤
          (∫ t in Set.Ici 0, q t) / (beta * lam) :=
        (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
      rw [intervalIntegral.integral_of_le hT]
      exact hdiv
  have hres_int : Integrable (fun t => ‖r t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, q t) / (mu * beta))
    · intro T
      by_cases hT : 0 < T
      · exact hres_local T hT
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact div_nonneg hq_integral_nonneg (le_of_lt (mul_pos hmu hbeta))
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hresIoc := hres_local T hTpos
      have hqIoc := hq_local T hTpos
      have hcmp : ∫ t in Set.Ioc 0 T, (mu * beta) * ‖r t‖ ^ 2 ≤
          ∫ t in Set.Ioc 0 T, q t := by
        apply MeasureTheory.integral_mono_ae (hresIoc.const_mul (mu * beta)) hqIoc
        filter_upwards with t
        dsimp [q]
        have hn : 0 ≤ beta * lam * ‖deriv x t‖ ^ 2 :=
          mul_nonneg (mul_nonneg hbeta.le hlam.le) (sq_nonneg _)
        linarith
      have hc : 0 < mu * beta := mul_pos hmu hbeta
      have hmul : (mu * beta) * (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤
          ∫ t in Set.Ici 0, q t := by
        rw [← MeasureTheory.integral_const_mul]
        exact hcmp.trans (hq_global T hTpos)
      have hdiv : (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤
          (∫ t in Set.Ici 0, q t) / (mu * beta) :=
        (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
      rw [intervalIntegral.integral_of_le hT]
      exact hdiv
  have hdv_local : ∀ T, 0 < T →
      IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Set.Icc 0 T) := by
    intro T hT
    have hresIcc : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) :=
      hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
    have hv_sq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hvL2 T hT).aestronglyMeasurable).mp (hvL2 T hT)
    have hvplus_sq : IntegrableOn (fun t => ‖v t + B z‖ ^ 2) (Set.Icc 0 T) := by
      have hconst : IntegrableOn (fun _ : ℝ => ‖B z‖ ^ 2) (Set.Icc 0 T) :=
        continuousOn_const.integrableOn_Icc
      apply Integrable.mono' (hv_sq.const_mul 2 |>.add
        (hconst.const_mul 2))
      · exact ((hvL2 T hT).aestronglyMeasurable.add
          (continuousOn_const.aestronglyMeasurable measurableSet_Icc)).norm.pow 2
      · filter_upwards with t
        dsimp
        rw [abs_of_nonneg (sq_nonneg _)]
        have hn := norm_add_le (v t) (B z)
        have hsquare := (sq_le_sq₀ (norm_nonneg (v t + B z))
          (by positivity)).mpr hn
        nlinarith [hsquare, sq_nonneg (‖v t‖ - ‖B z‖)]
    apply Integrable.mono' (hresIcc.const_mul 2 |>.add (hvplus_sq.const_mul 2))
    · exact (aestronglyMeasurable_deriv v (volume.restrict (Set.Icc 0 T))).norm.pow 2
    · filter_upwards with t
      dsimp
      rw [abs_of_nonneg (sq_nonneg _)]
      have heq : deriv v t = r t - (v t + B z) := by
        dsimp [r]
        abel
      rw [heq]
      have hn := norm_sub_le (r t) (v t + B z)
      have hsquare := (sq_le_sq₀ (norm_nonneg (r t - (v t + B z)))
        (by positivity)).mpr hn
      nlinarith [hsquare, sq_nonneg (‖r t‖ - ‖v t + B z‖)]
  have hres_global : ∀ T, 0 < T →
      (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤ ∫ t in Set.Ici 0, ‖r t‖ ^ 2 := by
    intro T hT
    apply MeasureTheory.setIntegral_mono_set hres_int
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact sq_nonneg _
    · exact Filter.Eventually.of_forall (fun t ht => ht.1.le)
  have hdv_int : Integrable (fun t => ‖deriv v t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    have hri : 0 ≤ ∫ t in Set.Ici 0, ‖r t‖ ^ 2 := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact sq_nonneg _
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2)
    · intro T
      by_cases hT : 0 < T
      · exact (hdv_local T hT).mono_set Set.Ioc_subset_Icc_self
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact add_nonneg hri (sq_nonneg _)
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hresIcc : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) :=
        hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
      have hdv_sq := hdv_local T hTpos
      have hr_eq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
          r t = deriv v t + v t + B z := by
        filter_upwards with t
        rfl
      have hend := prop212_residual_endpoint_inequality (v := v) (r := r) (b := B z)
        hTpos (hv_ac T hTpos) (hv_deriv T hTpos) hdv_sq hresIcc hr_eq
      simp_rw [intervalIntegral.integral_of_le hTpos.le] at hend
      have hcmp := hres_global T hTpos
      have hbound : (∫ t in Set.Ioc 0 T, ‖deriv v t‖ ^ 2) + ‖v T + B z‖ ^ 2 ≤
          (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2 := by
        linarith
      rw [intervalIntegral.integral_of_le hT]
      linarith [hbound, sq_nonneg (‖v T + B z‖)]
  have hv_bound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖v t‖ ≤ C := by
    let C : ℝ := (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2
    refine ⟨‖v 0‖ + ‖B z‖ + C + 1, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hri : 0 ≤ ∫ s in Set.Ici 0, ‖r s‖ ^ 2 := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        exact sq_nonneg _
      dsimp [C]
      nlinarith [hri, norm_nonneg (v 0), norm_nonneg (B z), sq_nonneg (‖v 0 + B z‖)]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hresIcc : IntegrableOn (fun s => ‖r s‖ ^ 2) (Set.Icc 0 t) :=
        hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
      have hdv_sq := hdv_local t htpos
      have hr_eq : ∀ᵐ s ∂volume.restrict (Set.Icc 0 t),
          r s = deriv v s + v s + B z := by
        filter_upwards with s
        rfl
      have hend := prop212_residual_endpoint_inequality (v := v) (r := r) (b := B z)
        htpos (hv_ac t htpos) (hv_deriv t htpos) hdv_sq hresIcc hr_eq
      simp_rw [intervalIntegral.integral_of_le htpos.le] at hend
      have hcmp := hres_global t htpos
      have hri : 0 ≤ ∫ s in Set.Ici 0, ‖r s‖ ^ 2 := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        exact sq_nonneg _
      have hstate : ‖v t + B z‖ ^ 2 ≤ C := by
        dsimp [C]
        have hdi : 0 ≤ ∫ s in Set.Ioc 0 t, ‖deriv v s‖ ^ 2 := by
          apply MeasureTheory.integral_nonneg_of_ae
          filter_upwards with s
          exact sq_nonneg _
        linarith [hend, hcmp, hdi]
      have hstate' : ‖v t + B z‖ ≤ C + 1 := by
        have hC : 0 ≤ C := by
          dsimp [C]
          exact add_nonneg hri (sq_nonneg _)
        nlinarith [hstate, hC, norm_nonneg (v t + B z),
          sq_nonneg (‖v t + B z‖ - (C + 1))]
      calc
        ‖v t‖ ≤ ‖v t + B z‖ + ‖B z‖ := by
          calc
            ‖v t‖ = ‖(v t + B z) - B z‖ := by congr 1; abel
            _ ≤ ‖v t + B z‖ + ‖B z‖ := norm_sub_le _ _
        _ ≤ ‖v 0‖ + ‖B z‖ + C + 1 := by
          linarith [hstate', norm_nonneg (B z), norm_nonneg (v 0)]
  have hscalar_lim : ∃ l, Tendsto
      (fun t => (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop (nhds l) := by
    obtain ⟨lE, hEl⟩ := hE_lim
    obtain ⟨lG, hGl⟩ := hGamma_lim
    have hsub := hEl.sub hGl
    have hscaled := hsub.const_mul ((2 * beta)⁻¹)
    have hF : Tendsto
        (fun t => (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop
        (nhds ((2 * beta)⁻¹ * (lE - lG))) := by
      convert hscaled using 1
      funext t
      dsimp [E]
      field_simp [ne_of_gt hbeta]
      ring
    exact ⟨(2 * beta)⁻¹ * (lE - lG), hF⟩
  exact ⟨hGamma_anti, hGamma_lim, hBsq, hx_bound, hdx_int, hres_int,
    hdv_int, hv_bound, hscalar_lim⟩

end AbbasDynamical2015
