import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_7
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_5
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.prop_1
import Mathlib
import Foundation.Convex.Subdifferential
import Foundation.Hilbert.WeakTopology

namespace AbbasDynamical2015

open MeasureTheory Filter

private theorem prop216_integrableOn_Ici_of_nonneg_interval_bound
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

private theorem prop216_dissipation_on_Ici
    {F q : ℝ → ℝ} {L : ℝ}
    (hF_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval F 0 T)
    (hq_local : ∀ T, 0 < T → IntegrableOn q (Set.Ioc 0 T))
    (hq_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hF_lower : ∀ t, 0 ≤ t → L ≤ F t)
    (hderiv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), deriv F t + q t ≤ 0) :
    IntegrableOn q (Set.Ici 0) := by
  have hq_bound : ∀ T, 0 < T → (∫ s in 0..T, q s) ≤ F 0 - L := by
    intro T hT
    have hqint : IntervalIntegrable q volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hq_local T hT)
    have hFint : IntervalIntegrable (fun s => -deriv F s) volume 0 T :=
      (hF_ac T hT).intervalIntegrable_deriv.neg
    have hpoint : ∀ᵐ s ∂volume.restrict (Set.Icc 0 T), q s ≤ -deriv F s := by
      filter_upwards [hderiv T hT] with s hs
      linarith
    have hint := intervalIntegral.integral_mono_ae_restrict hT.le hqint hFint hpoint
    rw [intervalIntegral.integral_neg] at hint
    rw [(hF_ac T hT).integral_deriv_eq_sub] at hint
    linarith [hF_lower T hT.le]
  apply prop216_integrableOn_Ici_of_nonneg_interval_bound (C := F 0 - L)
    (hlocal := fun T => by
      by_cases hT : 0 < T
      · exact hq_local T hT
      · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
        exact integrableOn_empty)
    (hnonneg := hq_nonneg)
  intro T hT
  rcases hT.eq_or_lt with rfl | hT
  · simpa using (show 0 ≤ F 0 - L from by linarith [hF_lower 0 le_rfl])
  · exact hq_bound T hT

private theorem prop216_sqdist_ac {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H} {a b : ℝ} (hx : AbsolutelyContinuousOnInterval x a b) (z : H) :
    AbsolutelyContinuousOnInterval (fun t => (1 / 2 : ℝ) * ‖x t - z‖ ^ 2) a b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  have hs := hx.sub hconst
  have hn : AbsolutelyContinuousOnInterval (fun t => ‖x t - z‖) a b := by
    rw [absolutelyContinuousOnInterval_iff] at hs ⊢
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hs ε hε
    refine ⟨δ, hδ, ?_⟩
    intro E hE hsum
    refine lt_of_le_of_lt ?_ (hh _ hE hsum)
    apply Finset.sum_le_sum
    intro i hi
    simpa [Real.norm_eq_abs, dist_eq_norm] using
      (abs_norm_sub_norm_le (x (E.2 i).1 - z) (x (E.2 i).2 - z))
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using (hn.mul hn).const_mul (1 / 2 : ℝ)

private theorem prop216_inner_ac {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : ℝ → H} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
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

private theorem prop216_orbit_inner_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (lam mu : ℝ) (hmu_lam : mu * lam = 1)
    (a dx dv q : H) (horb : lam • dx + dv + q = 0) :
    inner ℝ a dx + mu * inner ℝ a (dv + q) = 0 := by
  have hs := congrArg (fun y : H => inner ℝ a y) horb
  have hs' : lam * inner ℝ a dx + (inner ℝ a dv + inner ℝ a q) = 0 := by
    dsimp only at hs
    rw [inner_add_right, inner_add_right, real_inner_smul_right] at hs
    simpa [add_assoc] using hs
  rw [inner_add_right]
  calc
    inner ℝ a dx + mu * (inner ℝ a dv + inner ℝ a q) =
        (mu * lam) * inner ℝ a dx + mu * (inner ℝ a dv + inner ℝ a q) := by rw [hmu_lam]; ring
    _ = mu * (lam * inner ℝ a dx + (inner ℝ a dv + inner ℝ a q)) := by ring
    _ = 0 := by rw [hs', mul_zero]

private theorem prop216_inner_deriv_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {T : SetValuedOperator H H} {x v dx dv : ℝ → H}
    (hT : T.IsMonotone) (hmem : ∀ s : ℝ, 0 ≤ s → v s ∈ T (x s)) {t : ℝ} (ht : 0 < t)
    (hxd : HasDerivAt x (dx t) t) (hvd : HasDerivAt v (dv t) t) :
    0 ≤ inner ℝ (dx t) (dv t) := by
  let qx : ℝ → H := fun h => h⁻¹ • (x (t + h) - x t)
  let qv : ℝ → H := fun h => h⁻¹ • (v (t + h) - v t)
  have hqx := hxd.tendsto_slope_zero
  have hqv := hvd.tendsto_slope_zero
  have hlim : Tendsto (fun h => inner ℝ (qx h) (qv h)) (nhdsWithin 0 {0}ᶜ)
      (nhds (inner ℝ (dx t) (dv t))) := hqx.inner hqv
  rw [← neg_nonpos]
  apply le_of_tendsto hlim.neg
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ⟨t, ht, ?_⟩
  intro h hh hne
  have hth : 0 ≤ t + h := by rw [Real.dist_eq] at hh; nlinarith [abs_lt.mp hh]
  have hm := hT (v (t + h)) (hmem (t + h) hth) (v t) (hmem t ht.le)
  dsimp [qx, qv]
  rw [real_inner_smul_left, inner_smul_right]
  rw [real_inner_comm]
  rw [← mul_assoc]
  exact neg_nonpos.mpr (mul_nonneg (mul_self_nonneg _) hm)

private theorem prop216_augmented_dissipation_algebra
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

private theorem prop216_limit_zero_of_memLp_deriv_bound_Ici (F G : ℝ → ℝ) (p r : ENNReal)
    (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ENNReal)) (hr : 1 ≤ r)
    (hF_nonneg : ∀ t, 0 ≤ t → 0 ≤ F t)
    (hF_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval F 0 b)
    (hF : MemLp F p (volume.restrict (Set.Ici 0)))
    (hG : MemLp G r (volume.restrict (Set.Ici 0)))
    (hderiv : ∀ᵐ t ∂volume.restrict (Set.Ici 0), deriv F t ≤ G t) :
    Tendsto F atTop (nhds 0) := by
  let F0 : ℝ → ℝ := (Set.Ici (0 : ℝ)).indicator F
  let G0 : ℝ → ℝ := (Set.Ici (0 : ℝ)).indicator G
  have hF0 : MemLp F0 p volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Ici]
    simpa [F0] using hF
  have hG0 : MemLp G0 r volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Ici]
    simpa [G0] using hG
  have hF0_nonneg : ∀ t, 0 ≤ F0 t := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa [F0, Set.mem_Ici, ht] using hF_nonneg t ht
    · simp [F0, Set.mem_Ici, ht]
  have hF0_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval F0 0 b := by
    intro b hb
    have h := hF_ac b hb
    rw [absolutelyContinuousOnInterval_iff] at h ⊢
    intro ε hε
    rcases h ε hε with ⟨δ, hδ, hsmall⟩
    refine ⟨δ, hδ, ?_⟩
    intro E hE hsum
    calc
      ∑ i ∈ Finset.range E.1, dist (F0 (E.2 i).1) (F0 (E.2 i).2) =
          ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hleft := hE.left i hi
        have hleft' : 0 ≤ (E.2 i).1 := by
          rw [Set.uIcc_of_le (le_of_lt hb)] at hleft
          exact hleft.1.1
        have hright' : 0 ≤ (E.2 i).2 := by
          rw [Set.uIcc_of_le (le_of_lt hb)] at hleft
          exact hleft.2.1
        simp [F0, Set.mem_Ici, hleft', hright']
      _ < ε := hsmall E hE hsum
  have hderiv0 : ∀ᵐ t ∂volume, deriv F0 t ≤ G0 t := by
    have hpos : ∀ᵐ t ∂volume, 0 < t → deriv F0 t ≤ G0 t := by
      rw [ae_restrict_iff' measurableSet_Ici] at hderiv
      filter_upwards [hderiv] with t ht
      intro htn
      have heq : F0 =ᶠ[nhds t] F := by
        filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (0 : ℝ) from htn)] with s hs
        simp [F0, Set.mem_Ici, le_of_lt (show 0 < s from hs)]
      have hgeq : G0 t = G t := by simp [G0, Set.mem_Ici, le_of_lt htn]
      rw [Filter.EventuallyEq.deriv_eq heq, hgeq]
      exact ht (le_of_lt htn)
    have hneq : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [hpos, hneq] with t ht htn
    rcases lt_or_gt_of_ne htn with hlt | hgt
    · have heq : F0 =ᶠ[nhds t] (fun _ : ℝ => 0) := by
        filter_upwards [(isOpen_Iio.mem_nhds (show t ∈ Set.Iio (0 : ℝ) from hlt))] with s hs
        simp [F0, Set.mem_Ici, not_le.mpr (show s < 0 from hs)]
      have hz : deriv F0 t = 0 := by
        rw [Filter.EventuallyEq.deriv_eq heq]
        simp
      simp [G0, Set.mem_Ici, not_le.mpr hlt, hz]
    · exact ht hgt
  have hlim := limit_zero_of_memLp_deriv_bound F0 G0 p r hp hp_top hr hF0_nonneg hF0_ac hF0 hG0
    hderiv0
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [F0, Set.mem_Ici, ht]


/-- Proposition 2.16: energy-gap integrability and convergence for a strong orbit. -/
theorem proposition_2_16 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hz : z ∈ S)
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
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf))) :
    Integrable (fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
      inner ℝ (B z) (x t - z)) (volume.restrict (Set.Ici 0)) ∧
    Tendsto (fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
      inner ℝ (B z) (x t - z)) atTop (nhds 0) ∧
    ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)) ∧
      Tendsto (fun t ↦ (Phi (x t) : EReal).toReal) atTop
        (nhds (Phi xinf : EReal).toReal) := by
  have hp := proposition_2_12 S Phi hPhi B x v z lam mu beta hS hz hlam hmu
    hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2
    horbit hsolution hdom
  rcases hp with ⟨hGamma_anti, hGamma_lim, hBsq, hx_bound, hdx_sq, hres_sq,
    hdv_sq, hv_bound, henergy_lim⟩
  let F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
    inner ℝ (B z) (x t - z)
  have hF_nonneg : ∀ t, 0 ≤ t → 0 ≤ F t := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution z hz) (hdom.1 t ht)
    dsimp [F]
    rw [real_inner_comm]
    rw [inner_neg_left, real_inner_comm] at hineq
    linarith
  have hphi_chain : ∀ T, 0 < T →
      AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t) := by
    intro T hT
    apply subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hsubgradient t ht.1
    · intro t ht
      exact hdom.1 t ht.1
    · exact hx_deriv T hT
    · exact hvL2 T hT
    · exact hdxL2 T hT
  let Gamma : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))
  have hGamma_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval Gamma 0 T := by
    intro T hT
    have hx0 := hx_ac T hT
    have hconstx : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hconstp : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hi : AbsolutelyContinuousOnInterval
        (fun t => inner ℝ (z - x t) (v t)) 0 T := by
      have hi' := prop216_inner_ac (hx0.sub hconstx) (hv_ac T hT)
      convert hi'.neg using 1
      funext t
      simp [inner_sub_left]
    have ht : AbsolutelyContinuousOnInterval
        (fun t ↦ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (z - x t) (v t)) 0 T :=
      (hconstp.sub (hphi_chain T hT).1).sub hi
    simpa [Gamma] using
      (prop216_sqdist_ac hx0 z).add (ht.const_mul mu)
  have hderivGamma : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv Gamma t + mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hmonoSub : SetValuedOperator.IsMonotone
        (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
      ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
    have hinner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hh : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
            Set.Ioc_subset_Icc_self (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset
            Set.Ioc_subset_Icc_self (hv_deriv T hT),
          ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop216_inner_deriv_nonneg hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at hh
      exact hh
    have horbT := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hinner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt] with
      t hxt hvt hphit hdt horb ht hphid
    have hphi' := (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1
      simp [inner_sub_left, real_inner_comm]
      ring
    have hG : HasDerivAt Gamma
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      have hh := ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi').sub
          hin).const_mul mu)
      convert hsq.add hh using 1
      simp only [inner_sub_left, real_inner_comm]
      rw [hphit]
      ring
    have hmono := hmonoSub (v t) horb.1 (-B z) (hsolution z hz)
    have hmono' : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      rw [real_inner_comm]
      simpa [inner_sub_right, inner_add_right, inner_neg_right] using hmono
    have hcoco := hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
        inner ℝ (x t - z) (B (x t) - B z) := hcoco
    have horb' := prop216_orbit_inner_identity lam mu hmu_lam (x t - z)
      (deriv x t) (deriv v t) (v t + B (x t)) (by simpa [add_assoc] using horb.2)
    have hsplit : inner ℝ (x t - z) (v t + B (x t)) =
        inner ℝ (x t - z) (v t + B z) +
          inner ℝ (x t - z) (B (x t) - B z) := by
      rw [show B (x t) = B z + (B (x t) - B z) by abel]
      simp only [inner_add_right]
      abel_nf
    rw [inner_sub_right] at hcoco'
    rw [inner_add_right] at horb'
    have horb_scalar : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * inner ℝ (x t - z) (v t + B (x t)) = 0 := by
      simpa [mul_add, add_assoc] using horb'
    rw [hsplit] at horb_scalar
    have hmono_mu := mul_nonneg hmu.le (by simpa [inner_add_right] using hmono')
    have hcoco_mu := mul_le_mul_of_nonneg_left hcoco' hmu.le
    have hinnerB : inner ℝ (x t - z) (B (x t) - B z) =
        inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z) := by
      rw [inner_sub_right]
    have hcoco_mu' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * inner ℝ (x t - z) (B (x t) - B z) := by
      rw [hinnerB]
      simpa [mul_assoc] using hcoco_mu
    have hsub := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      horb.1 (hdom.2 z hz)
    rw [show z - x t = -(x t - z) by abel, inner_neg_right, real_inner_comm] at hsub
    have hFle : F t ≤ inner ℝ (x t - z) (v t) + inner ℝ (B z) (x t - z) := by
      dsimp [F]
      linarith
    have hinnerBz : inner ℝ (B z) (x t - z) = inner ℝ (x t - z) (B z) :=
      real_inner_comm _ _
    rw [hinnerBz] at hFle
    have hFle_mu := mul_le_mul_of_nonneg_left hFle hmu.le
    have hmono_mu' : 0 ≤ mu * (inner ℝ (x t - z) (v t) + inner ℝ (x t - z) (B z)) := by
      simpa [inner_add_right] using hmono_mu
    rw [inner_add_right] at horb_scalar
    rw [hinnerB] at horb_scalar
    rw [hinnerB] at hcoco_mu'
    have horb_scalar' : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * (inner ℝ (x t - z) (v t) + inner ℝ (x t - z) (B z)) +
        mu * (inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z)) = 0 := by
      linarith [horb_scalar]
    rw [hG.deriv]
    linarith [horb_scalar', hmono_mu', hFle_mu, hcoco_mu']
  have hq_local : ∀ T, 0 < T →
      IntegrableOn (fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hxc : ContinuousOn x (Set.uIcc 0 T) := (hx_ac T hT).continuousOn
    have hcF : ContinuousOn F (Set.Icc 0 T) := by
      have hpc : ContinuousOn (fun t => (Phi (x t) : EReal).toReal)
          (Set.Icc 0 T) := (hphi_chain T hT).1.continuousOn.mono Set.Icc_subset_uIcc
      have hxc' : ContinuousOn x (Set.Icc 0 T) := hxc.mono Set.Icc_subset_uIcc
      have hi : ContinuousOn (fun t => inner ℝ (B z) (x t - z)) (Set.Icc 0 T) :=
        continuousOn_const.inner (hxc'.sub continuousOn_const)
      simpa [F] using (hpc.sub continuousOn_const).add hi
    have hcB : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) := by
      have hBc : Continuous B :=
        (lipschitzWith_of_cocoercive hB).continuous.comp
          (continuous_id.subtype_mk fun _ => Set.mem_univ _)
      exact ((hBc.continuousOn.comp (hxc.mono Set.Icc_subset_uIcc)
          (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hiF : IntegrableOn (fun t => mu * F t) (Set.Icc 0 T) :=
      (hcF.const_mul mu).integrableOn_Icc
    have hiB : IntegrableOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      (hcB.const_mul (mu * beta)).integrableOn_Icc
    exact (hiF.add hiB).mono_set Set.Ioc_subset_Icc_self
  have hq_int : Integrable (fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop216_dissipation_on_Ici (F := Gamma)
      (q := fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2) (L := 0)
      hGamma_ac hq_local
      (fun t ht => add_nonneg (mul_nonneg hmu.le (hF_nonneg t ht))
        (mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _)))
      (fun t ht => by
        have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
          (hsubgradient t ht) (hdom.2 z hz)
        rw [real_inner_comm] at hineq
        dsimp [Gamma]
        nlinarith [sq_nonneg (‖x t - z‖)])
      (by simpa [add_assoc] using hderivGamma)
  have hF_int : Integrable F (volume.restrict (Set.Ici 0)) := by
    have hmuF : Integrable (fun t => mu * F t) (volume.restrict (Set.Ici 0)) := by
      convert hq_int.sub (hBsq.const_mul (mu * beta)) using 1
      funext t
      dsimp
      ring
    convert hmuF.const_mul mu⁻¹ using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hmu.ne', one_mul]
  have hFlim : Tendsto F atTop (nhds 0) := by
    obtain ⟨C, hC⟩ := hv_bound
    let G : ℝ → ℝ := fun t ↦ (C + ‖B z‖) * ‖deriv x t‖
    have hCnonneg : 0 ≤ C := by
      have hC0 := hC 0 le_rfl
      exact le_trans (norm_nonneg (v 0)) hC0
    have hG_nonneg : ∀ t, 0 ≤ G t := by
      intro t
      dsimp [G]
      exact mul_nonneg (add_nonneg hCnonneg (norm_nonneg _)) (norm_nonneg _)
    have hnorm_meas : AEStronglyMeasurable (fun t ↦ ‖deriv x t‖)
        (volume.restrict (Set.Ici 0)) := by
      apply AEMeasurable.aestronglyMeasurable
      convert hdx_sq.aestronglyMeasurable.aemeasurable.sqrt using 1
      funext t
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hG_meas : AEStronglyMeasurable G (volume.restrict (Set.Ici 0)) := by
      dsimp [G]
      exact hnorm_meas.const_mul _
    have hG_sq : Integrable (fun t ↦ G t ^ 2)
        (volume.restrict (Set.Ici 0)) := by
      convert hdx_sq.const_mul ((C + ‖B z‖) ^ 2) using 1
      funext t
      dsimp [G]
      ring
    have hG : MemLp G 2 (volume.restrict (Set.Ici 0)) := by
      rw [memLp_two_iff_integrable_sq_norm hG_meas]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg _)] using hG_sq
    have hderivF0 : ∀ n : ℕ, ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) (n + 1) →
        deriv F t ≤ G t := by
      intro n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hlocal : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) ((n : ℝ) + 1)), deriv F t ≤ G t := by
        filter_upwards [hx_deriv (n + 1) hn, (hphi_chain (n + 1) hn).2,
          MeasureTheory.ae_restrict_of_ae (hphi_chain (n + 1) hn).1.ae_differentiableAt,
          ae_restrict_mem measurableSet_Icc] with t hxt hphit hphid ht
        have hphi' := (hphid (by simpa [Set.uIcc_of_le hn.le] using ht)).hasDerivAt
        have hi : HasDerivAt (fun s ↦ inner ℝ (B z) (x s - z))
            (inner ℝ (B z) (deriv x t)) t := by
          simpa [inner_sub_right] using
            ((hasDerivAt_const (x := t) (B z)).inner ℝ (hxt.sub_const z))
        have hF' := ((hphi'.sub_const ((Phi z : EReal).toReal)).add hi)
        have hFd : deriv F t = inner ℝ (v t) (deriv x t) +
            inner ℝ (B z) (deriv x t) := by
          dsimp [F]
          simpa [hphit] using hF'.deriv
        rw [hFd]
        have hC' := hC t ht.1
        have hinner : inner ℝ (v t) (deriv x t) + inner ℝ (B z) (deriv x t) ≤
            (‖v t‖ + ‖B z‖) * ‖deriv x t‖ := by
          calc
            _ ≤ |inner ℝ (v t) (deriv x t)| + |inner ℝ (B z) (deriv x t)| := by
              linarith [le_abs_self (inner ℝ (v t) (deriv x t)),
                le_abs_self (inner ℝ (B z) (deriv x t))]
            _ ≤ ‖v t‖ * ‖deriv x t‖ + ‖B z‖ * ‖deriv x t‖ := by
              gcongr
              · exact abs_real_inner_le_norm _ _
              · exact abs_real_inner_le_norm _ _
            _ = (‖v t‖ + ‖B z‖) * ‖deriv x t‖ := by ring
        have hcoef : (‖v t‖ + ‖B z‖) * ‖deriv x t‖ ≤ G t := by
          dsimp [G]
          gcongr
        exact hinner.trans hcoef
      exact (ae_restrict_iff' (s := Set.Icc (0 : ℝ) (n + 1)) measurableSet_Icc).mp hlocal
    have hderivF : ∀ᵐ t ∂volume.restrict (Set.Ici 0), deriv F t ≤ G t := by
      rw [ae_restrict_iff' measurableSet_Ici]
      have hall : ∀ᵐ t ∂volume, ∀ n : ℕ,
          t ∈ Set.Icc (0 : ℝ) (n + 1) → deriv F t ≤ G t :=
        ae_all_iff.2 hderivF0
      filter_upwards [hall] with t ht htn
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ht n ⟨htn, by linarith⟩
    have hF_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval F 0 T := by
      intro T hT
      have hconstz : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
        contDiffOn_const.absolutelyContinuousOnInterval
      have hi : AbsolutelyContinuousOnInterval
          (fun t => inner ℝ (B z) (x t - z)) 0 T := by
        exact prop216_inner_ac (contDiffOn_const.absolutelyContinuousOnInterval)
          ((hx_ac T hT).sub hconstz)
      have hconstp : AbsolutelyContinuousOnInterval (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
        contDiffOn_const.absolutelyContinuousOnInterval
      simpa [F] using (((hphi_chain T hT).1.sub hconstp).add hi)
    exact prop216_limit_zero_of_memLp_deriv_bound_Ici F G 1 2
      (by norm_num) (by norm_num) (by norm_num) hF_nonneg
      hF_ac (memLp_one_iff_integrable.mpr hF_int) hG hderivF
  refine ⟨hF_int, ?_, ?_⟩
  · simpa [F] using hFlim
  · rcases hweak with ⟨xinf, hxinfS, hxweak⟩
    have hmonoSub : SetValuedOperator.IsMonotone
        (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
      ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
    have hmono := hmonoSub (-B xinf) (hsolution xinf hxinfS) (-B z) (hsolution z hz)
    have hmono' : inner ℝ (xinf - z) (B xinf - B z) ≤ 0 := by
      have hm : 0 ≤ inner ℝ (xinf - z) (-B xinf + B z) := by
        simpa [real_inner_comm] using hmono
      have heq : inner ℝ (xinf - z) (B xinf - B z) =
          -inner ℝ (xinf - z) (-B xinf + B z) := by
        simp only [inner_sub_right, inner_add_right, inner_neg_right]
        ring
      rw [heq]
      exact neg_nonpos.mpr hm
    have hcoco := hB.ineq ⟨xinf, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B xinf - B z‖ ^ 2 ≤
        inner ℝ (xinf - z) (B xinf - B z) := hcoco
    have hnorm : ‖B xinf - B z‖ = 0 := by
      have hs : ‖B xinf - B z‖ ^ 2 = 0 := by
        nlinarith [hcoco', hmono']
      nlinarith [hs, norm_nonneg (B xinf - B z)]
    have hB_equal : B xinf = B z := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hinner := (weakConvergence_iff_forall_tendsto_inner_right x xinf).1 hxweak (B z)
    have hinner_sub : Tendsto (fun t ↦ inner ℝ (B z) (x t - xinf)) atTop
        (nhds (inner ℝ (B z) (xinf - xinf))) := by
      have hconst : Tendsto (fun _ : ℝ ↦ inner ℝ xinf (B z)) atTop
          (nhds (inner ℝ xinf (B z))) := tendsto_const_nhds
      have hh := hinner.sub hconst
      simpa [inner_sub_right, real_inner_comm] using hh
    have hineq_z := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution z hz) (hdom.2 xinf hxinfS)
    have hineq_inf := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution xinf hxinfS) (hdom.2 z hz)
    have hvalue_zero : (Phi xinf : EReal).toReal - (Phi z : EReal).toReal +
        inner ℝ (B z) (xinf - z) = 0 := by
      have hz' : (Phi xinf : EReal).toReal ≥ (Phi z : EReal).toReal -
          inner ℝ (B z) (xinf - z) := by
        simpa [inner_neg_left, real_inner_comm] using hineq_z
      have hi' : (Phi z : EReal).toReal ≥ (Phi xinf : EReal).toReal +
          inner ℝ (B z) (xinf - z) := by
        rw [hB_equal] at hineq_inf
        rw [inner_neg_left] at hineq_inf
        rw [show z - xinf = -(xinf - z) by abel, inner_neg_right] at hineq_inf
        simp only [neg_neg] at hineq_inf
        exact hineq_inf
      linarith
    have hinner_z : Tendsto (fun t ↦ inner ℝ (B z) (x t - z)) atTop
        (nhds (inner ℝ (B z) (xinf - z))) := by
      have hconst : Tendsto (fun _ : ℝ ↦ inner ℝ z (B z)) atTop
          (nhds (inner ℝ z (B z))) := tendsto_const_nhds
      have hh := hinner.sub hconst
      simpa [inner_sub_right, real_inner_comm] using hh
    have hsum : Tendsto
        (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
        (nhds (0 + (Phi z : EReal).toReal - inner ℝ (B z) (xinf - z))) := by
      simpa using (hFlim.add tendsto_const_nhds).sub hinner_z
    have hval : Tendsto (fun t ↦ (Phi (x t) : EReal).toReal) atTop
        (nhds (Phi xinf : EReal).toReal) := by
      have hsum' : Tendsto
          (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
          (nhds (Phi xinf : EReal).toReal) := by
        have hsum0 : Tendsto
            (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
            (nhds ((Phi z : EReal).toReal - inner ℝ (B z) (xinf - z))) := by
          simpa using hsum
        rw [show (Phi z : EReal).toReal - inner ℝ (B z) (xinf - z) =
            (Phi xinf : EReal).toReal from by linarith [hvalue_zero]] at hsum0
        exact hsum0
      apply Filter.Tendsto.congr' _ hsum'
      filter_upwards [] with t
      dsimp [F]
      ring
    exact ⟨xinf, hxinfS, hxweak, hval⟩

end AbbasDynamical2015
