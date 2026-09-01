import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.Subdifferential
import Foundation.Differentiation.ODE
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.def_1

namespace AbbasDynamical2015

open MeasureTheory
open scoped Pointwise

private theorem ac_comp_of_lipschitzOn_image_vec
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℝ → E} {phi : E → F} {a b : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hphi : LipschitzOnWith K phi (f '' Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun s => phi (f s)) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  rcases (absolutelyContinuousOnInterval_iff _ _ _).mp hf (ε / (K + 1))
      (by positivity) with ⟨δ, hδ, hδ_bound⟩
  refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    ∑ i ∈ Finset.range n, dist (phi (f (I i).1)) (phi (f (I i).2))
        ≤ ∑ i ∈ Finset.range n, K * dist (f (I i).1) (f (I i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := hphi ⟨(I i).1, (hnI₁.left i hi).left, rfl⟩
            ⟨(I i).2, (hnI₁.left i hi).right, rfl⟩
          apply ENNReal.toReal_mono
            (ENNReal.mul_ne_top (by simp) (edist_ne_top _ _)) at h
          rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at h
    _ = K * ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2) := by
          rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by
          gcongr
          simpa using (hδ_bound (n, I) hnI₁ hnI₂).le
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

set_option maxHeartbeats 1600000 in
private theorem ac_hasDerivWithinAt_right_of_ae_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {a b : ℝ} {f g : ℝ → H} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContinuousOn g (Set.Icc a b))
    (hderiv : ∀ᵐ s ∂volume.restrict (Set.Icc a b), HasDerivAt f (g s) s) :
    ∀ x ∈ Set.Ico a b, HasDerivWithinAt f (g x) (Set.Ici x) x := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hderiv
  have hrep : ∀ y ∈ Set.Icc a b, f y = f a + ∫ s in a..y, g s := by
    intro y hy
    have hay : a ≤ y := hy.1
    have hgy : IntervalIntegrable g volume a y := by
      have hgy' : ContinuousOn g (Set.Icc a y) :=
        hg.mono fun s hs => ⟨hs.1, hs.2.trans hy.2⟩
      exact hgy'.intervalIntegrable_of_Icc hay
    have hcoord (w : H) :
        inner ℝ (f y - (f a + ∫ s in a..y, g s)) w = 0 := by
      let L : H →L[ℝ] ℝ := innerSL ℝ w
      have hLac : AbsolutelyContinuousOnInterval (fun s => L (f s)) a b := by
        apply ac_comp_of_lipschitzOn_image_vec hf
        exact L.lipschitz.lipschitzOnWith
      have hLacy : AbsolutelyContinuousOnInterval (fun s => L (f s)) a y := by
        apply hLac.mono
        simpa only [Set.uIcc_of_le hay, Set.uIcc_of_le hab] using
          (Set.Icc_subset_Icc le_rfl hy.2)
      have hcomp :
          (∫ s in a..y, deriv (fun s => L (f s)) s) =
            ∫ s in a..y, L (g s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hderiv] with s hs hsI
        have hsIoc : s ∈ Set.Ioc a y := by
          simpa [Set.uIoc_of_le hay] using hsI
        have hsIcc : s ∈ Set.Icc a b :=
          ⟨le_of_lt hsIoc.1, hsIoc.2.trans hy.2⟩
        have hsderiv := hs hsIcc
        have hscalar := L.hasFDerivAt.comp_hasDerivAt s hsderiv
        simpa only [Function.comp_apply] using hscalar.deriv
      have hftc := hLacy.integral_deriv_eq_sub
      calc
        inner ℝ (f y - (f a + ∫ s in a..y, g s)) w =
            L (f y) - L (f a) - L (∫ s in a..y, g s) := by
              simp only [L, innerSL_apply_apply, inner_sub_left, inner_add_left,
                real_inner_comm]
              abel
        _ = (∫ s in a..y, deriv (fun s => L (f s)) s) -
              ∫ s in a..y, L (g s) := by
              rw [← hftc, ← L.intervalIntegral_comp_comm hgy]
        _ = 0 := by rw [hcomp]; abel
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [← real_inner_self_eq_norm_sq]
    exact hcoord (f y - (f a + ∫ s in a..y, g s))
  intro x hx
  have hP : HasDerivWithinAt (fun y => f a + ∫ s in a..y, g s)
      (g x) (Set.Ici x) x := by
    apply HasDerivWithinAt.const_add
    letI : Fact (x ∈ Set.Icc a b) := ⟨⟨hx.1, hx.2.le⟩⟩
    have hIcc : Set.Icc a b ∈ nhdsWithin x (Set.Ioi x) := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx.2),
        self_mem_nhdsWithin] with y hyb hyx
      exact ⟨hx.1.trans hyx.le, hyb.le⟩
    have hcont : ContinuousWithinAt g (Set.Ioi x) x :=
      (hg x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin hIcc
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · have hgx : ContinuousOn g (Set.Icc a x) :=
        hg.mono fun s hs => ⟨hs.1, hs.2.trans hx.2.le⟩
      exact hgx.intervalIntegrable_of_Icc hx.1
    · exact (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem hIcc)
    · exact hcont
  apply hP.congr_of_eventuallyEq
  · have hIio : ∀ᶠ y in nhdsWithin x (Set.Ici x), y < b :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx.2)
    filter_upwards [self_mem_nhdsWithin, hIio] with y hy hyb
    exact hrep y ⟨hx.1.trans hy, hyb.le⟩
  · exact hrep x ⟨hx.1, hx.2.le⟩

/-- Theorem 2.1: existence and uniqueness of the strong global solution of (8)--(10). -/
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (lam beta : ℝ) (x0 v0 : H)
    (hlam : 0 < lam) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hv0 : v0 ∈ ERealFunction.subdifferential Phi x0) :
    ∃! xv : (ℝ → H) × (ℝ → H),
      IsStrongGlobalSolutionCombined Phi B lam x0 v0 xv.1 xv.2 ∧
      (∀ t, t < 0 → xv.1 t = x0) ∧
      (∀ t, t < 0 → xv.2 t = v0) := by
  have hB_lipschitz : LipschitzWith (Real.toNNReal (1 / beta)) B :=
    cocoercive_implies_lipschitz B beta hB
  let gamma : ERealFunction.PosReal := ⟨lam⁻¹, inv_pos.mpr hlam⟩
  let P : H → H := Prox[gamma, Phi, hPhi]
  have hP_firm : FirmlyNonexpansive P := by
    simpa [P, gamma, ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
        (ERealFunction.smul_mem_gammaZero Phi hPhi gamma)
  have hP_lipschitz : LipschitzWith 1 P :=
    lipschitzWith_one_of_firmlyNonexpansive hP_firm
  let F : H → H := fun q => P q - q - lam⁻¹ • B (P q)
  let K : NNReal := Real.toNNReal (2 + |lam⁻¹| / beta)
  have hK_nonneg : 0 ≤ 2 + |lam⁻¹| / beta := by positivity
  have hF_lipschitz : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [show (K : ℝ) = 2 + |lam⁻¹| / beta by
      exact Real.coe_toNNReal _ (by positivity)]
    have hPpq : ‖P p - P q‖ ≤ ‖p - q‖ := by
      simpa [dist_eq_norm] using hP_lipschitz.dist_le_mul p q
    have hBPpq : ‖B (P p) - B (P q)‖ ≤ (1 / beta) * ‖P p - P q‖ := by
      simpa only [dist_eq_norm,
        Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hbeta.le)] using
        hB_lipschitz.dist_le_mul (P p) (P q)
    calc
      dist (F p) (F q) = ‖(P p - P q) - (p - q) - lam⁻¹ • (B (P p) - B (P q))‖ := by
        rw [dist_eq_norm]
        congr 1
        simp only [F]
        module
      _ ≤ ‖P p - P q‖ + ‖p - q‖ + ‖lam⁻¹ • (B (P p) - B (P q))‖ := by
        calc
          _ ≤ ‖(P p - P q) - (p - q)‖ + ‖lam⁻¹ • (B (P p) - B (P q))‖ := norm_sub_le _ _
          _ ≤ (‖P p - P q‖ + ‖p - q‖) + ‖lam⁻¹ • (B (P p) - B (P q))‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = _ := by ac_rfl
      _ = ‖P p - P q‖ + ‖p - q‖ + |lam⁻¹| * ‖B (P p) - B (P q)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖p - q‖ + ‖p - q‖ + |lam⁻¹| * ((1 / beta) * ‖p - q‖) := by
        exact add_le_add (add_le_add hPpq le_rfl)
          (mul_le_mul_of_nonneg_left (hBPpq.trans (mul_le_mul_of_nonneg_left hPpq
            (one_div_nonneg.mpr hbeta.le))) (abs_nonneg _))
      _ = (2 + |lam⁻¹| / beta) * dist p q := by
        rw [dist_eq_norm]
        ring
  let q0 : H := x0 + lam⁻¹ • v0
  have hPq0 : P q0 = x0 := by
    rw [show P q0 = Prox[gamma • Phi, ERealFunction.smul_mem_gammaZero Phi hPhi gamma] q0 by
      rfl]
    symm
    apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
      (ERealFunction.smul_mem_gammaZero Phi hPhi gamma) q0 x0).2
    rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
    change q0 - x0 ∈ (gamma : ℝ) • ((ERealFunction.subdifferential Phi) x0)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ gamma.2.ne']
    simpa [q0, gamma, smul_smul, mul_inv_cancel₀ hlam.ne'] using hv0
  obtain ⟨z, hz0, hzderiv⟩ := exists_global_solution_of_lipschitz F hF_lipschitz q0
  have hz0' : z 0 = x0 + lam⁻¹ • v0 := by simpa [q0] using hz0
  have hz_continuous : Continuous z := continuous_iff_continuousAt.2 fun t =>
    (hzderiv t).continuousAt
  have hF_continuous : Continuous F := hF_lipschitz.continuous
  have hz_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval z 0 b := by
    intro b hb
    have hFz_continuous : Continuous (fun t => F (z t)) :=
      hF_continuous.comp hz_continuous
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      hFz_continuous.continuousOn
    have hC_nonneg : 0 ≤ C := by
      exact (norm_nonneg _).trans (hC 0 ⟨le_rfl, hb.le⟩)
    have hz_lipschitz : LipschitzOnWith (Real.toNNReal C) z (Set.Icc 0 b) := by
      apply (convex_Icc 0 b).lipschitzOnWith_of_nnnorm_deriv_le
      · intro t ht
        exact (hzderiv t).differentiableAt
      · intro t ht
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC_nonneg]
        simp only [coe_nnnorm]
        simpa only [(hzderiv t).deriv] using hC t ht
    have hz_lipschitz' : LipschitzOnWith (Real.toNNReal C) z (Set.uIcc 0 b) := by
      simpa only [Set.uIcc_of_le hb.le] using hz_lipschitz
    exact hz_lipschitz'.absolutelyContinuousOnInterval
  let x : ℝ → H := fun t => P (z t)
  let v : ℝ → H := fun t => lam • (z t - x t)
  have hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b := by
    intro b hb
    apply ac_comp_of_lipschitzOn_image_vec (hz_ac b hb)
    exact hP_lipschitz.lipschitzOnWith
  have hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b := by
    intro b hb
    simpa [v] using (hz_ac b hb).sub (hx_ac b hb) |>.const_smul lam
  have hx0 : x 0 = x0 := by
    simpa [x] using (congrArg P hz0).trans hPq0
  have hv0' : v 0 = v0 := by
    simp only [v]
    rw [hx0, hz0']
    calc
      lam • (x0 + lam⁻¹ • v0 - x0) = (lam * lam⁻¹) • v0 := by module
      _ = v0 := by rw [mul_inv_cancel₀ hlam.ne']; simp
  have hv_subgradient : ∀ t, v t ∈ ERealFunction.subdifferential Phi (x t) := by
    intro t
    simpa [v, x, P, gamma] using
      ERealFunction.scaledProximityOperator_residual_mem hPhi gamma (z t)
  have hz_eq : z = fun t => x t + lam⁻¹ • v t := by
    funext t
    simp only [x, v]
    rw [smul_smul, inv_mul_cancel₀ hlam.ne']
    module
  have hF_eq : ∀ t, F (z t) = -lam⁻¹ • (v t + B (x t)) := by
    intro t
    simp only [F, x, v]
    rw [smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hlam.ne']
    module
  have h_combined : ∀ t,
      HasDerivAt (fun s => lam • x s + v s) (-(v t + B (x t))) t := by
    intro t
    have hfun : (fun s => lam • x s + v s) = fun s => lam • z s := by
      funext s
      simp only [x, v]
      module
    rw [hfun]
    convert (hzderiv t).const_smul lam using 1
    rw [hF_eq, smul_smul, mul_neg, mul_inv_cancel₀ hlam.ne']
    module
  let xt : ℝ → H := fun t => if t < 0 then x0 else x t
  let vt : ℝ → H := fun t => if t < 0 then v0 else v t
  have hxt_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xt 0 b := by
    intro b hb
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    rcases (absolutelyContinuousOnInterval_iff _ _ _).mp (hx_ac b hb) ε hε with
      ⟨δ, hδ, hδ_bound⟩
    refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
    have hbound := hδ_bound (n, I) hnI₁ hnI₂
    apply lt_of_le_of_lt ?_ hbound
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 0 ≤ (I i).1 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).left.1
    have hi2 : 0 ≤ (I i).2 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).right.1
    rw [show xt (I i).1 = x (I i).1 by simp [xt, not_lt.mpr hi1],
      show xt (I i).2 = x (I i).2 by simp [xt, not_lt.mpr hi2]]
  have hvt_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval vt 0 b := by
    intro b hb
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    rcases (absolutelyContinuousOnInterval_iff _ _ _).mp (hv_ac b hb) ε hε with
      ⟨δ, hδ, hδ_bound⟩
    refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
    have hbound := hδ_bound (n, I) hnI₁ hnI₂
    apply lt_of_le_of_lt ?_ hbound
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 0 ≤ (I i).1 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).left.1
    have hi2 : 0 ≤ (I i).2 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).right.1
    rw [show vt (I i).1 = v (I i).1 by simp [vt, not_lt.mpr hi1],
      show vt (I i).2 = v (I i).2 by simp [vt, not_lt.mpr hi2]]
  have hpositive_ae : ∀ᵐ t ∂volume.restrict (Set.Ici (0 : ℝ)), 0 < t := by
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    exact ae_restrict_mem measurableSet_Ioi
  have ht_combined : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      HasDerivAt (fun s => lam • xt s + vt s) (-(vt t + B (xt t))) t := by
    filter_upwards [hpositive_ae] with t htpos
    have hxt_eq : xt =ᶠ[nhds t] x := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      have hs0 : 0 < s := hs
      simp [xt, not_lt.mpr hs0.le]
    have hvt_eq : vt =ᶠ[nhds t] v := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      have hs0 : 0 < s := hs
      simp [vt, not_lt.mpr hs0.le]
    have hcombined_eq : (fun s => lam • xt s + vt s) =ᶠ[nhds t]
        (fun s => lam • x s + v s) := hxt_eq.const_smul lam |>.add hvt_eq
    simpa [xt, vt, not_lt.mpr htpos.le] using
      (h_combined t).congr_of_eventuallyEq hcombined_eq
  have h_exists :
      IsStrongGlobalSolutionCombined Phi B lam x0 v0 xt vt ∧
      (∀ t, t < 0 → xt t = x0) ∧
      (∀ t, t < 0 → vt t = v0) := by
    refine ⟨⟨hxt_ac, hvt_ac, ?_, ht_combined, ?_, ?_⟩, ?_, ?_⟩
    · intro t ht
      simpa [xt, vt, not_lt.mpr ht] using hv_subgradient t
    · simpa [xt, not_lt.mpr le_rfl] using hx0
    · simpa [vt, not_lt.mpr le_rfl] using hv0'
    · intro t ht
      simp [xt, ht]
    · intro t ht
      simp [vt, ht]
  refine ⟨⟨xt, vt⟩, h_exists, ?_⟩
  intro y hy
  rcases hy with ⟨⟨hyx_ac, hyv_ac, hy_subgradient, hy_combined,
    hyx0, hyv0⟩, hyx_neg, hyv_neg⟩
  let q : ℝ → H := fun t => y.1 t + lam⁻¹ • y.2 t
  have hq_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval q 0 b := by
    intro b hb
    simpa [q] using (hyx_ac b hb).add ((hyv_ac b hb).const_smul lam⁻¹)
  have hq0 : q 0 = q0 := by
    simp [q, q0, hyx0, hyv0]
  have hy_prox : ∀ t, 0 ≤ t → y.1 t = P (q t) := by
    intro t ht
    rw [show P (q t) = Prox[gamma • Phi,
      ERealFunction.smul_mem_gammaZero Phi hPhi gamma] (q t) by rfl]
    apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
      (ERealFunction.smul_mem_gammaZero Phi hPhi gamma) (q t) (y.1 t)).2
    rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
    change q t - y.1 t ∈
      (gamma : ℝ) • ((ERealFunction.subdifferential Phi) (y.1 t))
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ gamma.2.ne']
    simpa [q, gamma, smul_smul, mul_inv_cancel₀ hlam.ne'] using hy_subgradient t ht
  have hy_combined_volume : ∀ᵐ t ∂volume,
      t ∈ Set.Ici 0 → HasDerivAt (fun s => lam • y.1 s + y.2 s)
        (-(y.2 t + B (y.1 t))) t := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hy_combined
  have hq_dynamics_Icc (b : ℝ) (hb : 0 < b) :
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt q (F (q t)) t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hy_combined_volume] with t hdyn ht
    have hcandidate_dyn := hdyn (Set.mem_Ici.mpr ht.1)
    have hqDA : HasDerivAt q (-lam⁻¹ • (y.2 t + B (y.1 t))) t := by
      have hqfun : q = fun s => lam⁻¹ • (lam • y.1 s + y.2 s) := by
        funext s
        simp only [q, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      have hscaled := hcandidate_dyn.const_smul lam⁻¹
      rw [hqfun]
      convert hscaled using 1
      module
    have hFq : F (q t) = -lam⁻¹ • (y.2 t + B (y.1 t)) := by
      simp only [F, q]
      rw [← hy_prox t ht.1]
      module
    rw [hFq]
    exact hqDA
  have hq_right (b : ℝ) (hb : 0 < b) : ∀ t ∈ Set.Ico 0 b,
      HasDerivWithinAt q (F (q t)) (Set.Ici t) t := by
    have hFq_cont : ContinuousOn (fun t => F (q t)) (Set.Icc 0 b) :=
      hF_continuous.continuousOn.comp (by
        simpa only [Set.uIcc_of_le hb.le] using (hq_ac b hb).continuousOn)
        (fun _ _ => Set.mem_univ _)
    exact ac_hasDerivWithinAt_right_of_ae_hasDerivAt hb.le (hq_ac b hb)
      hFq_cont (hq_dynamics_Icc b hb)
  have hq_eq_z_Icc (b : ℝ) (hb : 0 < b) : Set.EqOn q z (Set.Icc 0 b) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ => F) (s := fun _ => Set.univ) (K := K)
    · intro t ht
      exact hF_lipschitz.lipschitzOnWith
    · simpa only [Set.uIcc_of_le hb.le] using (hq_ac b hb).continuousOn
    · exact hq_right b hb
    · intro t ht
      exact Set.mem_univ _
    · exact hz_continuous.continuousOn
    · intro t ht
      exact (hzderiv t).hasDerivWithinAt
    · intro t ht
      exact Set.mem_univ _
    · exact hq0.trans hz0.symm
  have hq_eq_z (t : ℝ) (ht : 0 ≤ t) : q t = z t := by
    exact hq_eq_z_Icc (t + 1) (by linarith) ⟨ht, by linarith⟩
  have hyx_eq (t : ℝ) (ht : 0 ≤ t) : y.1 t = xt t := by
    rw [show xt t = x t by simp [xt, not_lt.mpr ht], hy_prox t ht, hq_eq_z t ht]
  have hyv_recover (t : ℝ) : y.2 t = lam • (q t - y.1 t) := by
    simp [q]
    rw [smul_smul, mul_inv_cancel₀ hlam.ne']
    module
  have hyv_eq (t : ℝ) (ht : 0 ≤ t) : y.2 t = vt t := by
    rw [hyv_recover t, hq_eq_z t ht]
    have hyx : y.1 t = x t := by
      simpa [xt, not_lt.mpr ht] using hyx_eq t ht
    rw [hyx]
    simp [vt, v, not_lt.mpr ht]
  apply Prod.ext <;> funext t
  · by_cases ht : t < 0
    · simp [hyx_neg t ht, xt, ht]
    · exact hyx_eq t (le_of_not_gt ht)
  · by_cases ht : t < 0
    · simp [hyv_neg t ht, vt, ht]
    · exact hyv_eq t (le_of_not_gt ht)

end AbbasDynamical2015
