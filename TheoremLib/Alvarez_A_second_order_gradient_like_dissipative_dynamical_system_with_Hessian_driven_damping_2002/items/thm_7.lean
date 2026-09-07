import Mathlib
import Foundation.Differentiation.ODE
import Foundation.FixedPoint.Nonexpansive
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_10

namespace Alvarez2002

open Filter
open scoped RealInnerProductSpace

noncomputable def constrainedDINProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ) : H → H :=
  projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex)

noncomputable def constrainedDINPhaseField
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ)
    (β a b : ℝ) : H × H → H × H := fun z =>
  let P := constrainedDINProjection C Φ hC
  let q := P (z.1 - β • gradient Φ (P z.1) - a • z.1 - b • z.2)
  (q - z.1, -(a • z.1) - b • z.2)

private theorem constrainedDINProjection_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ) :
    LipschitzWith 1 (constrainedDINProjection C Φ hC) := by
  exact lipschitzWith_one_of_firmlyNonexpansive
    (firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex
      hC.nonempty hC.closed hC.convex)

@[simp] private theorem constrainedDINProjection_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ) (x : H) :
    constrainedDINProjection C Φ hC x ∈ C := by
  exact projectionPoint_mem C
    (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex) x

theorem constrainedDINProjection_eq_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ) {x : H} (hx : x ∈ C) :
    constrainedDINProjection C Φ hC x = x := by
  symm
  apply eq_projectionPoint_of_isBestApproximation C
    (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex)
  refine ⟨hx, ?_⟩
  simp [Metric.infDist_zero_of_mem hx]

private theorem constrainedDINProjectedGradient_locallyLipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ) :
    LocallyLipschitz (fun x => gradient Φ (constrainedDINProjection C Φ hC x)) := by
  let P := constrainedDINProjection C Φ hC
  have hP : LipschitzWith 1 P := constrainedDINProjection_lipschitz C Φ hC
  intro x
  let R : ℝ := ‖P x‖ + 1
  obtain ⟨L, hL, hgrad⟩ := hC.gradient_lipschitz_on_bounded R
  refine ⟨⟨L, hL⟩, Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hPu : ‖P u‖ ≤ R := by
    calc
      ‖P u‖ ≤ ‖P u - P x‖ + ‖P x‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖u - x‖ + ‖P x‖ := by
        gcongr
        simpa [dist_eq_norm] using hP.dist_le_mul u x
      _ ≤ R := by
        have hu' : ‖u - x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
        dsimp [R]
        linarith
  have hPv : ‖P v‖ ≤ R := by
    calc
      ‖P v‖ ≤ ‖P v - P x‖ + ‖P x‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖v - x‖ + ‖P x‖ := by
        gcongr
        simpa [dist_eq_norm] using hP.dist_le_mul v x
      _ ≤ R := by
        have hv' : ‖v - x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hv
        dsimp [R]
        linarith
  have hg := hgrad (P u) (constrainedDINProjection_mem C Φ hC u)
    (P v) (constrainedDINProjection_mem C Φ hC v) hPu hPv
  calc
    dist (gradient Φ (P u)) (gradient Φ (P v)) =
        ‖gradient Φ (P u) - gradient Φ (P v)‖ := dist_eq_norm _ _
    _ ≤ L * ‖P u - P v‖ := hg
    _ ≤ L * ‖u - v‖ := by
      gcongr
      simpa [dist_eq_norm] using hP.dist_le_mul u v
    _ = (⟨L, hL⟩ : NNReal) * dist u v := by simp [dist_eq_norm]

private theorem constrainedDINPhaseField_locallyLipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ)
    (β a b : ℝ) : LocallyLipschitz (constrainedDINPhaseField C Φ hC β a b) := by
  let P := constrainedDINProjection C Φ hC
  have hP : LocallyLipschitz P :=
    (constrainedDINProjection_lipschitz C Φ hC).locallyLipschitz
  have hg : LocallyLipschitz (fun x => gradient Φ (P x)) :=
    constrainedDINProjectedGradient_locallyLipschitz C Φ hC
  have hfst : LocallyLipschitz (Prod.fst : H × H → H) :=
    LipschitzWith.prod_fst.locallyLipschitz
  have hsnd : LocallyLipschitz (Prod.snd : H × H → H) :=
    LipschitzWith.prod_snd.locallyLipschitz
  let Lβ : H →L[ℝ] H := β • ContinuousLinearMap.id ℝ H
  let La : H →L[ℝ] H := a • ContinuousLinearMap.id ℝ H
  let Lb : H →L[ℝ] H := b • ContinuousLinearMap.id ℝ H
  have hβg : LocallyLipschitz (fun z : H × H => β • gradient Φ (P z.1)) := by
    simpa [Lβ, Function.comp_def] using
      Lβ.lipschitz.locallyLipschitz.comp (hg.comp hfst)
  have hax : LocallyLipschitz (fun z : H × H => a • z.1) := by
    simpa [La, Function.comp_def] using La.lipschitz.locallyLipschitz.comp hfst
  have hby : LocallyLipschitz (fun z : H × H => b • z.2) := by
    simpa [Lb, Function.comp_def] using Lb.lipschitz.locallyLipschitz.comp hsnd
  have harg : LocallyLipschitz
      (fun z : H × H => z.1 - β • gradient Φ (P z.1) - a • z.1 - b • z.2) := by
    exact ((hfst.sub hβg).sub hax).sub hby
  have hfirst : LocallyLipschitz (fun z : H × H =>
      P (z.1 - β • gradient Φ (P z.1) - a • z.1 - b • z.2) - z.1) :=
    (hP.comp harg).sub hfst
  have hsecond : LocallyLipschitz (fun z : H × H => -(a • z.1) - b • z.2) :=
    hax.neg.sub hby
  change LocallyLipschitz (fun z : H × H =>
    (P (z.1 - β • gradient Φ (P z.1) - a • z.1 - b • z.2) - z.1,
      -(a • z.1) - b • z.2))
  exact hfirst.prodMk hsecond

private theorem constrainedDIN_variation_of_constants
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (t : ℝ) (x p : ℝ → H) (ht : 0 ≤ t)
    (hp : ContinuousOn p (Set.Icc 0 t))
    (hderiv : ∀ s, s ∈ Set.Icc 0 t → HasDerivAt x (p s - x s) s) :
    x t = Real.exp (-t) • x 0 +
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
  have hderiv' : ∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun u : ℝ => Real.exp u • x u) (Real.exp s • p s) s := by
    intro s hs
    (convert (Real.hasDerivAt_exp s).smul (hderiv s hs) using 1 ; module)
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp s • p s)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0 t := by
    have hp' : ContinuousOn p (Set.uIcc 0 t) := by
      simpa only [Set.uIcc_of_le ht] using hp
    exact (Real.continuous_exp.continuousOn.smul hp').intervalIntegrable
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := fun s : ℝ => Real.exp s • x s)
    (f' := fun s : ℝ => Real.exp s • p s)
    (fun s hs => hderiv' s (by simpa [Set.uIcc_of_le ht] using hs)) hint
  have hscaled := congrArg (fun z : H => Real.exp (-t) • z) hfund
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) =
      Real.exp (-t) • ∫ s in 0..t, Real.exp s • p s := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul, ← Real.exp_add]
    congr 2
    ring
  have hsub : x t - Real.exp (-t) • x 0 =
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
    rw [hkernel]
    have hexp : Real.exp (-t) * Real.exp t = 1 := by simp [Real.exp_neg]
    simpa [smul_sub, smul_smul, hexp] using hscaled.symm
  simpa [add_comm] using eq_add_of_sub_eq hsub

private theorem constrainedDIN_exp_average_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (C : Set H) (p : ℝ → H) (t : ℝ) (ht : 0 < t) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (hp : ContinuousOn p (Set.Icc 0 t))
    (hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C) :
    (Real.exp t - 1)⁻¹ • (∫ s in 0..t, Real.exp s • p s) ∈ C := by
  let I : Set ℝ := Set.Icc 0 t
  let μI : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict I
  let ρ : ℝ → ENNReal := fun s => ENNReal.ofReal (Real.exp s)
  let ν : MeasureTheory.Measure ℝ := μI.withDensity ρ
  have hscalar : MeasureTheory.Integrable (fun s : ℝ => Real.exp s) μI := by
    change MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp s) I
    exact Real.continuous_exp.continuousOn.integrableOn_Icc
  have hρmeas : Measurable ρ := by
    dsimp [ρ]
    fun_prop
  have hρtop : ∀ᵐ s ∂μI, ρ s < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  letI : MeasureTheory.IsFiniteMeasure ν := by
    dsimp [ν, ρ]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hscalar.hasFiniteIntegral
  have hmassI : ∫ s in I, Real.exp s = Real.exp t - 1 := by
    dsimp [I]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.le]
    simp
  have hνmass : ν.real Set.univ = Real.exp t - 1 := by
    rw [MeasureTheory.measureReal_def, show ν = μI.withDensity ρ from rfl,
      MeasureTheory.withDensity_apply ρ MeasurableSet.univ]
    rw [MeasureTheory.setLIntegral_univ]
    change ENNReal.toReal (∫⁻ s, ENNReal.ofReal (Real.exp s) ∂μI) = _
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hscalar]
    · change ENNReal.toReal (ENNReal.ofReal (∫ s in I, Real.exp s)) = _
      rw [hmassI]
      rw [ENNReal.toReal_ofReal
        (le_of_lt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)))]
    · filter_upwards with s
      exact Real.exp_nonneg s
  have hmasspos : 0 < Real.exp t - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hνne : ν ≠ 0 := by
    intro hzero
    have hzero' : ν.real Set.univ = 0 := by simp [hzero]
    linarith [hνmass]
  letI : NeZero ν := ⟨hνne⟩
  have hwp : MeasureTheory.Integrable (fun s => Real.exp s • p s) μI := by
    change MeasureTheory.IntegrableOn (fun s => Real.exp s • p s) I
    exact (Real.continuous_exp.continuousOn.smul hp).integrableOn_Icc
  have hpν : MeasureTheory.Integrable p ν := by
    rw [show ν = μI.withDensity ρ from rfl,
      MeasureTheory.integrable_withDensity_iff_integrable_smul' hρmeas hρtop]
    simpa [ρ, ENNReal.toReal_ofReal, Real.exp_nonneg] using hwp
  have hpmemν : ∀ᵐ s ∂ν, p s ∈ C := by
    rw [show ν = μI.withDensity ρ from rfl,
      MeasureTheory.ae_withDensity_iff hρmeas]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs _
    exact hpmem s (by simpa [I] using hs)
  have hqC : ⨍ s, p s ∂ν ∈ C := hconvex.average_mem hclosed hpmemν hpν
  have hνintegral : (∫ s, p s ∂ν) = ∫ s in 0..t, Real.exp s • p s := by
    rw [show ν = μI.withDensity ρ from rfl,
      integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
    change (∫ s in I, (ρ s).toReal • p s) = _
    simp only [ρ, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.le]
  rw [MeasureTheory.average_eq, hνmass, hνintegral] at hqC
  exact hqC

private theorem constrainedDIN_viable_of_relaxed_derivative
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (C : Set H) (x p : ℝ → H) (t : ℝ) (ht : 0 ≤ t) (hx0 : x 0 ∈ C)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hp : ContinuousOn p (Set.Icc 0 t))
    (hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C)
    (hderiv : ∀ s, s ∈ Set.Icc 0 t → HasDerivAt x (p s - x s) s) : x t ∈ C := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hx0
  have hformula := constrainedDIN_variation_of_constants t x p ht.le hp hderiv
  let A : H := ∫ s in 0..t, Real.exp s • p s
  let q : H := (Real.exp t - 1)⁻¹ • A
  have hqC : q ∈ C := by
    simpa [q, A] using
      constrainedDIN_exp_average_mem C p t ht hclosed hconvex hp hpmem
  have hexp : Real.exp (-t) * Real.exp t = 1 := by simp [Real.exp_neg]
  have hdenom : Real.exp t - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hcoeff : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    nlinarith [hexp]
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) =
      Real.exp (-t) • A := by
    dsimp [A]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul, ← Real.exp_add]
    congr 2
    ring
  have hline : x t = (AffineMap.lineMap (x 0) q) (1 - Real.exp (-t)) := by
    rw [hformula, hkernel, AffineMap.lineMap_apply]
    dsimp [q]
    rw [smul_sub, smul_smul, hcoeff]
    field_simp
    rw [← hcoeff]
    module
  apply hline ▸ hconvex.lineMap_mem hx0 hqC
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
  · linarith [Real.exp_pos (-t)]

private theorem constrainedDIN_variation_of_constants_interior
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (t : ℝ) (x p : ℝ → H) (ht : 0 ≤ t)
    (hx : ContinuousOn x (Set.Icc 0 t)) (hp : ContinuousOn p (Set.Icc 0 t))
    (hderiv : ∀ s, s ∈ Set.Ioo 0 t → HasDerivAt x (p s - x s) s) :
    x t = Real.exp (-t) • x 0 +
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
  have hweighted : ContinuousOn (fun s : ℝ => Real.exp s • x s) (Set.Icc 0 t) :=
    Real.continuous_exp.continuousOn.smul hx
  have hderiv' : ∀ s ∈ Set.Ioo 0 t,
      HasDerivWithinAt (fun u : ℝ => Real.exp u • x u) (Real.exp s • p s)
        (Set.Ioi s) s := by
    intro s hs
    have h := (Real.hasDerivAt_exp s).smul (hderiv s hs)
    (convert h.hasDerivWithinAt using 1 ; module)
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp s • p s)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0 t :=
    (Real.continuous_exp.continuousOn.smul hp).intervalIntegrable_of_Icc ht
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hweighted
    hderiv' hint
  have hscaled := congrArg (fun z : H => Real.exp (-t) • z) hfund
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) =
      Real.exp (-t) • ∫ s in 0..t, Real.exp s • p s := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul, ← Real.exp_add]
    congr 2
    ring
  have hsub : x t - Real.exp (-t) • x 0 =
      ∫ s in 0..t, Real.exp (-(t - s)) • p s := by
    rw [hkernel]
    have hexp : Real.exp (-t) * Real.exp t = 1 := by simp [Real.exp_neg]
    simpa [smul_sub, smul_smul, hexp] using hscaled.symm
  simpa [add_comm] using eq_add_of_sub_eq hsub

private theorem constrainedDIN_viable_of_relaxed_derivative_interior
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (C : Set H) (x p : ℝ → H) (t : ℝ) (ht : 0 ≤ t) (hx0 : x 0 ∈ C)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hx : ContinuousOn x (Set.Icc 0 t)) (hp : ContinuousOn p (Set.Icc 0 t))
    (hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C)
    (hderiv : ∀ s, s ∈ Set.Ioo 0 t → HasDerivAt x (p s - x s) s) : x t ∈ C := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hx0
  have hformula :=
    constrainedDIN_variation_of_constants_interior t x p ht.le hx hp hderiv
  let A : H := ∫ s in 0..t, Real.exp s • p s
  let q : H := (Real.exp t - 1)⁻¹ • A
  have hqC : q ∈ C := by
    simpa [q, A] using
      constrainedDIN_exp_average_mem C p t ht hclosed hconvex hp hpmem
  have hexp : Real.exp (-t) * Real.exp t = 1 := by simp [Real.exp_neg]
  have hdenom : Real.exp t - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hcoeff : 1 - Real.exp (-t) = Real.exp (-t) * (Real.exp t - 1) := by
    nlinarith [hexp]
  have hkernel : (∫ s in 0..t, Real.exp (-(t - s)) • p s) =
      Real.exp (-t) • A := by
    dsimp [A]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-(t - s)) • p s = Real.exp (-t) • (Real.exp s • p s)
    rw [← mul_smul, ← Real.exp_add]
    congr 2
    ring
  have hline : x t = (AffineMap.lineMap (x 0) q) (1 - Real.exp (-t)) := by
    rw [hformula, hkernel, AffineMap.lineMap_apply]
    dsimp [q]
    rw [smul_sub, smul_smul, hcoeff]
    field_simp
    rw [← hcoeff]
    module
  apply hline ▸ hconvex.lineMap_mem hx0 hqC
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le))
  · linarith [Real.exp_pos (-t)]

private theorem constrainedDIN_norm_sub_le_of_hasDerivAt_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s t M : ℝ} {u du : ℝ → H} (hst : s ≤ t)
    (hdu : ∀ r, s ≤ r → r ≤ t → HasDerivAt u (du r) r)
    (hbound : ∀ r, s ≤ r → r ≤ t → ‖du r‖ ≤ M) :
    ‖u t - u s‖ ≤ M * (t - s) := by
  have hcont : ContinuousOn u (Set.Icc s t) := by
    intro r hr
    exact (hdu r hr.1 hr.2).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ u (Set.Ioo s t) := by
    intro r hr
    exact (hdu r hr.1.le hr.2.le).differentiableAt.differentiableWithinAt
  have hderiv_bound : ∀ᵐ r : ℝ, r ∈ Set.Ioo s t → ‖deriv u r‖ ≤ M := by
    filter_upwards [] with r hr
    simpa [(hdu r hr.1.le hr.2.le).deriv] using hbound r hr.1.le hr.2.le
  calc
    ‖u t - u s‖ ≤ ∫ r in s..t, M :=
      norm_sub_le_integral_of_norm_deriv_le_of_le hst hcont hdiff hderiv_bound
        intervalIntegrable_const
    _ = M * (t - s) := by simp [mul_comm]

private theorem constrainedDIN_contDiffOn_one_of_hasDerivAt_of_continuousOn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f f' : ℝ → H} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' s) : ContDiffOn ℝ 1 f s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact (contDiffOn_zero.mpr hf').congr heq

private theorem constrainedDIN_contDiffOn_two_of_hasDerivAt_of_contDiffOn_one
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f f' : ℝ → H} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContDiffOn ℝ 1 f' s) : ContDiffOn ℝ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact hf'.congr heq

private theorem constrainedDIN_hasDerivWithinAt_zero_of_contDiffOn_one
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f g : ℝ → H} (hf : ContDiffOn ℝ 1 f (Set.Ici 0))
    (hg : ContinuousOn g (Set.Ici 0))
    (hode : ∀ t, 0 < t → HasDerivAt f (g t) t) :
    HasDerivWithinAt f (g 0) (Set.Ici 0) 0 := by
  have hsplit := (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mp
    (show ContDiffOn ℝ (0 + 1) f (Set.Ici 0) by simpa using hf)
  have hdcont : ContinuousOn (derivWithin f (Set.Ici 0)) (Set.Ici 0) :=
    hsplit.2.2.continuousOn
  have hdlim : Tendsto (derivWithin f (Set.Ici 0))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (derivWithin f (Set.Ici 0) 0)) :=
    (hdcont 0 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self
  have hglim : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
    (hg 0 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self
  have heq : derivWithin f (Set.Ici 0) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact (hode t ht).deriv
  have hval : derivWithin f (Set.Ici 0) 0 = g 0 :=
    tendsto_nhds_unique_of_eventuallyEq hdlim hglim heq
  rw [← hval]
  exact (hsplit.1 0 (Set.mem_Ici.mpr le_rfl)).hasDerivWithinAt

theorem constrainedDIN_energy_dissipation_at
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (Φ : H → ℝ) (hC : ConstrainedHypothesis C Φ)
    (β a b : ℝ) (hβ : 0 < β) (hb : 0 < b) (hab : 0 < b + a)
    (Y : ℝ → H × H) {t : ℝ}
    (hY : HasDerivAt Y (constrainedDINPhaseField C Φ hC β a b (Y t)) t)
    (hxC : (Y t).1 ∈ C) :
    let u := (constrainedDINPhaseField C Φ hC β a b (Y t)).1
    let v := (constrainedDINPhaseField C Φ hC β a b (Y t)).2
    let lam := β * (a + 2 * b)
    let E := fun s => lam * Φ (Y s).1 + (1 / 2) * ‖a • (Y s).1 + b • (Y s).2‖ ^ 2
    let E' := lam * inner ℝ (gradient Φ (Y t).1) u -
      a * inner ℝ u v - b * ‖v‖ ^ 2
    HasDerivAt E E' t ∧ E' + (a + b) * ‖u‖ ^ 2 + b * ‖u - v‖ ^ 2 ≤ 0 := by
  dsimp only
  let P := constrainedDINProjection C Φ hC
  let z : H := (Y t).1 - β • gradient Φ (P (Y t).1) - a • (Y t).1 - b • (Y t).2
  let p : H := P z
  let u : H := p - (Y t).1
  let v : H := -(a • (Y t).1) - b • (Y t).2
  have hfield : constrainedDINPhaseField C Φ hC β a b (Y t) = (u, v) := by
    rfl
  have hxf : HasDerivAt (fun s => (Y s).1) u t := by
    have h := hY.hasFDerivAt.fst.hasDerivAt
    simpa [hfield] using h
  have hyf : HasDerivAt (fun s => (Y s).2) v t := by
    have h := hY.hasFDerivAt.snd.hasDerivAt
    simpa [hfield] using h
  rcases hC.continuously_differentiable_on_neighborhood with ⟨U, hUopen, hCU, hΦU⟩
  have hΦdiffWithin :=
    hΦU.differentiableOn (by norm_num) (Y t).1 (hCU hxC)
  have hΦdiff : DifferentiableAt ℝ Φ (Y t).1 :=
    hΦdiffWithin.differentiableAt (hUopen.mem_nhds (hCU hxC))
  have hΦcurve : HasDerivAt (fun s => Φ (Y s).1)
      (inner ℝ (gradient Φ (Y t).1) u) t := by
    simpa using
      (hΦdiff.hasGradientAt.hasFDerivAt.comp t hxf.hasFDerivAt).hasDerivAt
  have hq : HasDerivAt (fun s => a • (Y s).1 + b • (Y s).2)
      (a • u + b • v) t := (hxf.const_smul a).add (hyf.const_smul b)
  have hE := (hΦcurve.const_mul (β * (a + 2 * b))).add
    (hq.norm_sq.const_mul (1 / 2 : ℝ))
  have hqv : a • (Y t).1 + b • (Y t).2 = -v := by
    dsimp [v]
    module
  have hE' : HasDerivAt
      (fun s => β * (a + 2 * b) * Φ (Y s).1 +
        (1 / 2) * ‖a • (Y s).1 + b • (Y s).2‖ ^ 2)
      (β * (a + 2 * b) * inner ℝ (gradient Φ (Y t).1) u -
        a * inner ℝ u v - b * ‖v‖ ^ 2) t := by
    convert hE using 1
    rw [hqv]
    rw [inner_neg_left, inner_add_right]
    rw [real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm v u]
    ring
  refine ⟨hE', ?_⟩
  have hPx : P (Y t).1 = (Y t).1 := constrainedDINProjection_eq_self C Φ hC hxC
  have hchar : inner ℝ ((Y t).1 - p) (z - p) ≤ 0 := by
    have hpchar :=
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC.nonempty hC.closed hC.convex).mp
        (show p = constrainedDINProjection C Φ hC z from rfl)
    exact hpchar.2 (Y t).1 hxC
  have hproj : β * inner ℝ u (gradient Φ (Y t).1) ≤
      -‖u‖ ^ 2 + inner ℝ u v := by
    have hz : z - p = -β • gradient Φ (Y t).1 + v - u := by
      dsimp [z]
      rw [hPx]
      dsimp [u, v]
      module
    have hxp : (Y t).1 - p = -u := by
      dsimp [u]
      module
    rw [hxp, hz, inner_neg_left] at hchar
    simp only [inner_sub_right, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq] at hchar
    nlinarith
  have hβnonneg : 0 ≤ β := hβ.le
  have hscaled := mul_le_mul_of_nonneg_left hproj (show 0 ≤ a + 2 * b by linarith)
  rw [← mul_assoc] at hscaled
  rw [hfield]
  have hgu : inner ℝ (gradient Φ (Y t).1) u =
      inner ℝ u (gradient Φ (Y t).1) := real_inner_comm _ _
  have hnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
    rw [norm_sub_sq_real]
    ring
  rw [hgu, hnorm]
  nlinarith

private theorem constrainedDIN_integrableOn_Ici_of_nonneg_interval_bound
    {g : ℝ → ℝ} {a K : ℝ}
    (hlocal : ∀ T, MeasureTheory.IntegrableOn g (Set.Ioc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s)
    (hbound : ∀ T, a ≤ T → ∫ s in a..T, g s ≤ K) :
    MeasureTheory.IntegrableOn g (Set.Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded K a hlocal
    Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop a] with T hT
  have hnorm : (∫ s in a..T, ‖g s‖) = ∫ s in a..T, g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hT] at hs
    exact Real.norm_of_nonneg (hnonneg s hs.1.le)
  rw [hnorm]
  exact hbound T hT

/-- Theorem 7.1(i): global existence, uniqueness, regularity, and viability for `(c-DIN)`. -/
theorem constrained_din_global_properties_part_i {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (hβ : 0 < β) (ha : a ≠ 0) (hb : 0 < b) (hab : 0 < b + a)
  (x₀ y₀ : H) (hx₀ : x₀ ∈ C) :
  ∃ x y : ℝ → H,
    IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y ∧
    ContDiffOn ℝ 1 x (Set.Ici 0) ∧
    ContDiffOn ℝ 2 y (Set.Ici 0) ∧
    (∀ t, 0 ≤ t → x t ∈ C) ∧
    ∀ x' y',
      IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x' y' →
      ContDiffOn ℝ 1 x' (Set.Ici 0) ∧ ContDiffOn ℝ 2 y' (Set.Ici 0) →
      Set.EqOn x' x (Set.Ici 0) ∧ Set.EqOn y' y (Set.Ici 0) := by
  let F : H × H → H × H := constrainedDINPhaseField C Φ hC β a b
  have hFloc : LocallyLipschitz F :=
    constrainedDINPhaseField_locallyLipschitz C Φ hC β a b
  have hFcont : Continuous F := hFloc.continuous
  have hFnhds : ∀ z, ∃ U ∈ nhds z, ∃ L : ℝ, 0 ≤ L ∧
      ∀ p ∈ U, ∀ q ∈ U, ‖F p - F q‖ ≤ L * ‖p - q‖ := by
    intro z
    rcases hFloc z with ⟨K, U, hU, hKU⟩
    refine ⟨U, hU, K, K.coe_nonneg, ?_⟩
    intro p hp q hq
    simpa only [dist_eq_norm] using hKU.dist_le_mul p hp q hq
  obtain ⟨Tmax, Y, hYmax, hYunique, hYextend⟩ :=
    cauchy_lipschitz_continuation F (x₀, y₀) hFnhds
  have hYlocal (t : ℝ) (ht : 0 ≤ t) (htT : (t : WithTop ℝ) < Tmax) :
      HasDerivAt Y (F (Y t)) t := hYmax.2.1.2.2 t ⟨ht, htT⟩
  have hviable (t : ℝ) (ht : 0 ≤ t) (htT : (t : WithTop ℝ) < Tmax) :
      (Y t).1 ∈ C := by
    let p : ℝ → H := fun s => (F (Y s)).1 + (Y s).1
    have hYcont : ContinuousOn Y (Set.Icc 0 t) := by
      intro s hs
      exact (hYlocal s hs.1 (lt_of_le_of_lt (by exact_mod_cast hs.2) htT)).continuousAt
        |>.continuousWithinAt
    have hpcont : ContinuousOn p (Set.Icc 0 t) := by
      have hFYcont : ContinuousOn (fun s => F (Y s)) (Set.Icc 0 t) := by
        simpa only [Function.comp_def] using hFcont.comp_continuousOn hYcont
      exact hFYcont.fst.add hYcont.fst
    have hpmem : ∀ s, s ∈ Set.Icc 0 t → p s ∈ C := by
      intro s hs
      dsimp [p, F, constrainedDINPhaseField]
      simpa only [sub_add_cancel] using
        (constrainedDINProjection_mem C Φ hC
          ((Y s).1 - β • gradient Φ (constrainedDINProjection C Φ hC (Y s).1) -
            a • (Y s).1 - b • (Y s).2))
    have hxderiv : ∀ s, s ∈ Set.Icc 0 t →
        HasDerivAt (fun r => (Y r).1) (p s - (Y s).1) s := by
      intro s hs
      have h := (hYlocal s hs.1
        (lt_of_le_of_lt (by exact_mod_cast hs.2) htT)).hasFDerivAt.fst.hasDerivAt
      convert h using 1
      dsimp [p]
      module
    have hxinit : (Y 0).1 ∈ C := by
      rw [hYmax.2.1.2.1]
      exact hx₀
    exact constrainedDIN_viable_of_relaxed_derivative C (fun s => (Y s).1) p t ht
      hxinit hC.closed hC.convex hpcont hpmem hxderiv
  have hTtop : Tmax = (⊤ : WithTop ℝ) := by
    by_contra hnot
    obtain ⟨T, hTmax'⟩ := (WithTop.ne_top_iff_exists).mp hnot
    have hTmax : Tmax = (T : WithTop ℝ) := hTmax'.symm
    have hTpos : 0 < T := by simpa [hTmax] using hYmax.1
    obtain ⟨m, hm⟩ := hC.bounded_below
    let lam : ℝ := β * (a + 2 * b)
    let u : ℝ → H := fun s => (F (Y s)).1
    let v : ℝ → H := fun s => (F (Y s)).2
    let q : ℝ → H := fun s => a • (Y s).1 + b • (Y s).2
    let E : ℝ → ℝ := fun s => lam * Φ (Y s).1 + (1 / 2) * ‖q s‖ ^ 2
    let E' : ℝ → ℝ := fun s =>
      lam * inner ℝ (gradient Φ (Y s).1) (u s) -
        a * inner ℝ (u s) (v s) - b * ‖v s‖ ^ 2
    have hlam : 0 < lam := by
      dsimp [lam]
      exact mul_pos hβ (by linarith)
    have hEdata (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) :
        HasDerivAt E (E' s) s ∧
          E' s + (a + b) * ‖u s‖ ^ 2 + b * ‖u s - v s‖ ^ 2 ≤ 0 := by
      simpa [E, E', q, u, v, lam, F] using
        constrainedDIN_energy_dissipation_at C Φ hC β a b hβ hb
          (by linarith) Y
          (hYlocal s hs0 (by simpa [hTmax] using hsT))
          (hviable s hs0 (by simpa [hTmax] using hsT))
    have hEanti : AntitoneOn E (Set.Ico 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ico 0 T)
      · intro s hs
        exact (hEdata s hs.1 hs.2).1.continuousAt.continuousWithinAt
      · intro s hs
        have hs' : s ∈ Set.Ico 0 T := interior_subset hs
        exact (hEdata s hs'.1 hs'.2).1.differentiableAt.differentiableWithinAt
      · intro s hs
        have hs' : s ∈ Set.Ico 0 T := interior_subset hs
        have hd := hEdata s hs'.1 hs'.2
        rw [hd.1.deriv]
        nlinarith [mul_nonneg (by linarith : 0 ≤ a + b) (sq_nonneg ‖u s‖),
          mul_nonneg hb.le (sq_nonneg ‖u s - v s‖)]
    have hxzeroC : (Y 0).1 ∈ C := by
      rw [hYmax.2.1.2.1]
      exact hx₀
    have hEzeroLower : lam * m ≤ E 0 := by
      have hphi := hm (Y 0).1 hxzeroC
      dsimp [E]
      nlinarith [mul_le_mul_of_nonneg_left hphi hlam.le, sq_nonneg ‖q 0‖]
    let Q : ℝ := 2 * (E 0 - lam * m) + 1
    have hQpos : 0 < Q := by
      dsimp [Q]
      linarith
    have hqbound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) : ‖q s‖ ≤ Q := by
      have hanti := hEanti ⟨le_rfl, hTpos⟩ ⟨hs0, hsT⟩ hs0
      have hphi := hm (Y s).1
        (hviable s hs0 (by simpa [hTmax] using hsT))
      have hphis := mul_le_mul_of_nonneg_left hphi hlam.le
      have hsq : ‖q s‖ ^ 2 ≤ 2 * (E 0 - lam * m) := by
        dsimp [E] at hanti ⊢
        nlinarith
      dsimp [Q]
      nlinarith [sq_nonneg (‖q s‖ - 1 / 2), norm_nonneg (q s)]
    have hv_eq (s : ℝ) : v s = -q s := by
      dsimp [v, q, F, constrainedDINPhaseField]
      module
    let Ry : ℝ := Q * T + ‖y₀‖
    have hRy : 0 ≤ Ry := by
      dsimp [Ry]
      positivity
    have hybound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) : ‖(Y s).2‖ ≤ Ry := by
      have hydist : ‖(Y s).2 - (Y 0).2‖ ≤ Q * (s - 0) := by
        apply constrainedDIN_norm_sub_le_of_hasDerivAt_bound hs0
        · intro r hr0 hrs
          have hrT : r < T := lt_of_le_of_lt hrs hsT
          have hd := (hYlocal r hr0
            (by simpa [hTmax] using hrT)).hasFDerivAt.snd.hasDerivAt
          simpa [v, hv_eq r] using hd
        · intro r hr0 hrs
          have hrT : r < T := lt_of_le_of_lt hrs hsT
          simpa only [norm_neg] using hqbound r hr0 hrT
      have hyzero : (Y 0).2 = y₀ := by
        rw [hYmax.2.1.2.1]
      rw [hyzero] at hydist
      calc
        ‖(Y s).2‖ ≤ ‖(Y s).2 - (Y 0).2‖ + ‖(Y 0).2‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ Q * s + ‖y₀‖ := by
          rw [hyzero]
          simpa using add_le_add_right hydist ‖y₀‖
        _ ≤ Q * T + ‖y₀‖ := by
          gcongr
        _ = Ry := rfl
    let Rx : ℝ := |a|⁻¹ * (Q + |b| * Ry)
    have hRx : 0 ≤ Rx := by
      dsimp [Rx]
      positivity
    have hxbound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) : ‖(Y s).1‖ ≤ Rx := by
      have hax : a • (Y s).1 = q s - b • (Y s).2 := by
        dsimp [q]
        module
      calc
        ‖(Y s).1‖ = |a|⁻¹ * ‖a • (Y s).1‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          field_simp [abs_ne_zero.mpr ha]
        _ = |a|⁻¹ * ‖q s - b • (Y s).2‖ := by rw [hax]
        _ ≤ |a|⁻¹ * (‖q s‖ + |b| * ‖(Y s).2‖) := by
          gcongr
          simpa [norm_smul, Real.norm_eq_abs] using norm_sub_le (q s) (b • (Y s).2)
        _ ≤ |a|⁻¹ * (Q + |b| * Ry) := by
          gcongr
          · exact hqbound s hs0 hsT
          · exact hybound s hs0 hsT
        _ = Rx := rfl
    obtain ⟨L, hL, hgrad⟩ := hC.gradient_lipschitz_on_bounded Rx
    let G : ℝ := L * (2 * Rx) + ‖gradient Φ x₀‖
    have hG : 0 ≤ G := by
      dsimp [G]
      positivity
    have hgradbound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) :
        ‖gradient Φ (Y s).1‖ ≤ G := by
      have hx0eq : (Y 0).1 = x₀ := by rw [hYmax.2.1.2.1]
      have hx0bound : ‖x₀‖ ≤ Rx := by
        rw [← hx0eq]
        exact hxbound 0 le_rfl hTpos
      have hdiff := hgrad (Y s).1
        (hviable s hs0 (by simpa [hTmax] using hsT)) x₀ hx₀
        (hxbound s hs0 hsT) hx0bound
      calc
        ‖gradient Φ (Y s).1‖ ≤
            ‖gradient Φ (Y s).1 - gradient Φ x₀‖ + ‖gradient Φ x₀‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ L * ‖(Y s).1 - x₀‖ + ‖gradient Φ x₀‖ :=
          add_le_add hdiff le_rfl
        _ ≤ L * (2 * Rx) + ‖gradient Φ x₀‖ := by
          gcongr
          calc
            ‖(Y s).1 - x₀‖ ≤ ‖(Y s).1‖ + ‖x₀‖ := norm_sub_le _ _
            _ ≤ 2 * Rx := by nlinarith [hxbound s hs0 hsT, hx0bound]
        _ = G := rfl
    let U : ℝ := |β| * G + Q
    have hU : 0 ≤ U := by
      dsimp [U]
      positivity
    have hubound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) : ‖u s‖ ≤ U := by
      let P := constrainedDINProjection C Φ hC
      let z : H := (Y s).1 - β • gradient Φ (Y s).1 -
        a • (Y s).1 - b • (Y s).2
      have hxC := hviable s hs0 (by simpa [hTmax] using hsT)
      have hPx : P (Y s).1 = (Y s).1 := constrainedDINProjection_eq_self C Φ hC hxC
      have huform : u s = P z - (Y s).1 := by
        dsimp [u, F, constrainedDINPhaseField, z, P]
        rw [constrainedDINProjection_eq_self C Φ hC hxC]
      rw [huform, ← hPx]
      calc
        ‖P z - P (Y s).1‖ ≤ ‖z - (Y s).1‖ := by
          simpa using (constrainedDINProjection_lipschitz C Φ hC).norm_sub_le z (Y s).1
        _ = ‖-β • gradient Φ (Y s).1 - q s‖ := by
          congr 1
          dsimp [z, q]
          module
        _ ≤ ‖-β • gradient Φ (Y s).1‖ + ‖q s‖ := norm_sub_le _ _
        _ ≤ |β| * G + Q := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg]
          gcongr
          · exact hgradbound s hs0 hsT
          · exact hqbound s hs0 hsT
        _ = U := rfl
    let M : ℝ := U + Q
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hFbound (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) : ‖F (Y s)‖ ≤ M := by
      change ‖(u s, v s)‖ ≤ M
      rw [Prod.norm_def]
      apply max_le
      · exact (hubound s hs0 hsT).trans (by dsimp [M]; linarith [hQpos])
      · rw [hv_eq, norm_neg]
        exact (hqbound s hs0 hsT).trans (by dsimp [M]; linarith [hU])
    obtain ⟨l, hlim⟩ := tendsto_at_right_of_norm_deriv_le hTpos hM
      (fun s hs0 hsT => hYlocal s hs0 (by simpa [hTmax] using hsT)) hFbound
    have hdomain : Set.Ico 0 T = {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < Tmax} := by
      ext s
      simp [hTmax]
    obtain ⟨S, hTS, Z, hZ, hZY⟩ := hYextend T hTmax l (hdomain ▸ hlim)
    have hsub : {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < Tmax} ⊆ Set.Ico 0 S := by
      intro s hs
      refine ⟨hs.1, ?_⟩
      have hsT : s < T := by simpa [hTmax] using hs.2
      exact hsT.trans hTS
    have hmax := hYmax.2.2 (Set.Ico 0 S) Z Set.ordConnected_Ico
      ⟨le_rfl, hTpos.trans hTS⟩ hZ hsub
      (fun s hs0 hsT => (hZY s hs0 (by simpa [hTmax] using hsT)).symm)
    have hTin : T ∈ Set.Ico 0 S ∩ Set.Ici 0 := ⟨⟨hTpos.le, hTS⟩, hTpos.le⟩
    have hbad := hmax hTin
    exact (lt_irrefl T) (by simpa [hTmax] using hbad.2)
  have hYglobal (t : ℝ) (ht : 0 ≤ t) : HasDerivAt Y (F (Y t)) t :=
    hYlocal t ht (by simp [hTtop])
  have hviable_global (t : ℝ) (ht : 0 ≤ t) : (Y t).1 ∈ C :=
    hviable t ht (by simp [hTtop])
  let x : ℝ → H := fun t => (Y t).1
  let y : ℝ → H := fun t => (Y t).2
  have hxderiv (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivAt x ((F (Y t)).1) t := by
    simpa [x] using (hYglobal t ht).hasFDerivAt.fst.hasDerivAt
  have hyderiv (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivAt y ((F (Y t)).2) t := by
    simpa [y] using (hYglobal t ht).hasFDerivAt.snd.hasDerivAt
  have hYcontIci : ContinuousOn Y (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hYglobal t ht).continuousAt.continuousWithinAt
  have hFYcontIci : ContinuousOn (fun t => F (Y t)) (Set.Ici (0 : ℝ)) := by
    simpa only [Function.comp_def] using hFcont.comp_continuousOn hYcontIci
  have hxC1 : ContDiffOn ℝ 1 x (Set.Ici 0) :=
    constrainedDIN_contDiffOn_one_of_hasDerivAt_of_continuousOn
      (uniqueDiffOn_Ici 0) hxderiv hFYcontIci.fst
  have hyC1 : ContDiffOn ℝ 1 y (Set.Ici 0) :=
    constrainedDIN_contDiffOn_one_of_hasDerivAt_of_continuousOn
      (uniqueDiffOn_Ici 0) hyderiv hFYcontIci.snd
  have hyprimeC1 : ContDiffOn ℝ 1 (fun t => -(a • x t) - b • y t) (Set.Ici 0) :=
    (hxC1.const_smul a).neg.sub (hyC1.const_smul b)
  have hyderiv' (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivAt y (-(a • x t) - b • y t) t := by
    simpa [F, constrainedDINPhaseField, x, y] using hyderiv t ht
  have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) :=
    constrainedDIN_contDiffOn_two_of_hasDerivAt_of_contDiffOn_one
      (uniqueDiffOn_Ici 0) hyderiv' hyprimeC1
  have hxy : IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y := by
    refine ⟨hβ, ha, hb, hab, ?_, hx₀, ?_, ?_⟩
    · dsimp [x]
      rw [hYmax.2.1.2.1]
    · dsimp [y]
      rw [hYmax.2.1.2.1]
    · intro t ht
      have hxC := hviable_global t ht
      have hxd := hxderiv t ht
      have hyd := hyderiv t ht
      constructor
      · let P := constrainedDINProjection C Φ hC
        have hPx : P (Y t).1 = (Y t).1 :=
          constrainedDINProjection_eq_self C Φ hC hxC
        have hfirst : (F (Y t)).1 =
            P ((Y t).1 - β • gradient Φ (Y t).1 - a • (Y t).1 - b • (Y t).2) -
              (Y t).1 := by
          dsimp [F, constrainedDINPhaseField, P]
          rw [constrainedDINProjection_eq_self C Φ hC hxC]
        rw [hxd.deriv, hfirst]
        change (P ((Y t).1 - β • gradient Φ (Y t).1 - a • (Y t).1 - b • (Y t).2) -
            (Y t).1) + (Y t).1 -
          P ((Y t).1 - β • gradient Φ (Y t).1 - a • (Y t).1 - b • (Y t).2) = 0
        module
      · have hsecond : (F (Y t)).2 = -(a • (Y t).1) - b • (Y t).2 := by
          rfl
        rw [hyd.deriv, hsecond]
        change (-(a • (Y t).1) - b • (Y t).2) + a • (Y t).1 + b • (Y t).2 = 0
        module
  refine ⟨x, y, hxy, hxC1, hyC2, ?_, ?_⟩
  · intro t ht
    exact hviable_global t ht
  · intro x' y' hxy' hreg'
    rcases hxy' with ⟨_, _, _, _, hxzero, hxzeroC, hyzero, heq⟩
    rcases hreg' with ⟨hxC1', hyC2'⟩
    let d : ℝ → H := fun t => derivWithin x' (Set.Ici 0) t
    let p : ℝ → H := fun t => d t + x' t
    have hxsplit := (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)).mp
      (show ContDiffOn ℝ (0 + 1) x' (Set.Ici 0) by simpa using hxC1')
    have hdcont : ContinuousOn d (Set.Ici 0) := by
      simpa [d] using hxsplit.2.2.continuousOn
    have hpcont : ContinuousOn p (Set.Ici 0) := by
      simpa [p] using hdcont.add hxC1'.continuousOn
    have hp_pos (t : ℝ) (ht : 0 < t) : p t ∈ C := by
      have hd : d t = deriv x' t := by
        dsimp [d]
        exact derivWithin_of_mem_nhds (Ici_mem_nhds ht)
      have hproj := sub_eq_zero.mp (heq t ht.le).1
      have hpEq : p t = projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex)
          (x' t - β • gradient Φ (x' t) - a • x' t - b • y' t) := by
        dsimp [p]
        rw [hd]
        exact hproj
      rw [hpEq]
      exact projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex) _
    have hpzeroC : p 0 ∈ C := by
      apply hC.closed.mem_of_tendsto
        ((hpcont 0 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hp_pos t ht
    have hpmem (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) : p t ∈ C := by
      rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
      · exact hpzeroC
      · exact hp_pos t ht
    have hcandidate_viable (t : ℝ) (ht : 0 ≤ t) : x' t ∈ C := by
      apply constrainedDIN_viable_of_relaxed_derivative_interior C x' p t ht
        (by simpa [hxzero] using hxzeroC) hC.closed hC.convex
      · exact hxC1'.continuousOn.mono Set.Icc_subset_Ici_self
      · exact hpcont.mono Set.Icc_subset_Ici_self
      · intro s hs
        exact hpmem s hs.1
      · intro s hs
        have hdiff : DifferentiableAt ℝ x' s :=
          (hxC1'.differentiableOn (by norm_num) s hs.1.le).differentiableAt
            (Ici_mem_nhds hs.1)
        have hd : d s = deriv x' s := by
          dsimp [d]
          exact derivWithin_of_mem_nhds (Ici_mem_nhds hs.1)
        convert hdiff.hasDerivAt using 1
        dsimp [p]
        rw [hd]
        module
    let Z : ℝ → H × H := fun t => (x' t, y' t)
    have hyC1' : ContDiffOn ℝ 1 y' (Set.Ici 0) := hyC2'.of_le (by norm_num)
    have hZC1 : ContDiffOn ℝ 1 Z (Set.Ici 0) := by
      exact hxC1'.prodMk hyC1'
    have hZode_pos (t : ℝ) (ht : 0 < t) : HasDerivAt Z (F (Z t)) t := by
      have hxdiff : DifferentiableAt ℝ x' t :=
        (hxC1'.differentiableOn (by norm_num) t ht.le).differentiableAt
          (Ici_mem_nhds ht)
      have hydiff : DifferentiableAt ℝ y' t :=
        (hyC2'.differentiableOn (by norm_num) t ht.le).differentiableAt
          (Ici_mem_nhds ht)
      have hxeq := (heq t ht.le).1
      have hyeq := (heq t ht.le).2
      let P := constrainedDINProjection C Φ hC
      have hxvel : deriv x' t =
          P (x' t - β • gradient Φ (x' t) - a • x' t - b • y' t) - x' t := by
        apply eq_sub_of_add_eq
        simpa [P, constrainedDINProjection] using sub_eq_zero.mp hxeq
      have hyvel : deriv y' t = -(a • x' t) - b • y' t := by
        have hneg : deriv y' t = -(a • x' t + b • y' t) :=
          eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hyeq)
        rw [hneg]
        module
      have hPx : P (x' t) = x' t :=
        constrainedDINProjection_eq_self C Φ hC (hcandidate_viable t ht.le)
      have hfield : F (Z t) = (deriv x' t, deriv y' t) := by
        apply Prod.ext
        · change P (x' t - β • gradient Φ (P (x' t)) - a • x' t - b • y' t) -
              x' t = deriv x' t
          rw [hPx]
          exact hxvel.symm
        · dsimp [F, Z, constrainedDINPhaseField]
          exact hyvel.symm
      rw [hfield]
      exact hxdiff.hasDerivAt.prodMk hydiff.hasDerivAt
    have hZcont : ContinuousOn Z (Set.Ici 0) := hZC1.continuousOn
    have hFZcont : ContinuousOn (fun t => F (Z t)) (Set.Ici 0) := by
      simpa only [Function.comp_def] using hFcont.comp_continuousOn hZcont
    have hZode_zero : HasDerivWithinAt Z (F (Z 0)) (Set.Ici 0) 0 :=
      constrainedDIN_hasDerivWithinAt_zero_of_contDiffOn_one hZC1 hFZcont hZode_pos
    have hZright (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
        HasDerivWithinAt Z (F (Z t)) (Set.Ici t) t := by
      rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
      · exact hZode_zero
      · exact (hZode_pos t ht).hasDerivWithinAt
    have hYright (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
        HasDerivWithinAt Y (F (Y t)) (Set.Ici t) t :=
      (hYglobal t ht).hasDerivWithinAt
    have hZzero : Z 0 = (x₀, y₀) := by simp [Z, hxzero, hyzero]
    have hpair : Set.EqOn Z Y (Set.Ici 0) := by
      intro t ht
      rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
      · exact hZzero.trans hYmax.2.1.2.1.symm
      · rcases hFnhds (x₀, y₀) with ⟨U, hU, L, hL, hLip⟩
        let K : NNReal := ⟨L, hL⟩
        have hLipU : LipschitzOnWith K F U := by
          apply LipschitzOnWith.of_dist_le_mul
          intro z hz w hw
          simpa only [dist_eq_norm] using hLip z hz w hw
        have hUZ : U ∈ nhds (Z 0) := by simpa [hZzero] using hU
        have hUY : U ∈ nhds (Y 0) := by simpa [hYmax.2.1.2.1] using hU
        have hZnear : Z ⁻¹' U ∈ nhdsWithin 0 (Set.Ici 0) :=
          (hZcont 0 (Set.mem_Ici.mpr le_rfl)) hUZ
        have hYnear : Y ⁻¹' U ∈ nhdsWithin 0 (Set.Ici 0) :=
          ((hYglobal 0 le_rfl).continuousAt.continuousWithinAt) hUY
        obtain ⟨δZ, hδZ, hδZU⟩ := Metric.mem_nhdsWithin_iff.mp hZnear
        obtain ⟨δY, hδY, hδYU⟩ := Metric.mem_nhdsWithin_iff.mp hYnear
        let δ : ℝ := min (t / 2) (min (δZ / 2) (δY / 2))
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
        have hδt : δ < t := by
          have := min_le_left (t / 2) (min (δZ / 2) (δY / 2))
          linarith
        have hδZ' : δ < δZ := by
          have := le_trans (min_le_right (t / 2) (min (δZ / 2) (δY / 2)))
            (min_le_left (δZ / 2) (δY / 2))
          linarith
        have hδY' : δ < δY := by
          have := le_trans (min_le_right (t / 2) (min (δZ / 2) (δY / 2)))
            (min_le_right (δZ / 2) (δY / 2))
          linarith
        have hZU (r : ℝ) (hr : r ∈ Set.Icc 0 δ) : Z r ∈ U := by
          apply hδZU
          constructor
          · rw [Metric.mem_ball, Real.dist_eq]
            simp only [sub_zero, abs_of_nonneg hr.1]
            exact hr.2.trans_lt hδZ'
          · exact hr.1
        have hYU (r : ℝ) (hr : r ∈ Set.Icc 0 δ) : Y r ∈ U := by
          apply hδYU
          constructor
          · rw [Metric.mem_ball, Real.dist_eq]
            simp only [sub_zero, abs_of_nonneg hr.1]
            exact hr.2.trans_lt hδY'
          · exact hr.1
        have hlocalEq := ODE_solution_unique_of_mem_Icc_right
          (v := fun _ : ℝ => F) (s := fun _ => U) (K := K)
          (fun _ _ => hLipU)
          (hZcont.mono Set.Icc_subset_Ici_self)
          (fun r hr => hZright r hr.1) (fun r hr => hZU r ⟨hr.1, hr.2.le⟩)
          (hYcontIci.mono Set.Icc_subset_Ici_self)
          (fun r hr => hYright r hr.1) (fun r hr => hYU r ⟨hr.1, hr.2.le⟩)
          (hZzero.trans hYmax.2.1.2.1.symm)
        have hseed : Z (δ / 2) = Y (δ / 2) :=
          hlocalEq ⟨by linarith, by linarith⟩
        have hprop := ode_eqOn_Ioo_of_locally_lipschitz F hFnhds
          (show δ / 2 ∈ Set.Ioo 0 (t + 1) by constructor <;> linarith)
          Z Y
          (fun r hr => hZode_pos r hr.1)
          (fun r hr => hYglobal r hr.1.le)
          hseed
        exact hprop ⟨ht, by linarith⟩
    constructor
    · intro t ht
      exact congrArg Prod.fst (hpair ht)
    · intro t ht
      exact congrArg Prod.snd (hpair ht)

/-- Theorem 7.1(ii): energy decay and asymptotic properties of every `(c-DIN)` trajectory. -/
theorem constrained_din_global_properties_part_ii {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (hβ : 0 < β) (ha : a ≠ 0) (hb : 0 < b) (hab : 0 < b + a)
  (x₀ y₀ : H) (x y : ℝ → H)
  (hxy : IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y)
  (hreg : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0)) :
    (∀ ell : ℝ, β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ ell →
      ell ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 → ∃ l : ℝ,
      AntitoneOn (fun t => constrainedEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) ∧
      BddBelow ((fun t => constrainedEnergy Φ a b ell (x t) (y t)) '' Set.Ici 0) ∧
      Tendsto (fun t => constrainedEnergy Φ a b ell (x t) (y t)) atTop (nhds l)) ∧
    MeasureTheory.MemLp (deriv x) 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    MeasureTheory.MemLp (deriv y) 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    (∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l)) ∧
    Tendsto (deriv y) atTop (nhds 0) := by
  obtain ⟨X, Y, hXY, hXreg, hYreg, hXC, hunique⟩ :=
    constrained_din_global_properties_part_i C Φ hC β a b hβ ha hb hab x₀ y₀
      hxy.2.2.2.2.2.1
  have hsame := hunique x y hxy hreg
  have hxC (t : ℝ) (ht : 0 ≤ t) : x t ∈ C := by
    rw [hsame.1 (Set.mem_Ici.mpr ht)]
    exact hXC t ht
  have heq (t : ℝ) (ht : 0 ≤ t) :
      deriv x t + x t - constrainedDINProjection C Φ hC
          (x t - β • gradient Φ (x t) - a • x t - b • y t) = 0 ∧
        deriv y t + a • x t + b • y t = 0 := by
    simpa [constrainedDINProjection] using hxy.2.2.2.2.2.2.2 t ht
  have hxd (t : ℝ) (ht : 0 < t) : HasDerivAt x (deriv x t) t :=
    (hreg.1.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hyd (t : ℝ) (ht : 0 < t) : HasDerivAt y (deriv y t) t :=
    (hreg.2.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hPhiDiff (t : ℝ) (ht : 0 ≤ t) : DifferentiableAt ℝ Φ (x t) := by
    rcases hC.continuously_differentiable_on_neighborhood with ⟨U, hUopen, hCU, hPhiU⟩
    exact (hPhiU.differentiableOn (by norm_num) (x t) (hCU (hxC t ht))).differentiableAt
      (hUopen.mem_nhds (hCU (hxC t ht)))
  have hPhiCont : ContinuousOn (fun t => Φ (x t)) (Set.Ici 0) := by
    intro t ht
    exact (hPhiDiff t ht).continuousAt.comp_continuousWithinAt
      (hreg.1.continuousOn t ht)
  have henergyCont (ell : ℝ) : ContinuousOn
      (fun t => constrainedEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) := by
    exact (continuousOn_const.mul hPhiCont).add
      (continuousOn_const.mul
        (((continuousOn_const.smul hreg.1.continuousOn).add
          (continuousOn_const.smul hreg.2.continuousOn)).norm.pow 2))
  have henergyHasDeriv (ell : ℝ) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun s => constrainedEnergy Φ a b ell (x s) (y s))
        (ell * inner ℝ (gradient Φ (x t)) (deriv x t) -
          a * inner ℝ (deriv x t) (deriv y t) - b * ‖deriv y t‖ ^ 2) t := by
    have hPhiCurve : HasDerivAt (fun s => Φ (x s))
        (inner ℝ (gradient Φ (x t)) (deriv x t)) t := by
      simpa using ((hPhiDiff t ht.le).hasGradientAt.hasFDerivAt.comp t
        (hxd t ht).hasFDerivAt).hasDerivAt
    have hq : HasDerivAt (fun s => a • x s + b • y s)
        (a • deriv x t + b • deriv y t) t :=
      ((hxd t ht).const_smul a).add ((hyd t ht).const_smul b)
    have hqv : a • x t + b • y t = -deriv y t := by
      exact eq_neg_of_add_eq_zero_right
        (by simpa [add_assoc] using (heq t ht.le).2)
    have hE := (hPhiCurve.const_mul ell).add (hq.norm_sq.const_mul (1 / 2 : ℝ))
    have hE' : HasDerivAt
        (fun s => ell * Φ (x s) + (1 / 2) * ‖a • x s + b • y s‖ ^ 2)
        (ell * inner ℝ (gradient Φ (x t)) (deriv x t) -
          a * inner ℝ (deriv x t) (deriv y t) - b * ‖deriv y t‖ ^ 2) t := by
      convert hE using 1
      rw [hqv, inner_neg_left, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq,
        real_inner_comm (deriv y t) (deriv x t)]
      ring
    simpa [constrainedEnergy] using hE'
  have hprojection (t : ℝ) (ht : 0 ≤ t) :
      β * inner ℝ (deriv x t) (gradient Φ (x t)) ≤
        -‖deriv x t‖ ^ 2 + inner ℝ (deriv x t) (deriv y t) := by
    let P := constrainedDINProjection C Φ hC
    let z := x t - β • gradient Φ (x t) - a • x t - b • y t
    let p := P z
    have hp : p = deriv x t + x t := by
      exact (sub_eq_zero.mp (heq t ht).1).symm
    have hchar : inner ℝ (x t - p) (z - p) ≤ 0 := by
      exact ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC.nonempty hC.closed hC.convex).mp
        (show p = constrainedDINProjection C Φ hC z from rfl)).2 (x t) (hxC t ht)
    have hz : z - p = -β • gradient Φ (x t) + deriv y t - deriv x t := by
      have hqv : a • x t + b • y t = -deriv y t := by
        exact eq_neg_of_add_eq_zero_right
          (by simpa [add_assoc] using (heq t ht).2)
      calc
        z - p = (x t - β • gradient Φ (x t) - (a • x t + b • y t)) -
            (deriv x t + x t) := by rw [hp]; dsimp [z]; module
        _ = -β • gradient Φ (x t) + deriv y t - deriv x t := by
          rw [hqv]
          module
    have hxp : x t - p = -deriv x t := by rw [hp]; module
    rw [hxp, hz, inner_neg_left] at hchar
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at hchar
    nlinarith
  have hparameter (ell : ℝ)
      (hlow : β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ ell)
      (hhigh : ell ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2) :
      let c := ell / β
      0 < c ∧ (c - a) ^ 2 ≤ 4 * b * c := by
    dsimp only
    have hsb : (Real.sqrt b) ^ 2 = b := by
      simpa using Real.sq_sqrt hb.le
    have hsab : (Real.sqrt (b + a)) ^ 2 = b + a := by
      simpa using Real.sq_sqrt hab.le
    have hsne : Real.sqrt b ≠ Real.sqrt (b + a) := by
      intro h
      apply ha
      have : b = b + a := by
        calc
          b = (Real.sqrt b) ^ 2 := hsb.symm
          _ = (Real.sqrt (b + a)) ^ 2 := by rw [h]
          _ = b + a := hsab
      linarith
    have hspos : 0 < (Real.sqrt b - Real.sqrt (b + a)) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hsne)
    have hc_low : (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ ell / β := by
      exact (le_div_iff₀ hβ).2 (by simpa [mul_comm] using hlow)
    have hc_high : ell / β ≤
        (Real.sqrt b + Real.sqrt (b + a)) ^ 2 := by
      exact (div_le_iff₀ hβ).2 (by simpa [mul_comm] using hhigh)
    have hproduct :
        (ell / β - (Real.sqrt b - Real.sqrt (b + a)) ^ 2) *
          (ell / β - (Real.sqrt b + Real.sqrt (b + a)) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc_low) (sub_nonpos.mpr hc_high)
    constructor
    · exact hspos.trans_le hc_low
    · nlinarith
  have henergyProperties : ∀ ell : ℝ,
      β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ ell →
      ell ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 → ∃ l : ℝ,
      AntitoneOn (fun t => constrainedEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) ∧
      BddBelow ((fun t => constrainedEnergy Φ a b ell (x t) (y t)) '' Set.Ici 0) ∧
      Tendsto (fun t => constrainedEnergy Φ a b ell (x t) (y t)) atTop (nhds l) := by
    intro ell hlow hhigh
    let c := ell / β
    have hc := hparameter ell hlow hhigh
    have hderiv_nonpos (t : ℝ) (ht : 0 < t) :
        deriv (fun s => constrainedEnergy Φ a b ell (x s) (y s)) t ≤ 0 := by
      have hp := mul_le_mul_of_nonneg_left (hprojection t ht.le) hc.1.le
      change c * (β * inner ℝ (deriv x t) (gradient Φ (x t))) ≤
        c * (-‖deriv x t‖ ^ 2 + inner ℝ (deriv x t) (deriv y t)) at hp
      have hell : ell = c * β := by
        dsimp [c]
        field_simp [hβ.ne']
      have hsquare : 0 ≤
          ‖(2 * c) • deriv x t - (c - a) • deriv y t‖ ^ 2 := sq_nonneg _
      rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
        norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hsquare
      simp only [mul_pow, sq_abs] at hsquare
      norm_num at hsquare
      have hdiscY := mul_le_mul_of_nonneg_right hc.2 (sq_nonneg ‖deriv y t‖)
      change (c - a) ^ 2 * ‖deriv y t‖ ^ 2 ≤
        4 * b * c * ‖deriv y t‖ ^ 2 at hdiscY
      have hquad : -c * ‖deriv x t‖ ^ 2 +
          (c - a) * inner ℝ (deriv x t) (deriv y t) -
            b * ‖deriv y t‖ ^ 2 ≤ 0 := by
        nlinarith [hc.1]
      have hgu : inner ℝ (gradient Φ (x t)) (deriv x t) =
          inner ℝ (deriv x t) (gradient Φ (x t)) := real_inner_comm _ _
      rw [(henergyHasDeriv ell t ht).deriv, hgu]
      rw [hell]
      nlinarith [hp, hquad]
    have hanti : AntitoneOn
        (fun t => constrainedEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) (henergyCont ell)
      · intro t ht
        have ht' : 0 < t := by simpa only [interior_Ici] using ht
        exact (henergyHasDeriv ell t ht').differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' : 0 < t := by simpa only [interior_Ici] using ht
        exact hderiv_nonpos t ht'
    obtain ⟨m, hm⟩ := hC.bounded_below
    have hbdd : BddBelow
        ((fun t => constrainedEnergy Φ a b ell (x t) (y t)) '' Set.Ici 0) := by
      refine ⟨ell * m, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have hpm := hm (x t) (hxC t ht)
      have hellnonneg : 0 ≤ ell := by
        have hell : ell = c * β := by
          dsimp [c]
          field_simp [hβ.ne']
        rw [hell]
        exact mul_nonneg hc.1.le hβ.le
      dsimp [constrainedEnergy]
      nlinarith [mul_le_mul_of_nonneg_left hpm hellnonneg,
        sq_nonneg ‖a • x t + b • y t‖]
    let G : ℝ → ℝ := fun t =>
      constrainedEnergy Φ a b ell (x (max t 0)) (y (max t 0))
    have hGanti : Antitone G := by
      intro s t hst
      exact hanti (le_max_right s 0) (le_max_right t 0) (max_le_max_right 0 hst)
    have hGbelow : BddBelow (Set.range G) := by
      rcases hbdd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hk ⟨max t 0, le_max_right t 0, rfl⟩
    refine ⟨⨅ t, G t, hanti, hbdd, ?_⟩
    apply (tendsto_atTop_ciInf hGanti hGbelow).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [G, max_eq_left ht]
  let F := constrainedDINPhaseField C Φ hC β a b
  let Z : ℝ → H × H := fun t => (x t, y t)
  let u : ℝ → H := fun t => (F (Z t)).1
  let v : ℝ → H := fun t => (F (Z t)).2
  have hfield (t : ℝ) (ht : 0 ≤ t) : u t = deriv x t ∧ v t = deriv y t := by
    have hPx := constrainedDINProjection_eq_self C Φ hC (hxC t ht)
    constructor
    · dsimp [u, F, Z, constrainedDINPhaseField]
      rw [hPx]
      symm
      apply eq_sub_of_add_eq
      exact sub_eq_zero.mp (heq t ht).1
    · dsimp [v, F, Z, constrainedDINPhaseField]
      have hneg : deriv y t = -(a • x t + b • y t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq t ht).2)
      rw [hneg]
      module
  have hZderiv (t : ℝ) (ht : 0 < t) : HasDerivAt Z (F (Z t)) t := by
    have hp := (hxd t ht).prodMk (hyd t ht)
    convert hp using 1
    exact Prod.ext (hfield t ht.le).1 (hfield t ht.le).2
  have hZcont : ContinuousOn Z (Set.Ici 0) := hreg.1.continuousOn.prodMk hreg.2.continuousOn
  have hFcont : Continuous F :=
    (constrainedDINPhaseField_locallyLipschitz C Φ hC β a b).continuous
  have hucont : ContinuousOn u (Set.Ici 0) := by
    exact (hFcont.comp_continuousOn hZcont).fst
  have hvcont : ContinuousOn v (Set.Ici 0) := by
    exact (hFcont.comp_continuousOn hZcont).snd
  let lam := β * (a + 2 * b)
  let E : ℝ → ℝ := fun t => constrainedEnergy Φ a b lam (x t) (y t)
  let E' : ℝ → ℝ := fun t =>
    lam * inner ℝ (gradient Φ (x t)) (u t) -
      a * inner ℝ (u t) (v t) - b * ‖v t‖ ^ 2
  let D : ℝ → ℝ := fun t =>
    (a + b) * ‖u t‖ ^ 2 + b * ‖u t - v t‖ ^ 2
  have hlam : 0 < lam := by dsimp [lam]; exact mul_pos hβ (by linarith)
  have hmidData (t : ℝ) (ht : 0 < t) :
      HasDerivAt E (E' t) t ∧ E' t + D t ≤ 0 := by
    simpa [E, E', D, lam, F, Z, u, v, constrainedEnergy, add_assoc] using
      constrainedDIN_energy_dissipation_at C Φ hC β a b hβ hb hab Z
        (hZderiv t ht) (hxC t ht.le)
  have hEcont : ContinuousOn E (Set.Ici 0) := henergyCont lam
  have hgradcont : ContinuousOn (fun t => gradient Φ (x t)) (Set.Ici 0) := by
    let P := constrainedDINProjection C Φ hC
    have hGP : Continuous (fun z => gradient Φ (P z)) :=
      (constrainedDINProjectedGradient_locallyLipschitz C Φ hC).continuous
    have hcomp : ContinuousOn (fun t => gradient Φ (P (x t))) (Set.Ici 0) :=
      hGP.comp_continuousOn hreg.1.continuousOn
    apply hcomp.congr
    intro t ht
    exact congrArg (gradient Φ)
      (constrainedDINProjection_eq_self C Φ hC (hxC t ht)).symm
  have hE'cont : ContinuousOn E' (Set.Ici 0) := by
    exact (((continuousOn_const.mul (hgradcont.inner hucont)).sub
      (continuousOn_const.mul (hucont.inner hvcont))).sub
      (continuousOn_const.mul (hvcont.norm.pow 2)))
  have hDcont : ContinuousOn D (Set.Ici 0) := by
    exact (continuousOn_const.mul (hucont.norm.pow 2)).add
      (continuousOn_const.mul ((hucont.sub hvcont).norm.pow 2))
  obtain ⟨m, hm⟩ := hC.bounded_below
  have hElower (t : ℝ) (ht : 0 ≤ t) : lam * m ≤ E t := by
    have hp := mul_le_mul_of_nonneg_left (hm (x t) (hxC t ht)) hlam.le
    dsimp [E, constrainedEnergy]
    nlinarith [sq_nonneg ‖a • x t + b • y t‖]
  have hDfinite (T : ℝ) (hT : 0 ≤ T) : ∫ t in 0..T, D t ≤ E 0 - lam * m := by
    rcases hT.eq_or_lt with rfl | hT
    · simp only [intervalIntegral.integral_same, sub_nonneg]
      exact hElower 0 le_rfl
    have hE'int : IntervalIntegrable E' MeasureTheory.volume 0 T :=
      (hE'cont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT.le
    have hDint : IntervalIntegrable D MeasureTheory.volume 0 T :=
      (hDcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT.le
    have hpoint : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Icc 0 T), E' t ≤ -D t := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
        MeasureTheory.ae_restrict_of_ae (MeasureTheory.volume.ae_ne (0 : ℝ))] with t ht ht0
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      linarith [(hmidData t htpos).2]
    have hmono := intervalIntegral.integral_mono_ae_restrict hT.le hE'int hDint.neg hpoint
    have hftc : (∫ t in 0..T, E' t) = E T - E 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
        (hEcont.mono Set.Icc_subset_Ici_self)
      · intro t ht
        exact (hmidData t (by simpa [Set.uIoo_of_le hT.le] using ht.1)).1
      · exact hE'int
    rw [hftc] at hmono
    have hmono' : E T - E 0 ≤ -(∫ t in 0..T, D t) := by
      simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using hmono
    linarith [hElower T hT.le]
  let A : ℝ → ℝ := fun t => ‖u t‖ ^ 2
  let B : ℝ → ℝ := fun t => ‖u t - v t‖ ^ 2
  have hAcont : ContinuousOn A (Set.Ici 0) := hucont.norm.pow 2
  have hBcont : ContinuousOn B (Set.Ici 0) := (hucont.sub hvcont).norm.pow 2
  have hAlocal (T : ℝ) : MeasureTheory.IntegrableOn A (Set.Ioc 0 T) := by
    by_cases hT : 0 < T
    · exact (hAcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    · rw [Set.Ioc_eq_empty hT]
      exact MeasureTheory.integrableOn_empty
  have hBlocal (T : ℝ) : MeasureTheory.IntegrableOn B (Set.Ioc 0 T) := by
    by_cases hT : 0 < T
    · exact (hBcont.mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    · rw [Set.Ioc_eq_empty hT]
      exact MeasureTheory.integrableOn_empty
  have hAint : MeasureTheory.IntegrableOn A (Set.Ici 0) := by
    apply constrainedDIN_integrableOn_Ici_of_nonneg_interval_bound hAlocal
      (fun t _ => sq_nonneg _) (K := (E 0 - lam * m) / (a + b))
    intro T hT
    have hAinterval : IntervalIntegrable A MeasureTheory.volume 0 T :=
      (hAcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
    have hDinterval : IntervalIntegrable D MeasureTheory.volume 0 T :=
      (hDcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
    have hscaled : ∫ t in 0..T, (a + b) * A t ≤ ∫ t in 0..T, D t := by
      apply intervalIntegral.integral_mono_on hT (hAinterval.const_mul (a + b)) hDinterval
      intro t ht
      dsimp [D, B]
      exact le_add_of_nonneg_right (mul_nonneg hb.le (sq_nonneg _))
    rw [intervalIntegral.integral_const_mul] at hscaled
    apply (le_div_iff₀ (by linarith : 0 < a + b)).2
    simpa [mul_comm] using hscaled.trans (hDfinite T hT)
  have hBint : MeasureTheory.IntegrableOn B (Set.Ici 0) := by
    apply constrainedDIN_integrableOn_Ici_of_nonneg_interval_bound hBlocal
      (fun t _ => sq_nonneg _) (K := (E 0 - lam * m) / b)
    intro T hT
    have hBinterval : IntervalIntegrable B MeasureTheory.volume 0 T :=
      (hBcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
    have hDinterval : IntervalIntegrable D MeasureTheory.volume 0 T :=
      (hDcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
    have hscaled : ∫ t in 0..T, b * B t ≤ ∫ t in 0..T, D t := by
      apply intervalIntegral.integral_mono_on hT (hBinterval.const_mul b) hDinterval
      intro t ht
      dsimp [D, A]
      exact le_add_of_nonneg_left
        (mul_nonneg (by linarith : 0 ≤ a + b) (sq_nonneg _))
    rw [intervalIntegral.integral_const_mul] at hscaled
    apply (le_div_iff₀ hb).2
    simpa [mul_comm] using hscaled.trans (hDfinite T hT)
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have huLp : MeasureTheory.MemLp u 2 μ := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm]
    · exact hAint.mono_set Set.Ioi_subset_Ici_self
    · exact (hucont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have huvLp : MeasureTheory.MemLp (fun t => u t - v t) 2 μ := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm]
    · exact hBint.mono_set Set.Ioi_subset_Ici_self
    · exact ((hucont.sub hvcont).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi
  have hvLp : MeasureTheory.MemLp v 2 μ := by
    have htemp := huLp.sub huvLp
    apply htemp.ae_eq
    filter_upwards with t
    change u t - (u t - v t) = v t
    module
  have hdxLp : MeasureTheory.MemLp (deriv x) 2 μ := by
    apply huLp.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hfield t ht.le).1
  have hdyLp : MeasureTheory.MemLp (deriv y) 2 μ := by
    apply hvLp.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hfield t ht.le).2
  have hyderivC1 : ContDiffOn ℝ 1 (deriv y) (Set.Ioi 0) := by
    exact (hreg.2.mono Set.Ioi_subset_Ici_self).deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hddy (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (deriv y) (-(a • deriv x t) - b • deriv y t) t := by
    have hright : HasDerivAt (fun s => -(a • x s) - b • y s)
        (-(a • deriv x t) - b • deriv y t) t := by
      convert ((hxd t ht).const_smul a).neg.sub ((hyd t ht).const_smul b) using 1
    have hevent : deriv y =ᶠ[nhds t] fun s => -(a • x s) - b • y s := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have hneg : deriv y s = -(a • x s + b • y s) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq s hs.le).2)
      rw [hneg]
      module
    exact hright.congr_of_eventuallyEq hevent
  have hddyEq (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      deriv (deriv y) t = -(a • deriv x t) - b • deriv y t :=
    (hddy t ht).deriv
  have hddyLp : MeasureTheory.MemLp (deriv (deriv y)) 2 μ := by
    have hright : MeasureTheory.MemLp
        (fun t => -(a • deriv x t) - b • deriv y t) 2 μ :=
      (hdxLp.const_smul a).neg.sub (hdyLp.const_smul b)
    apply hright.ae_eq
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hddyEq t ht).symm
  have hgint : MeasureTheory.IntegrableOn (fun t => ‖deriv y t‖ ^ 2) (Set.Ioi 0) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hdyLp.aestronglyMeasurable).mp hdyLp
  have hprod : MeasureTheory.IntegrableOn
      (fun t => ‖deriv y t‖ * ‖deriv (deriv y) t‖) (Set.Ioi 0) :=
    hdyLp.norm.integrable_mul hddyLp.norm
  have hg'int : MeasureTheory.IntegrableOn
      (fun t => 2 * inner ℝ (deriv y t) (deriv (deriv y) t)) (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.mono' (hprod.const_mul 2)
    · exact (hdyLp.aestronglyMeasurable.inner hddyLp.aestronglyMeasurable).const_mul 2
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul]
      norm_num
      exact abs_real_inner_le_norm _ _
  have hsqzero : Tendsto (fun t => ‖deriv y t‖ ^ 2) atTop (nhds 0) := by
    apply MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (f' := fun t => 2 * inner ℝ (deriv y t) (deriv (deriv y) t))
    · intro t ht
      rw [hddyEq t ht]
      simpa [real_inner_comm] using (hddy t ht).norm_sq
    · exact hg'int
    · exact hgint
  have hdyzero : Tendsto (deriv y) atTop (nhds 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsqzero
    convert hsqrt using 1
    · funext t
      rw [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_norm]
    · simp
  have hsb : (Real.sqrt b) ^ 2 = b := by simpa using Real.sq_sqrt hb.le
  have hsab : (Real.sqrt (b + a)) ^ 2 = b + a := by
    simpa using Real.sq_sqrt hab.le
  have hmidLow : β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ lam := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  have hmidHigh : lam ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  obtain ⟨lE, _, _, hElim⟩ := henergyProperties lam hmidLow hmidHigh
  have hqzero : Tendsto (fun t => ‖a • x t + b • y t‖ ^ 2) atTop (nhds 0) := by
    have hnorm : Tendsto (fun t => ‖deriv y t‖ ^ 2) atTop (nhds 0) := by
      simpa using hdyzero.norm.pow 2
    apply hnorm.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hy := (heq t ht).2
    have hq : a • x t + b • y t = -deriv y t :=
      eq_neg_of_add_eq_zero_right (by simpa [add_assoc] using hy)
    simp [hq]
  have hPhilim : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
    refine ⟨lam⁻¹ * lE, ?_⟩
    have hkin : Tendsto (fun t => (1 / 2 : ℝ) * ‖a • x t + b • y t‖ ^ 2)
        atTop (nhds 0) := by simpa using tendsto_const_nhds.mul hqzero
    have hdiff := hElim.sub hkin
    have hscaled : Tendsto
        (fun t => lam⁻¹ *
          (constrainedEnergy Φ a b lam (x t) (y t) -
            (1 / 2 : ℝ) * ‖a • x t + b • y t‖ ^ 2))
        atTop (nhds (lam⁻¹ * (lE - 0))) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => lam⁻¹) atTop (nhds lam⁻¹)).mul hdiff
    convert hscaled using 1
    · funext t
      dsimp [constrainedEnergy]
      field_simp [hlam.ne']
      ring
    · simp
  exact ⟨henergyProperties, hdxLp, hdyLp, hPhilim, hdyzero⟩

private theorem constrainedDIN_uniformContinuousOn_sq_integrable_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Set.Ici 0)) :
    Tendsto f atTop (nhds 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨ε, hε, hbad⟩
  have htail : Tendsto (fun n : ℕ => ∫ x in Set.Ici (n : ℝ), ‖f x‖ ^ 2)
      atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => ‖f x‖ ^ 2) (fun n : ℕ => measurableSet_Ici)
      (fun m n hmn => Set.Ici_subset_Ici.mpr (Nat.cast_le.mpr hmn))
      ⟨0, hint.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))⟩
    have hempty : (⋂ n : ℕ, Set.Ici (n : ℝ)) = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact False.elim ((not_le_of_gt hn) (Set.mem_iInter.mp hx n))
      · simp
    simpa [hempty] using h
  have hδ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by linarith)
  rcases hδ with ⟨δ, hδ, hδprop⟩
  have hc : 0 < (ε / 2) ^ 2 * (δ / 2) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) _ hc
  obtain ⟨u, huN, hubad⟩ := hbad (N : ℝ)
  have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg N) huN
  have hlow : ∀ x ∈ Set.Ioc u (u + δ / 2), (ε / 2) ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x hx
    have hxu : |x - u| < δ := by
      rw [abs_of_nonneg (le_of_lt (sub_pos.mpr hx.1))]
      linarith [hx.2, hδ]
    have hfx : dist (f x) (f u) < ε / 2 := by
      exact hδprop x (le_trans hu0 (le_of_lt hx.1)) u hu0
        (by simpa [Real.dist_eq] using hxu)
    have hub : ε ≤ ‖f u‖ := by simpa using hubad
    have htri : ‖f u‖ ≤ ‖f x‖ + ‖f x - f u‖ := by
      calc
        ‖f u‖ = ‖f x + (f u - f x)‖ := by congr 1; abel
        _ ≤ ‖f x‖ + ‖f u - f x‖ := norm_add_le _ _
        _ = ‖f x‖ + ‖f x - f u‖ := by rw [norm_sub_rev]
    have hnorm : ε / 2 < ‖f x‖ := by
      rw [dist_eq_norm] at hfx
      linarith
    nlinarith [norm_nonneg (f x)]
  have hint_lower : (ε / 2) ^ 2 * (δ / 2) ≤
      ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 := by
    calc
      (ε / 2) ^ 2 * (δ / 2) = ∫ x in Set.Ioc u (u + δ / 2), (ε / 2) ^ 2 := by
        rw [MeasureTheory.integral_const]
        simp [max_eq_left (by linarith : 0 ≤ δ / 2)]
        ring
      _ ≤ ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae
        · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact hint.mono_set (by
            intro x hx
            exact le_trans hu0 (le_of_lt hx.1))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hlow x hx
  have hinter : Set.Ioc u (u + δ / 2) ⊆ Set.Ici (N : ℝ) := by
    intro x hx
    exact le_trans huN (le_of_lt hx.1)
  have hint_upper : ∫ x in Set.Ioc u (u + δ / 2), ‖f x‖ ^ 2 ≤
      ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hint.mono_set (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg N))
    · filter_upwards with x
      exact sq_nonneg _
    · exact hinter.eventuallyLE
  have hN' := hN N le_rfl
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact sq_nonneg _
  change |(∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

/-- Theorem 7.1(iii): further boundedness and decay for a bounded `(c-DIN)` trajectory. -/
theorem constrained_din_global_properties_part_iii {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (hβ : 0 < β) (ha : a ≠ 0) (hb : 0 < b) (hab : 0 < b + a)
  (x₀ y₀ : H) (x y : ℝ → H)
  (hxy : IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y)
  (hreg : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0)) :
    Bornology.IsBounded (x '' Set.Ici 0) →
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici 0) ∧
      Bornology.IsBounded (y '' Set.Ici 0) ∧
      Bornology.IsBounded ((deriv x) '' Set.Ici 0) ∧
      Tendsto (deriv x) atTop (nhds 0) := by
  intro hxbounded
  obtain ⟨X, Y, hXY, hXreg, hYreg, hXC, hunique⟩ :=
    constrained_din_global_properties_part_i C Φ hC β a b hβ ha hb hab x₀ y₀
      hxy.2.2.2.2.2.1
  have hsame := hunique x y hxy hreg
  have hxC (t : ℝ) (ht : 0 ≤ t) : x t ∈ C := by
    rw [hsame.1 (Set.mem_Ici.mpr ht)]
    exact hXC t ht
  have heq (t : ℝ) (ht : 0 ≤ t) :
      deriv x t + x t - constrainedDINProjection C Φ hC
          (x t - β • gradient Φ (x t) - a • x t - b • y t) = 0 ∧
        deriv y t + a • x t + b • y t = 0 := by
    simpa [constrainedDINProjection] using hxy.2.2.2.2.2.2.2 t ht
  have hii := constrained_din_global_properties_part_ii C Φ hC β a b hβ ha hb hab
    x₀ y₀ x y hxy hreg
  rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨R, hR⟩
  have hxzero : x 0 = x₀ := hxy.2.2.2.2.1
  have hRnonneg : 0 ≤ R := by
    exact (norm_nonneg x₀).trans (hR x₀ ⟨0, Set.mem_Ici.mpr le_rfl, hxzero⟩)
  obtain ⟨L, hL, hgrad⟩ := hC.gradient_lipschitz_on_bounded R
  let G : ℝ := L * (2 * R) + ‖gradient Φ x₀‖
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hgradbound (t : ℝ) (ht : 0 ≤ t) : ‖gradient Φ (x t)‖ ≤ G := by
    have hxt := hR (x t) ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hx0 := hR x₀ ⟨0, Set.mem_Ici.mpr le_rfl, hxzero⟩
    have hdiff := hgrad (x t) (hxC t ht) x₀ hxy.2.2.2.2.2.1 hxt hx0
    calc
      ‖gradient Φ (x t)‖ ≤
          ‖gradient Φ (x t) - gradient Φ x₀‖ + ‖gradient Φ x₀‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ L * ‖x t - x₀‖ + ‖gradient Φ x₀‖ := add_le_add hdiff le_rfl
      _ ≤ L * (2 * R) + ‖gradient Φ x₀‖ := by
        gcongr
        calc
          ‖x t - x₀‖ ≤ ‖x t‖ + ‖x₀‖ := norm_sub_le _ _
          _ ≤ 2 * R := by nlinarith
      _ = G := rfl
  have hgradbounded :
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨G, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hgradbound t ht
  let lam : ℝ := β * (a + 2 * b)
  have hlam : 0 < lam := by dsimp [lam]; exact mul_pos hβ (by linarith)
  have hsb : (Real.sqrt b) ^ 2 = b := by simpa using Real.sq_sqrt hb.le
  have hsab : (Real.sqrt (b + a)) ^ 2 = b + a := by
    simpa using Real.sq_sqrt hab.le
  have hmidLow : β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ lam := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  have hmidHigh : lam ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  obtain ⟨lE, hEanti, hEbelow, hElim⟩ := hii.1 lam hmidLow hmidHigh
  obtain ⟨m, hm⟩ := hC.bounded_below
  let q : ℝ → H := fun t => a • x t + b • y t
  let E : ℝ → ℝ := fun t => constrainedEnergy Φ a b lam (x t) (y t)
  have hEzeroLower : lam * m ≤ E 0 := by
    have hp := mul_le_mul_of_nonneg_left (hm (x 0) (hxC 0 le_rfl)) hlam.le
    dsimp [E, constrainedEnergy, q]
    nlinarith [sq_nonneg ‖a • x 0 + b • y 0‖]
  let Q : ℝ := 2 * (E 0 - lam * m) + 1
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hqbound (t : ℝ) (ht : 0 ≤ t) : ‖q t‖ ≤ Q := by
    have hanti := hEanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hphi := hm (x t) (hxC t ht)
    have hphis := mul_le_mul_of_nonneg_left hphi hlam.le
    have hsq : ‖q t‖ ^ 2 ≤ 2 * (E 0 - lam * m) := by
      dsimp [E, constrainedEnergy, q] at hanti ⊢
      nlinarith
    dsimp [Q]
    nlinarith [sq_nonneg (‖q t‖ - 1 / 2), norm_nonneg (q t)]
  let Ry : ℝ := |b|⁻¹ * (Q + |a| * R)
  have hRy : 0 ≤ Ry := by dsimp [Ry]; positivity
  have hybound (t : ℝ) (ht : 0 ≤ t) : ‖y t‖ ≤ Ry := by
    have hby : b • y t = q t - a • x t := by dsimp [q]; module
    calc
      ‖y t‖ = |b|⁻¹ * ‖b • y t‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        field_simp [abs_ne_zero.mpr hb.ne']
      _ = |b|⁻¹ * ‖q t - a • x t‖ := by rw [hby]
      _ ≤ |b|⁻¹ * (‖q t‖ + |a| * ‖x t‖) := by
        gcongr
        simpa [norm_smul, Real.norm_eq_abs] using norm_sub_le (q t) (a • x t)
      _ ≤ |b|⁻¹ * (Q + |a| * R) := by
        gcongr
        · exact hqbound t ht
        · exact hR (x t) ⟨t, Set.mem_Ici.mpr ht, rfl⟩
      _ = Ry := rfl
  have hybounded : Bornology.IsBounded (y '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Ry, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hybound t ht
  let V : ℝ := |β| * G + Q
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hdxbound (t : ℝ) (ht : 0 ≤ t) : ‖deriv x t‖ ≤ V := by
    let P := constrainedDINProjection C Φ hC
    let z : H := x t - β • gradient Φ (x t) - a • x t - b • y t
    have hPx : P (x t) = x t := constrainedDINProjection_eq_self C Φ hC (hxC t ht)
    have hform : deriv x t = P z - x t := by
      have hp : P z = deriv x t + x t := (sub_eq_zero.mp (heq t ht).1).symm
      rw [hp]
      module
    rw [hform, ← hPx]
    calc
      ‖P z - P (x t)‖ ≤ ‖z - x t‖ := by
        simpa using (constrainedDINProjection_lipschitz C Φ hC).norm_sub_le z (x t)
      _ = ‖-β • gradient Φ (x t) - q t‖ := by
        congr 1
        dsimp [z, q]
        module
      _ ≤ ‖-β • gradient Φ (x t)‖ + ‖q t‖ := norm_sub_le _ _
      _ ≤ |β| * G + Q := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        gcongr
        · exact hgradbound t ht
        · exact hqbound t ht
      _ = V := rfl
  have hdxbounded : Bornology.IsBounded ((deriv x) '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨V, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hdxbound t ht
  have hdybound (t : ℝ) (ht : 0 ≤ t) : ‖deriv y t‖ ≤ Q := by
    have hneg : deriv y t = -q t := by
      dsimp [q]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq t ht).2)
    rw [hneg, norm_neg]
    exact hqbound t ht
  let F := constrainedDINPhaseField C Φ hC β a b
  let Z : ℝ → H × H := fun t => (x t, y t)
  have hfield (t : ℝ) (ht : 0 ≤ t) : F (Z t) = (deriv x t, deriv y t) := by
    apply Prod.ext
    · dsimp [F, Z, constrainedDINPhaseField]
      rw [constrainedDINProjection_eq_self C Φ hC (hxC t ht)]
      symm
      apply eq_sub_of_add_eq
      exact sub_eq_zero.mp (heq t ht).1
    · dsimp [F, Z, constrainedDINPhaseField]
      have hneg : deriv y t = -(a • x t + b • y t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq t ht).2)
      rw [hneg]
      module
  have hxd (t : ℝ) (ht : 0 < t) : HasDerivAt x (deriv x t) t :=
    (hreg.1.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hyd (t : ℝ) (ht : 0 < t) : HasDerivAt y (deriv y t) t :=
    (hreg.2.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hZode (t : ℝ) (ht : 0 < t) : HasDerivAt Z (F (Z t)) t := by
    have hp := (hxd t ht).prodMk (hyd t ht)
    convert hp using 1
    exact hfield t ht.le
  have hZC1 : ContDiffOn ℝ 1 Z (Set.Ici 0) :=
    hreg.1.prodMk (hreg.2.of_le (by norm_num))
  have hFcont : Continuous F :=
    (constrainedDINPhaseField_locallyLipschitz C Φ hC β a b).continuous
  have hFZcont : ContinuousOn (fun t => F (Z t)) (Set.Ici 0) :=
    hFcont.comp_continuousOn hZC1.continuousOn
  have hZzero : HasDerivWithinAt Z (F (Z 0)) (Set.Ici 0) 0 :=
    constrainedDIN_hasDerivWithinAt_zero_of_contDiffOn_one hZC1 hFZcont hZode
  have hxwithin (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt x (deriv x t) (Set.Ici 0) t := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · have hz := hZzero.hasFDerivWithinAt.fst.hasDerivWithinAt
      simpa [Z, hfield 0 le_rfl] using hz
    · exact (hxd t ht).hasDerivWithinAt
  have hywithin (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt y (deriv y t) (Set.Ici 0) t := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · have hz := hZzero.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [Z, hfield 0 le_rfl] using hz
    · exact (hyd t ht).hasDerivWithinAt
  let KV : NNReal := ⟨V, hV⟩
  let KQ : NNReal := ⟨Q, hQ.le⟩
  have hxLip : LipschitzOnWith KV x (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hxwithin
    intro t ht
    apply NNReal.coe_le_coe.mpr
    simpa [KV] using hdxbound t ht
  have hyLip : LipschitzOnWith KQ y (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hywithin
    intro t ht
    apply NNReal.coe_le_coe.mpr
    simpa [KQ] using hdybound t ht
  let arg : ℝ → H := fun t =>
    x t - β • gradient Φ (x t) - a • x t - b • y t
  have hvel (t : ℝ) (ht : 0 ≤ t) :
      deriv x t = constrainedDINProjection C Φ hC (arg t) - x t := by
    have hp : constrainedDINProjection C Φ hC (arg t) = deriv x t + x t := by
      exact (sub_eq_zero.mp (heq t ht).1).symm
    rw [hp]
    module
  let Kvel : ℝ := (1 + |β| * L + |a|) * V + |b| * Q + V
  have hKvel : 0 ≤ Kvel := by dsimp [Kvel]; positivity
  have hvelLip : LipschitzOnWith (Real.toNNReal Kvel) (deriv x) (Set.Ici 0) := by
    apply LipschitzOnWith.of_dist_le'
    intro s hs t ht
    have hxs : ‖x s‖ ≤ R := hR (x s) ⟨s, hs, rfl⟩
    have hxt : ‖x t‖ ≤ R := hR (x t) ⟨t, ht, rfl⟩
    have hxdiff : ‖x s - x t‖ ≤ V * ‖s - t‖ := by
      simpa [dist_eq_norm, KV] using hxLip.dist_le_mul s hs t ht
    have hxdiff' : ‖x s - x t‖ ≤ ‖s - t‖ * V := by
      simpa [mul_comm] using hxdiff
    have hydiff : ‖y s - y t‖ ≤ Q * ‖s - t‖ := by
      simpa [dist_eq_norm, KQ] using hyLip.dist_le_mul s hs t ht
    have hydiff' : ‖y s - y t‖ ≤ ‖s - t‖ * Q := by
      simpa [mul_comm] using hydiff
    have hgdiff : ‖gradient Φ (x s) - gradient Φ (x t)‖ ≤
        L * (V * ‖s - t‖) :=
      (hgrad (x s) (hxC s hs) (x t) (hxC t ht) hxs hxt).trans
        (mul_le_mul_of_nonneg_left hxdiff hL)
    have hargdiff : ‖arg s - arg t‖ ≤
        ((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖ := by
      calc
        ‖arg s - arg t‖ = ‖(x s - x t) -
            β • (gradient Φ (x s) - gradient Φ (x t)) -
            a • (x s - x t) - b • (y s - y t)‖ := by
          congr 1
          dsimp [arg]
          module
        _ ≤ ‖x s - x t‖ + |β| * ‖gradient Φ (x s) - gradient Φ (x t)‖ +
            |a| * ‖x s - x t‖ + |b| * ‖y s - y t‖ := by
          calc
            _ ≤ ‖(x s - x t) - β • (gradient Φ (x s) - gradient Φ (x t)) -
                a • (x s - x t)‖ + ‖b • (y s - y t)‖ := norm_sub_le _ _
            _ ≤ (‖(x s - x t) - β • (gradient Φ (x s) - gradient Φ (x t))‖ +
                ‖a • (x s - x t)‖) + ‖b • (y s - y t)‖ := by gcongr; apply norm_sub_le
            _ ≤ ((‖x s - x t‖ + ‖β • (gradient Φ (x s) - gradient Φ (x t))‖) +
                ‖a • (x s - x t)‖) + ‖b • (y s - y t)‖ := by gcongr; apply norm_sub_le
            _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖s - t‖ * V + |β| * (L * (V * ‖s - t‖)) +
            |a| * (V * ‖s - t‖) + |b| * (Q * ‖s - t‖) := by
          gcongr
        _ = ((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖ := by ring
    rw [dist_eq_norm, hvel s hs, hvel t ht]
    calc
      ‖(constrainedDINProjection C Φ hC (arg s) - x s) -
          (constrainedDINProjection C Φ hC (arg t) - x t)‖ ≤
          ‖constrainedDINProjection C Φ hC (arg s) -
            constrainedDINProjection C Φ hC (arg t)‖ + ‖x s - x t‖ := by
        rw [show
          (constrainedDINProjection C Φ hC (arg s) - x s) -
              (constrainedDINProjection C Φ hC (arg t) - x t) =
            (constrainedDINProjection C Φ hC (arg s) -
              constrainedDINProjection C Φ hC (arg t)) - (x s - x t) by
          module]
        exact norm_sub_le _ _
      _ ≤ ‖arg s - arg t‖ + ‖x s - x t‖ := by
        gcongr
        simpa using
          (constrainedDINProjection_lipschitz C Φ hC).norm_sub_le (arg s) (arg t)
      _ ≤ (((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖) +
          V * ‖s - t‖ := add_le_add hargdiff hxdiff
      _ = Kvel * dist s t := by
        dsimp [Kvel]
        rw [dist_eq_norm, Real.norm_eq_abs]
        ring
  have hdxuc : UniformContinuousOn (deriv x) (Set.Ici 0) := hvelLip.uniformContinuousOn
  have hdxintIoi : MeasureTheory.IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ioi 0) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hii.2.1.aestronglyMeasurable).mp hii.2.1
  have hdxintIci : MeasureTheory.IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  have hdxzero : Tendsto (deriv x) atTop (nhds 0) :=
    constrainedDIN_uniformContinuousOn_sq_integrable_tendsto_zero _ hdxuc hdxintIci
  exact ⟨hgradbounded, hybounded, hdxbounded, hdxzero⟩
end Alvarez2002
