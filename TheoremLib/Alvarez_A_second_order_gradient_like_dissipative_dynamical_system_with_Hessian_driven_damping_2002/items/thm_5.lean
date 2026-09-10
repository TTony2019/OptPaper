import Mathlib
import Foundation.Differentiation.ODE
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_thm_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_8

namespace Alvarez2002

open Filter
open MeasureTheory
open scoped Topology

def LipschitzOnBoundedSets {H : Type*} [NormedAddCommGroup H]
    (f : H → H) : Prop := ∀ s : Set H, Bornology.IsBounded s →
      ∃ K : NNReal, LipschitzOnWith K f s

def SameTrajectoryOnNonnegative {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (x1 y1 x2 y2 : ℝ → H) : Prop :=
  ∀ t, 0 ≤ t → (x1 t = x2 t ∧ y1 t = y2 t)

noncomputable def LyapunovEnergy {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (a b ell : ℝ) (x y : H) : ℝ :=
  ell * Φ x + (1 / 2) * ‖a • x + b • y‖ ^ 2

def MemL2OnNonnegative {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ℝ → H) : Prop :=
  MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))

def BoundedOnNonnegative {H : Type*} [NormedAddCommGroup H]
    (f : ℝ → H) : Prop := Bornology.IsBounded (f '' Set.Ici (0 : ℝ))

private noncomputable def gdinPhaseField
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ) : H × H → H × H := fun z =>
  (-β • gradient Φ z.1 - a • z.1 - b • z.2, -a • z.1 - b • z.2)

private theorem gdin_grad_lipschitzOnBounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradΦ : H → H) (hloclip : LipschitzOnBoundedSets gradΦ) :
    LocallyLipschitz gradΦ := by
  intro z
  rcases hloclip (Metric.closedBall z 1) Metric.isBounded_closedBall with ⟨K, hK⟩
  exact ⟨K, Metric.closedBall z 1, Metric.closedBall_mem_nhds z zero_lt_one, hK⟩

private theorem gdinPhaseField_locallyLipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hloclip : LipschitzOnBoundedSets (gradient Φ)) :
    LocallyLipschitz (gdinPhaseField Φ β a b) := by
  have hg : LocallyLipschitz (gradient Φ) := gdin_grad_lipschitzOnBounded (gradient Φ) hloclip
  have hfst : LocallyLipschitz (Prod.fst : H × H → H) :=
    LipschitzWith.prod_fst.locallyLipschitz
  have hsnd : LocallyLipschitz (Prod.snd : H × H → H) :=
    LipschitzWith.prod_snd.locallyLipschitz
  let Lβ : H →L[ℝ] H := β • ContinuousLinearMap.id ℝ H
  let La : H →L[ℝ] H := a • ContinuousLinearMap.id ℝ H
  let Lb : H →L[ℝ] H := b • ContinuousLinearMap.id ℝ H
  have hβg : LocallyLipschitz (fun z : H × H => β • gradient Φ z.1) := by
    simpa [Lβ, Function.comp_def] using Lβ.lipschitz.locallyLipschitz.comp (hg.comp hfst)
  have hax : LocallyLipschitz (fun z : H × H => a • z.1) := by
    simpa [La, Function.comp_def] using La.lipschitz.locallyLipschitz.comp hfst
  have hby : LocallyLipschitz (fun z : H × H => b • z.2) := by
    simpa [Lb, Function.comp_def] using Lb.lipschitz.locallyLipschitz.comp hsnd
  unfold gdinPhaseField
  simpa only [Pi.neg_apply, Pi.sub_apply, neg_smul] using
    (((hβg.neg.sub hax).sub hby).prodMk (hax.neg.sub hby))

private theorem gdin_grad_continuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) : Continuous (gradient Φ) := by
  simpa [gradient, Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.comp
      (hΦ.continuous_fderiv (by norm_num))

private theorem gdin_admissible_energy_deriv_nonpos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (β a b ell : ℝ) (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (hlow : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell)
    (hhigh : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2) (u q : H) :
    -ell * β * ‖u‖ ^ 2 - (ell + a * β) * inner ℝ u q -
        (a + b) * ‖q‖ ^ 2 ≤ 0 := by
  have hs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
  have ht_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hs_four : Real.sqrt (a + b) ^ 4 = (a + b) ^ 2 := by
    rw [show Real.sqrt (a + b) ^ 4 = (Real.sqrt (a + b) ^ 2) ^ 2 by ring, hs_sq]
  have ht_four : Real.sqrt b ^ 4 = b ^ 2 := by
    rw [show Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 by ring, ht_sq]
  have hdisc : (ell + a * β) ^ 2 ≤ 4 * (ell * β) * (a + b) := by
    have hprod : 0 ≤
        (ell - β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2) *
          (β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 - ell) :=
      mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhigh)
    ring_nf at hprod
    rw [hs_sq, ht_sq, hs_four, ht_four] at hprod
    ring_nf at hprod ⊢
    nlinarith
  have hell : 0 ≤ ell :=
    (mul_nonneg hβ.le (sq_nonneg _)).trans hlow
  have hA : 0 ≤ ell * β := mul_nonneg hell hβ.le
  have hquad : 0 ≤ ell * β * ‖u‖ ^ 2 - |ell + a * β| * ‖u‖ * ‖q‖ +
      (a + b) * ‖q‖ ^ 2 := by
    by_cases hzero : ell * β = 0
    · have hc : ell + a * β = 0 := by nlinarith
      simp [hzero, hc, mul_nonneg hab.le (sq_nonneg ‖q‖)]
    · have hpos : 0 < ell * β := lt_of_le_of_ne hA (Ne.symm hzero)
      have hrest : 0 ≤ 4 * (ell * β) * (a + b) - |ell + a * β| ^ 2 := by
        rw [sq_abs]
        linarith
      nlinarith [sq_nonneg
        (2 * (ell * β) * ‖u‖ - |ell + a * β| * ‖q‖)]
  have hinner : |inner ℝ u q| ≤ ‖u‖ * ‖q‖ := abs_real_inner_le_norm u q
  have hcross : -(ell + a * β) * inner ℝ u q ≤
      |ell + a * β| * ‖u‖ * ‖q‖ := by
    calc
      -(ell + a * β) * inner ℝ u q ≤
          |-(ell + a * β) * inner ℝ u q| := le_abs_self _
      _ = |ell + a * β| * |inner ℝ u q| := by rw [abs_mul, abs_neg]
      _ ≤ |ell + a * β| * (‖u‖ * ‖q‖) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
      _ = |ell + a * β| * ‖u‖ * ‖q‖ := by ring
  nlinarith

private theorem gdin_energy_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b ell : ℝ) (x y : ℝ → H)
    (hΦ : ContDiff ℝ 1 Φ)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    {x₀ y₀ : H} (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => LyapunovEnergy Φ a b ell (x s) (y s))
      (-ell * β * ‖gradient Φ (x t)‖ ^ 2 -
        (ell + a * β) * inner ℝ (gradient Φ (x t)) (a • x t + b • y t) -
        (a + b) * ‖a • x t + b • y t‖ ^ 2) t := by
  have hx : HasDerivAt x (deriv x t) t :=
    (hxy.1.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hy : HasDerivAt y (deriv y t) t :=
    (hxy.2.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hPhiDeriv : HasFDerivAt Φ (innerSL ℝ (gradient Φ (x t))) (x t) := by
    simpa [innerSL] using
      ((hΦ.differentiable (by norm_num) (x t)).hasGradientAt.hasFDerivAt)
  have hp : HasDerivAt (fun s => Φ (x s))
      (inner ℝ (gradient Φ (x t)) (deriv x t)) t := by
    simpa using hPhiDeriv.comp_hasDerivAt t hx
  have hq : HasDerivAt (fun s => a • x s + b • y s)
      (a • deriv x t + b • deriv y t) t :=
    (hx.const_smul a).add (hy.const_smul b)
  have hE := (hp.const_smul ell).add (hq.norm_sq.const_smul (1 / 2 : ℝ))
  have hE' : HasDerivAt (fun s => ell * Φ (x s) +
      (1 / 2 : ℝ) * ‖a • x s + b • y s‖ ^ 2)
      (ell * inner ℝ (gradient Φ (x t)) (deriv x t) +
        (1 / 2 : ℝ) * (2 * inner ℝ (a • x t + b • y t)
          (a • deriv x t + b • deriv y t))) t := by
    simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hE
  convert hE' using 1
  have hxval : deriv x t = -β • gradient Φ (x t) - a • x t - b • y t := by
    rw [show -β • gradient Φ (x t) - a • x t - b • y t =
      -(β • gradient Φ (x t) + a • x t + b • y t) by module]
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.1 t ht.le)
  have hyval : deriv y t = -a • x t - b • y t := by
    rw [show -a • x t - b • y t = -(a • x t + b • y t) by module]
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.2.1 t ht.le)
  rw [hxval, hyval]
  rw [show ‖gradient Φ (x t)‖ ^ 2 =
      inner ℝ (gradient Φ (x t)) (gradient Φ (x t)) by
        rw [real_inner_self_eq_norm_sq],
    show ‖a • x t + b • y t‖ ^ 2 =
      inner ℝ (a • x t + b • y t) (a • x t + b • y t) by
        rw [real_inner_self_eq_norm_sq]]
  simp only [one_div, inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (x t) (gradient Φ (x t)),
    real_inner_comm (y t) (gradient Φ (x t)), real_inner_comm (y t) (x t)]
  ring

private theorem antitoneOn_Ici_bddBelow_tendsto_atTop
    {f : ℝ → ℝ} (hanti : AntitoneOn f (Set.Ici (0 : ℝ)))
    (hlower : ∃ m : ℝ, ∀ t : ℝ, 0 ≤ t → m ≤ f t) :
    ∃ l : ℝ, Tendsto f atTop (nhds l) := by
  let g : ℝ → ℝ := fun t => f (max t 0)
  have hganti : Antitone g := by
    intro s t hst
    exact hanti (le_max_right s 0) (le_max_right t 0) (max_le_max_right 0 hst)
  rcases hlower with ⟨m, hm⟩
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨m, ?_⟩
    rintro z ⟨t, rfl⟩
    exact hm (max t 0) (le_max_right t 0)
  refine ⟨⨅ t, g t, (tendsto_atTop_ciInf hganti hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [g, max_eq_left ht]

private theorem gdin_dissipation_integrableOn_Ioi
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici (0 : ℝ)) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn (fun t => ‖gradient Φ (x t)‖ ^ 2) (Set.Ioi (0 : ℝ)) := by
  let ell : ℝ := β * (a + 2 * b)
  let E : ℝ → ℝ := fun t => LyapunovEnergy Φ a b ell (x t) (y t)
  let v : ℝ → H := fun t => deriv x t
  let g : ℝ → H := fun t => gradient Φ (x t)
  have hxcont : ContinuousOn x (Set.Ici (0 : ℝ)) := hxy.1.continuousOn
  have hycont : ContinuousOn y (Set.Ici (0 : ℝ)) := hxy.2.continuousOn
  have hEcont : ContinuousOn E (Set.Ici (0 : ℝ)) := by
    dsimp [E]
    unfold LyapunovEnergy
    exact ((hΦ.continuous.continuousOn.comp hxcont (fun _ _ => Set.mem_univ _)).const_smul ell).add
      (((hxcont.const_smul a).add (hycont.const_smul b)).norm.pow 2 |>.const_mul (1 / 2 : ℝ))
  let w : ℝ → H := fun t => fderivWithin ℝ x (Set.Ici 0) t 1
  have hw01 : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
    have hcw := hxy.1.continuousOn_fderivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact (hcw.mono Set.Icc_subset_Ici_self).clm_apply continuousOn_const
  have hvsq01 : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) := by
    have hwint : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
      (hw01.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    apply hwint.congr_fun
    · intro t ht
      have hdt : DifferentiableAt ℝ x t := by
        have hd := hxy.1.differentiableOn (by norm_num) t ht.1.le
        exact hd.differentiableAt (Ici_mem_nhds ht.1)
      have hfd := fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht.1.le) hdt
      dsimp [w, v]
      rw [hfd, fderiv_apply_one_eq_deriv]
    · exact measurableSet_Ioc
  have hgscont : ContinuousOn (fun t => ‖g t‖ ^ 2) (Set.Icc (0 : ℝ) 1) := by
    have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      exact (gdin_grad_continuous Φ hΦ).continuousOn.comp
        (hxcont.mono Set.Icc_subset_Ici_self) (fun _ _ => Set.mem_univ _)
    exact hg.norm.pow 2
  have hgsq01 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    hgscont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hvcont_pos : ∀ T : ℝ, 1 ≤ T → ContinuousOn v (Set.Icc (1 : ℝ) T) := by
    intro T hT
    have hw : ContinuousOn w (Set.Icc (1 : ℝ) T) := by
      have hcw := hxy.1.continuousOn_fderivWithin (uniqueDiffOn_Ici 0) (by norm_num)
      exact (hcw.mono (by intro t ht; exact (show 0 ≤ t by linarith [ht.1]))).clm_apply
        continuousOn_const
    apply hw.congr
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hdt : DifferentiableAt ℝ x t := by
      have hd := hxy.1.differentiableOn (by norm_num) t ht0.le
      exact hd.differentiableAt (Ici_mem_nhds ht0)
    have hfd := fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht0.le) hdt
    dsimp [w, v]
    rw [hfd, fderiv_apply_one_eq_deriv]
  have hgscont_pos : ∀ T : ℝ, 1 ≤ T →
      ContinuousOn (fun t => ‖g t‖ ^ 2) (Set.Icc (1 : ℝ) T) := by
    intro T hT
    have hg : ContinuousOn g (Set.Icc (1 : ℝ) T) := by
      exact (gdin_grad_continuous Φ hΦ).continuousOn.comp
        (hxcont.mono (by intro t ht; exact (show 0 ≤ t by linarith [ht.1])))
        (fun _ _ => Set.mem_univ _)
    exact hg.norm.pow 2
  have hEderiv : ∀ t : ℝ, 0 < t → HasDerivAt E
      (-(a + b) * ‖v t‖ ^ 2 - β ^ 2 * b * ‖g t‖ ^ 2) t := by
    intro t ht
    have h := gdin_energy_hasDerivAt Φ β a b ell x y hΦ hxy hsol ht
    have hq : a • x t + b • y t = -(v t + β • g t) := by
      dsimp [v, g]
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht.le
    convert h using 1
    rw [hq]
    dsimp [ell, v, g]
    rw [show ‖gradient Φ (x t)‖ ^ 2 =
        inner ℝ (gradient Φ (x t)) (gradient Φ (x t)) by
          rw [real_inner_self_eq_norm_sq]]
    rw [show ‖deriv x t‖ ^ 2 = inner ℝ (deriv x t) (deriv x t) by
      rw [real_inner_self_eq_norm_sq]]
    rw [show ‖-(deriv x t + β • gradient Φ (x t))‖ ^ 2 =
        inner ℝ (-(deriv x t + β • gradient Φ (x t)))
          (-(deriv x t + β • gradient Φ (x t))) by
      rw [real_inner_self_eq_norm_sq]]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (deriv x t) (gradient Φ (x t))]
    ring
  have htotal : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ((a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2)) ≤
          E 1 - ell * Classical.choose hbounded := by
    intro T hT
    have hvcontT := hvcont_pos T hT
    have hgscontT := hgscont_pos T hT
    have hsumcont : ContinuousOn
        (fun t => (a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2) (Set.Icc 1 T) := by
      exact (hvcontT.norm.pow 2).const_mul (a + b) |>.add
        ((hgscontT.const_mul (β ^ 2 * b)))
    have hsumint : IntervalIntegrable
        (fun t => (a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2)
        MeasureTheory.volume 1 T := hsumcont.intervalIntegrable_of_Icc hT
    have hEint : ∫ t in (1 : ℝ)..T,
        ((a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2) = E 1 - E T := by
      have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
        ((hEcont.mono (by intro t ht; exact (show 0 ≤ t by linarith [ht.1]))).neg)
        (fun t ht => by
          have ht' : 0 < t := by linarith [ht.1]
          (convert (hEderiv t ht').neg using 1; (simp [sub_eq_add_neg, add_comm]; ring)))
        hsumint
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using heq
    have hElower : ell * (Classical.choose hbounded) ≤ E T := by
      dsimp [E, LyapunovEnergy]
      have hΦlower := Classical.choose_spec hbounded (x T)
      have hell : 0 ≤ ell := by
        have ha2b : 0 < a + 2 * b := by linarith
        dsimp [ell]
        exact (mul_pos hβ ha2b).le
      have hkin : 0 ≤ (1 / 2 : ℝ) * ‖a • x T + b • y T‖ ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_left hΦlower hell]
    linarith [hEint]
  have henergy_bound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T, ‖v t‖ ^ 2) ≤
        (E 1 - ell * Classical.choose hbounded) / (a + b) := by
    intro T hT
    have hvint : IntervalIntegrable (fun t => (a + b) * ‖v t‖ ^ 2)
        MeasureTheory.volume 1 T :=
      ((hvcont_pos T hT).norm.pow 2 |>.const_mul (a + b)).intervalIntegrable_of_Icc hT
    have hsumint : IntervalIntegrable
        (fun t => (a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2)
        MeasureTheory.volume 1 T := by
      exact ((hvcont_pos T hT).norm.pow 2).const_mul (a + b) |>.add
        ((hgscont_pos T hT).const_mul (β ^ 2 * b)) |>.intervalIntegrable_of_Icc hT
    have hmono := intervalIntegral.integral_mono_on hT hvint hsumint
      (fun t ht => le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (sq_nonneg β) hb.le) (sq_nonneg _)))
    rw [intervalIntegral.integral_const_mul] at hmono
    apply (le_div_iff₀ hab).2
    exact (by simpa [mul_comm] using hmono.trans (htotal T hT))
  have hgradient_bound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T, ‖g t‖ ^ 2) ≤
        (E 1 - ell * Classical.choose hbounded) / (β ^ 2 * b) := by
    intro T hT
    have hgint : IntervalIntegrable (fun t => β ^ 2 * b * ‖g t‖ ^ 2)
        MeasureTheory.volume 1 T :=
      ((hgscont_pos T hT).const_mul (β ^ 2 * b)).intervalIntegrable_of_Icc hT
    have hsumint : IntervalIntegrable
        (fun t => (a + b) * ‖v t‖ ^ 2 + β ^ 2 * b * ‖g t‖ ^ 2)
        MeasureTheory.volume 1 T := by
      exact ((hvcont_pos T hT).norm.pow 2).const_mul (a + b) |>.add
        ((hgscont_pos T hT).const_mul (β ^ 2 * b)) |>.intervalIntegrable_of_Icc hT
    have hmono := intervalIntegral.integral_mono_on hT hgint hsumint
      (fun t ht => le_add_of_nonneg_left (mul_nonneg hab.le (sq_nonneg _)))
    rw [intervalIntegral.integral_const_mul] at hmono
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hβ) hb)).2
    exact (by simpa [mul_comm] using hmono.trans (htotal T hT))
  have hvsq_tail : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Ioi (1 : ℝ)) := by
    refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((E 1 - ell * Classical.choose hbounded) / (a + b)) 1
      (μ := volume) (l := Filter.atTop) (b := fun n : ℕ => (n : ℝ) + 1) ?_ ?_ ?_
    · intro n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      exact ((hvcont_pos (n + 1) hn).norm.pow 2).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    · filter_upwards [] with n
      convert henergy_bound (n + 1) (by norm_num) using 1
      congr 1
      funext t
      exact Real.norm_of_nonneg (sq_nonneg _)
  have hgsq_tail : IntegrableOn (fun t => ‖g t‖ ^ 2) (Set.Ioi (1 : ℝ)) := by
    refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((E 1 - ell * Classical.choose hbounded) / (β ^ 2 * b)) 1
      (μ := volume) (l := Filter.atTop) (b := fun n : ℕ => (n : ℝ) + 1) ?_ ?_ ?_
    · intro n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
      exact (hgscont_pos (n + 1) hn).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    · filter_upwards [] with n
      convert hgradient_bound (n + 1) (by norm_num) using 1
      congr 1
      funext t
      exact Real.norm_of_nonneg (sq_nonneg _)
  constructor
  · rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hvsq01.union hvsq_tail
  · rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hgsq01.union hgsq_tail

private theorem gdin_hasDerivWithinAt_zero_of_contDiffOn_one
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

/- The existence and uniqueness conclusion in part (i) of Theorem 6.2. -/
theorem gdin_existence_uniqueness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b) :
    ∀ x₀ y₀, (∃ x y : ℝ → H, IsSolution_gDIN Φ β a b x₀ y₀ x y ∧ ContDiffOn ℝ 1 x (Set.Ici 0) ∧
    ContDiffOn ℝ 2 y (Set.Ici 0) ∧
    (∀ x' : ℝ → H, ∀ y' : ℝ → H, IsSolution_gDIN Φ β a b x₀ y₀ x' y' →
    (ContDiffOn ℝ 1 x' (Set.Ici 0) ∧ ContDiffOn ℝ 2 y' (Set.Ici 0)) →
    SameTrajectoryOnNonnegative x y x' y')) := by
  intro x₀ y₀
  let F : H × H → H × H := gdinPhaseField Φ β a b
  have hFloc : LocallyLipschitz F :=
    gdinPhaseField_locallyLipschitz Φ β a b hloclip
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
  obtain ⟨mΦ, hmΦ⟩ := hbounded
  have hTtop : Tmax = (⊤ : WithTop ℝ) := by
    by_contra hnot
    obtain ⟨T, hTmax'⟩ := (WithTop.ne_top_iff_exists).mp hnot
    have hTmax : Tmax = (T : WithTop ℝ) := hTmax'.symm
    have hTpos : 0 < T := by simpa [hTmax] using hYmax.1
    let X : ℝ → H := fun s => (Y s).1
    let Z : ℝ → H := fun s => (Y s).2
    let q : ℝ → H := fun s => a • X s + b • Z s
    let v : ℝ → H := fun s => deriv X s
    let g : ℝ → H := fun s => gradient Φ (X s)
    let ell : ℝ := β * (a + 2 * b)
    let E : ℝ → ℝ := fun s => LyapunovEnergy Φ a b ell (X s) (Z s)
    have hell : 0 < ell := by
      dsimp [ell]
      exact mul_pos hβ (by linarith)
    have hXAt (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        HasDerivAt X ((F (Y t)).1) t := by
      simpa [X] using (hYlocal t ht0 (by simpa [hTmax] using htT)).hasFDerivAt.fst.hasDerivAt
    have hZAt (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        HasDerivAt Z ((F (Y t)).2) t := by
      simpa [Z] using (hYlocal t ht0 (by simpa [hTmax] using htT)).hasFDerivAt.snd.hasDerivAt
    have hXderiv (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        deriv X t = (F (Y t)).1 := (hXAt t ht0 htT).deriv
    have hZderiv (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        deriv Z t = (F (Y t)).2 := (hZAt t ht0 htT).deriv
    have hqeq (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        q t = -(v t + β • g t) := by
      dsimp [q, v, g]
      rw [eq_neg_iff_add_eq_zero]
      have h := hXderiv t ht0 htT
      have hneg : deriv X t = -(β • g t + a • X t + b • Z t) := by
        convert h using 1; simp [F, gdinPhaseField, X, Z, g, sub_eq_add_neg]; abel
      have h0 : deriv X t + (β • g t + a • X t + b • Z t) = 0 :=
        (eq_neg_iff_add_eq_zero.mp hneg)
      simpa [q, v, g, add_assoc, add_left_comm, add_comm] using h0
    have hvform (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        v t = -β • g t - a • X t - b • Z t := by
      have h := hXderiv t ht0 htT
      simpa [v, F, gdinPhaseField, X, Z, g] using h
    have hzform (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
        deriv Z t = -a • X t - b • Z t := by
      have h := hZderiv t ht0 htT
      simpa [F, gdinPhaseField, X, Z] using h
    have hEderiv (t : ℝ) (ht0 : 0 < t) (htT : t < T) :
        HasDerivAt E (-(a + b) * ‖v t‖ ^ 2 - β ^ 2 * b * ‖g t‖ ^ 2) t := by
      have hxAt : HasDerivAt X (v t) t := by
        convert hXAt t ht0.le htT using 1
        exact hXderiv t ht0.le htT
      have hzAt : HasDerivAt Z (deriv Z t) t := by
        convert hZAt t ht0.le htT using 1
        exact hZderiv t ht0.le htT
      have hPhiDeriv : HasFDerivAt Φ (innerSL ℝ (gradient Φ (X t))) (X t) := by
        simpa [innerSL] using
          ((hΦ.differentiable (by norm_num) (X t)).hasGradientAt.hasFDerivAt)
      have hp : HasDerivAt (fun s => Φ (X s))
          (inner ℝ (gradient Φ (X t)) (v t)) t := by
        simpa using hPhiDeriv.comp_hasDerivAt t hxAt
      have hqAt : HasDerivAt q (a • v t + b • deriv Z t) t := by
        simpa [q] using (hxAt.const_smul a).add (hzAt.const_smul b)
      have hEraw : HasDerivAt
          (fun s => ell * Φ (X s) + (1 / 2 : ℝ) * ‖q s‖ ^ 2)
          (ell * inner ℝ (gradient Φ (X t)) (v t) +
            (1 / 2 : ℝ) * (2 * inner ℝ (q t)
              (a • v t + b • deriv Z t))) t := by
        simpa only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using
          (hp.const_smul ell).add ((hqAt.norm_sq).const_smul (1 / 2 : ℝ))
      convert hEraw using 1
      rw [hzform t ht0.le htT]
      rw [show -a • X t - b • Z t = -(q t) by
        dsimp [q]
        module]
      rw [hqeq t ht0.le htT]
      dsimp [g]
      rw [← real_inner_self_eq_norm_sq]
      simp [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_comm]
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      dsimp [ell]
      ring_nf
    let c : ℝ := T / 2
    have hcpos : 0 < c := by dsimp [c]; linarith
    have hcT : c < T := by dsimp [c]; linarith
    have hYcontOn (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        ContinuousOn Y (Set.Icc c r) := by
      intro s hs
      exact (hYlocal s (by linarith [hs.1, hcpos])
        (by simpa [hTmax] using lt_of_le_of_lt hs.2 hrT)).continuousAt.continuousWithinAt
    have hEcontOn (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        ContinuousOn E (Set.Icc c r) := by
      dsimp [E]
      exact ((hΦ.continuous.continuousOn.comp (hYcontOn r hrc hrT).fst
        (fun _ _ => Set.mem_univ _)).const_smul ell).add
        ((((hYcontOn r hrc hrT).fst.const_smul a).add
          ((hYcontOn r hrc hrT).snd.const_smul b)).norm.pow 2 |>.const_mul (1 / 2 : ℝ))
    have hvcontOn (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        ContinuousOn v (Set.Icc c r) := by
      have hFG : ContinuousOn (fun s => (F (Y s)).1) (Set.Icc c r) := by
        exact (hFcont.comp_continuousOn (hYcontOn r hrc hrT)).fst
      apply hFG.congr
      intro s hs
      exact hXderiv s (by linarith [hs.1, hcpos])
        (lt_of_le_of_lt hs.2 hrT)
    have hgcontOn (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        ContinuousOn g (Set.Icc c r) := by
      exact (gdin_grad_continuous Φ hΦ).continuousOn.comp
        (hYcontOn r hrc hrT).fst (fun _ _ => Set.mem_univ _)
    have hsumcontOn (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        ContinuousOn (fun s => (a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2)
          (Set.Icc c r) := by
      exact ((hvcontOn r hrc hrT).norm.pow 2).const_mul (a + b) |>.add
        ((hgcontOn r hrc hrT).norm.pow 2 |>.const_mul (β ^ 2 * b))
    have htotal (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        (∫ s in c..r, ((a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2)) ≤
          E c - ell * mΦ := by
      have hsumint : IntervalIntegrable
          (fun s => (a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2)
          volume c r := (hsumcontOn r hrc hrT).intervalIntegrable_of_Icc hrc
      have hEint : (∫ s in c..r,
          ((a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2)) = E c - E r := by
        have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrc
          (hEcontOn r hrc hrT).neg
          (fun s hs => by
            have hs' : 0 < s := lt_of_lt_of_le hcpos hs.1.le
            have hsT : s < T := lt_trans hs.2 hrT
            have hd := hEderiv s hs' hsT
            have hdn : HasDerivAt (fun x => -E x)
                ((a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2) s := by
              convert hd.neg using 1; simp [sub_eq_add_neg]; ring
            exact hdn) hsumint
        linarith [heq]
      have hEr : ell * mΦ ≤ E r := by
        dsimp [E, LyapunovEnergy]
        have hp := mul_le_mul_of_nonneg_left (hmΦ (X r)) hell.le
        have hk : 0 ≤ (1 / 2 : ℝ) * ‖q r‖ ^ 2 := by positivity
        linarith
      linarith [hEint]
    have hvsq_bound (r : ℝ) (hrc : c ≤ r) (hrT : r < T) :
        (∫ s in c..r, ‖v s‖ ^ 2) ≤ (E c - ell * mΦ) / (a + b) := by
      have hvint : IntervalIntegrable (fun s => (a + b) * ‖v s‖ ^ 2) volume c r :=
        ((hvcontOn r hrc hrT).norm.pow 2 |>.const_mul (a + b)).intervalIntegrable_of_Icc hrc
      have hsumint : IntervalIntegrable
          (fun s => (a + b) * ‖v s‖ ^ 2 + β ^ 2 * b * ‖g s‖ ^ 2)
          volume c r := (hsumcontOn r hrc hrT).intervalIntegrable_of_Icc hrc
      have hm := intervalIntegral.integral_mono_on hrc hvint hsumint
        (fun s hs => le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (sq_nonneg β) hb.le) (sq_nonneg (‖g s‖))))
      rw [intervalIntegral.integral_const_mul] at hm
      apply (le_div_iff₀ hab).2
      simpa [mul_comm] using hm.trans (htotal r hrc hrT)
    let l : Filter ℝ := nhdsWithin T (Set.Ioo c T)
    let bfun : ℝ → ℝ := fun s => if s < T then s else c
    have hl_ne : l.NeBot := by
      rw [show l = nhdsWithin T (Set.Ioo c T) by rfl, nhdsWithin_neBot]
      intro U hU
      have hcl : T ∈ closure (Set.Ioo c T) := by
        rw [closure_Ioo (ne_of_lt hcT)]
        exact ⟨hcT.le, le_rfl⟩
      exact mem_closure_iff_nhds.mp hcl U hU
    have hbfun : Tendsto bfun l (nhds T) := by
      have hid : Tendsto id l (nhds T) :=
        Filter.tendsto_id'.2 nhdsWithin_le_nhds
      apply hid.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [bfun, hs.2]
    have hvsqIoc : IntegrableOn (fun s => ‖v s‖ ^ 2) (Set.Ioc c T) := by
      apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
        (l := l) (b := bfun) (I := (E c - ell * mΦ) / (a + b))
      · intro s
        by_cases hs : s < T
        · by_cases hcs : c ≤ s
          · simpa [bfun, hs] using
              (((hvcontOn s hcs hs).norm.pow 2).integrableOn_Icc.mono_set
                Set.Ioc_subset_Icc_self)
          · simp [bfun, hs, Set.Ioc_eq_empty (fun h => hcs h.le)]
        · simp [bfun, hs]
      · exact hbfun
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hsT : s < T := hs.2
        have hcs : c ≤ s := hs.1.le
        rw [show bfun s = s by simp [bfun, hsT],
          show (fun z => ‖(fun u => ‖v u‖ ^ 2) z‖) = fun z => ‖v z‖ ^ 2 by
            funext z; exact Real.norm_of_nonneg (sq_nonneg _)]
        rw [← intervalIntegral.integral_of_le hcs]
        exact hvsq_bound s hcs hsT
    have hvintIoc : IntegrableOn v (Set.Ioc c T) := by
      have hvmeas : AEStronglyMeasurable v (volume.restrict (Set.Ioc c T)) := by
        simpa [v] using (aestronglyMeasurable_deriv X volume).restrict
      have hvLp : MemLp v 2 (volume.restrict (Set.Ioc c T)) :=
        (memLp_two_iff_integrable_sq_norm hvmeas).2 hvsqIoc
      exact hvLp.integrable (by norm_num)
    let vf : ℝ → H := (Set.Ioc c T).indicator v
    have hvfint : Integrable vf volume := hvintIoc.integrable_indicator measurableSet_Ioc
    have hmeasure : Tendsto (fun s : ℝ => volume (Set.Ioc s T))
        l (nhds 0) := by
      have hT : Tendsto (fun _ : ℝ => T) l (nhds T) := tendsto_const_nhds
      have hid : Tendsto (fun s : ℝ => s) l (nhds T) :=
        tendsto_id.mono_left inf_le_left
      have hs : Tendsto (fun s : ℝ => T - s) l (nhds 0) := by
        simpa using hT.sub hid
      simpa [Real.volume_Ioc, Function.comp_def] using
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs)
    have htail : Tendsto (fun s : ℝ => ∫ z in Set.Ioc s T, vf z)
        l (nhds 0) := by
      exact hvfint.tendsto_setIntegral_nhds_zero hmeasure
    let l0 : Filter ℝ := nhdsWithin T (Set.Ico 0 T)
    have hmeasure0 : Tendsto (fun s : ℝ => volume (Set.Ioc s T))
        l0 (nhds 0) := by
      have hT' : Tendsto (fun _ : ℝ => T) l0 (nhds T) := tendsto_const_nhds
      have hid' : Tendsto (fun s : ℝ => s) l0 (nhds T) :=
        tendsto_id.mono_left inf_le_left
      have hs' : Tendsto (fun s : ℝ => T - s) l0 (nhds 0) := by
        simpa using hT'.sub hid'
      simpa [Real.volume_Ioc, Function.comp_def] using
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs')
    have htail0 : Tendsto (fun s => ∫ z in Set.Ioc s T, vf z)
        l0 (nhds 0) := hvfint.tendsto_setIntegral_nhds_zero hmeasure0
    let Lx : H := X c + ∫ z in Set.Ioc c T, vf z
    have hXrep (s : ℝ) (hs : s ∈ Set.Ioo c T) :
        X s = Lx - ∫ z in Set.Ioc s T, vf z := by
      have hsc : c ≤ s := hs.1.le
      have hst : s ≤ T := hs.2.le
      have hvcs : IntegrableOn v (Set.Ioc c s) :=
        hvintIoc.mono_set (fun z hz => ⟨hz.1, le_trans hz.2 hst⟩)
      have hder := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsc
        ((hYcontOn s hsc hs.2).fst)
        (fun z hz => by
          have hzT : z < T := lt_of_lt_of_le hz.2 hs.2.le
          have hxz := hXAt z (by linarith [hz.1, hcpos]) hzT
          convert hxz using 1
          exact hXderiv z (by linarith [hz.1, hcpos]) hzT)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hsc).2 hvcs)
      have hdecomp : (∫ z in Set.Ioc c T, vf z) =
          (∫ z in Set.Ioc c s, vf z) + (∫ z in Set.Ioc s T, vf z) := by
        have hdisj : Disjoint (Set.Ioc c s) (Set.Ioc s T) := by
          apply Set.Ioc_disjoint_Ioc.mpr
          simp [min_eq_left hst, max_eq_right hsc]
        have hfirst : IntegrableOn vf (Set.Ioc c s) :=
          hvfint.integrableOn.mono_set
            (show Set.Ioc c s ⊆ Set.Ioc c T from
              fun z hz => ⟨hz.1, le_trans hz.2 hst⟩)
        have hsecond : IntegrableOn vf (Set.Ioc s T) :=
          hvfint.integrableOn.mono_set
            (show Set.Ioc s T ⊆ Set.Ioc c T from
              fun z hz => ⟨lt_trans hs.1 hz.1, hz.2⟩)
        calc
          (∫ z in Set.Ioc c T, vf z) =
              ∫ z in Set.Ioc c s ∪ Set.Ioc s T, vf z := by
                rw [Set.Ioc_union_Ioc_eq_Ioc hsc hst]
          _ = (∫ z in Set.Ioc c s, vf z) + (∫ z in Set.Ioc s T, vf z) :=
            MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hfirst hsecond
      have hset : (∫ z in Set.Ioc c s, vf z) = ∫ z in c..s, v z := by
        rw [intervalIntegral.integral_of_le hsc]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro z hz
        exact Set.indicator_of_mem
          (show z ∈ Set.Ioc c T from ⟨hz.1, le_trans hz.2 hst⟩) v
      rw [hset] at hdecomp
      rw [hder] at hdecomp
      dsimp [Lx, X, Z]
      rw [hdecomp]
      module
    have hXlim : Tendsto X l0 (nhds Lx) := by
      have hlim' : Tendsto (fun s => Lx - ∫ z in Set.Ioc s T, vf z) l0 (nhds Lx) := by
        simpa using (tendsto_const_nhds.sub htail0)
      apply hlim'.congr'
      have hIoo : Set.Ioo c T ∈ l0 := by
        apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        refine ⟨Set.Ioi c, Ioi_mem_nhds hcT, ?_⟩
        intro s hs
        exact ⟨hs.1, hs.2.2⟩
      filter_upwards [hIoo] with s hs
      exact (hXrep s hs).symm
    have hEcontIco : ContinuousOn E (Set.Ico 0 T) := by
      have hYc : ContinuousOn Y (Set.Ico 0 T) := by
        intro s hs
        exact (hYlocal s hs.1 (by simpa [hTmax] using hs.2)).continuousAt.continuousWithinAt
      dsimp [E]
      exact ((hΦ.continuous.continuousOn.comp hYc.fst
        (fun _ _ => Set.mem_univ _)).const_smul ell).add
        (((hYc.fst.const_smul a).add (hYc.snd.const_smul b)).norm.pow 2 |>.const_mul (1 / 2 : ℝ))
    have hEanti : AntitoneOn E (Set.Ico 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ico 0 T)
      · exact hEcontIco
      · intro s hs
        have hs' : s ∈ Set.Ioo (0 : ℝ) T := by simpa [interior_Ico] using hs
        exact (hEderiv s hs'.1 hs'.2).differentiableAt.differentiableWithinAt
      · intro s hs
        have hs' : s ∈ Set.Ioo (0 : ℝ) T := by simpa [interior_Ico] using hs
        rw [(hEderiv s hs'.1 hs'.2).deriv]
        nlinarith [mul_nonneg hab.le (sq_nonneg ‖v s‖),
          mul_nonneg (mul_nonneg (sq_nonneg β) hb.le) (sq_nonneg ‖g s‖)]
    let Q : ℝ := 2 * (E 0 - ell * mΦ) + 1
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      have hE0 : ell * mΦ ≤ E 0 := by
        dsimp [E, LyapunovEnergy]
        have hp := mul_le_mul_of_nonneg_left (hmΦ (X 0)) hell.le
        have hk : 0 ≤ (1 / 2 : ℝ) * ‖q 0‖ ^ 2 := by positivity
        linarith
      linarith
    have hqbound (s : ℝ) (hs : 0 ≤ s) (hsT : s < T) : ‖q s‖ ≤ Q := by
      have hEs : E s ≤ E 0 := hEanti ⟨le_rfl, hTpos⟩ ⟨hs, hsT⟩ hs
      have hps := mul_le_mul_of_nonneg_left (hmΦ (X s)) hell.le
      have hsq : ‖q s‖ ^ 2 ≤ 2 * (E 0 - ell * mΦ) := by
        dsimp [E, LyapunovEnergy] at hEs ⊢
        linarith
      dsimp [Q]
      nlinarith [sq_nonneg (‖q s‖ - 1), norm_nonneg (q s)]
    have hYlim : ∃ lz : H, Tendsto Y (nhdsWithin T (Set.Ico 0 T))
        (nhds (Lx, lz)) := by
      obtain ⟨lz, hlz⟩ := tendsto_at_right_of_norm_deriv_le
        (u := Z) (du := fun s : ℝ => -q s) hTpos hQ
        (fun s hs0 hsT => by
          have hz := hZAt s hs0 hsT
          convert hz using 1
          calc
            -q s = -a • X s - b • Z s := by dsimp [q]; module
            _ = deriv Z s := (hzform s hs0 hsT).symm
            _ = (F (Y s)).2 := hZderiv s hs0 hsT
          )
        (fun s hs0 hsT => by
          simpa [norm_neg] using hqbound s hs0 hsT)
      refine ⟨lz, ?_⟩
      simpa [nhds_prod_eq] using hXlim.prodMk hlz
    have hdom : {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < Tmax} = Set.Ico 0 T := by
      ext s
      simp [hTmax]
    obtain ⟨lz, hYlim⟩ := hYlim
    have hYlim' : Tendsto Y
        (nhdsWithin T {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < Tmax})
        (nhds (Lx, lz)) := by
      rw [hdom]
      exact hYlim
    obtain ⟨S, hTS, W, hW, hWY⟩ := hYextend T hTmax _ hYlim'
    have hsub : {s : ℝ | 0 ≤ s ∧ (s : WithTop ℝ) < Tmax} ⊆ Set.Ico 0 S := by
      intro s hs
      refine ⟨hs.1, ?_⟩
      have hsT : s < T := by simpa [hTmax] using hs.2
      exact hsT.trans hTS
    have hmax := hYmax.2.2 (Set.Ico 0 S) W Set.ordConnected_Ico
      ⟨le_rfl, hTpos.trans hTS⟩ hW hsub
      (fun s hs0 hsS => (hWY s hs0 (by simpa [hTmax] using hsS)).symm)
    have hbad := hmax ⟨⟨hTpos.le, hTS⟩, hTpos.le⟩
    exact (lt_irrefl T) (by simpa [hTmax] using hbad.2)
  have hYglobal (t : ℝ) (ht : 0 ≤ t) : HasDerivAt Y (F (Y t)) t :=
    hYlocal t ht (by simp [hTtop])
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
  have hFYcontIci : ContinuousOn (fun t => F (Y t)) (Set.Ici (0 : ℝ)) :=
    hFcont.comp_continuousOn hYcontIci
  have hxC1 : ContDiffOn ℝ 1 x (Set.Ici 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hxderiv t ht).differentiableAt.differentiableWithinAt,
      ?_, ?_⟩
    · intro h
      simp at h
    · have heq : ∀ t, t ∈ Set.Ici (0 : ℝ) → derivWithin x (Set.Ici 0) t = (F (Y t)).1 := by
        intro t ht
        exact (hxderiv t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
      exact contDiffOn_zero.mpr (hFYcontIci.fst.congr heq)
  have hyC1 : ContDiffOn ℝ 1 y (Set.Ici 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hyderiv t ht).differentiableAt.differentiableWithinAt,
      ?_, ?_⟩
    · intro h
      simp at h
    · have heq : ∀ t, t ∈ Set.Ici (0 : ℝ) → derivWithin y (Set.Ici 0) t = (F (Y t)).2 := by
        intro t ht
        exact (hyderiv t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
      exact contDiffOn_zero.mpr (hFYcontIci.snd.congr heq)
  have hyprimeC1 : ContDiffOn ℝ 1 (fun t => -(a • x t) - b • y t) (Set.Ici 0) :=
    (hxC1.const_smul a).neg.sub (hyC1.const_smul b)
  have hyderiv' (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivAt y (-(a • x t) - b • y t) t := by
    have h := hyderiv t ht
    simpa [F, gdinPhaseField, x, y] using h
  have hyC2 : ContDiffOn ℝ 2 y (Set.Ici 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hyderiv' t ht).differentiableAt.differentiableWithinAt,
      ?_, ?_⟩
    · intro h
      simp at h
    · have heq : ∀ t, t ∈ Set.Ici (0 : ℝ) → derivWithin y (Set.Ici 0) t = -(a • x t) - b • y t := by
        intro t ht
        exact (hyderiv' t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
      exact hyprimeC1.congr heq
  have hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have h := (hxderiv t ht).deriv
      dsimp [F, gdinPhaseField, x, y] at h ⊢
      rw [h]
      module
    · intro t ht
      have h := (hyderiv t ht).deriv
      dsimp [F, gdinPhaseField, x, y] at h ⊢
      rw [h]
      module
    · simpa [x] using congrArg Prod.fst hYmax.2.1.2.1
    · simpa [y] using congrArg Prod.snd hYmax.2.1.2.1
  refine ⟨x, y, hsol, hxC1, hyC2, ?_⟩
  intro x' y' hsol' hreg'
  let Y' : ℝ → H × H := fun t => (x' t, y' t)
  have hyC1' : ContDiffOn ℝ 1 y' (Set.Ici 0) := hreg'.2.of_le (by norm_num)
  have hY'cont : ContinuousOn Y' (Set.Ici 0) := by
    exact hreg'.1.continuousOn.prodMk hyC1'.continuousOn
  have hY'zero : Y' 0 = (x₀, y₀) := by
    dsimp [Y']
    exact Prod.ext (hsol'.2.2.1) (hsol'.2.2.2)
  have hY'ode_pos (t : ℝ) (ht : 0 < t) : HasDerivAt Y' (F (Y' t)) t := by
    have hxdiff : DifferentiableAt ℝ x' t :=
      (hreg'.1.differentiableOn (by norm_num) t ht.le).differentiableAt (Ici_mem_nhds ht)
    have hydiff : DifferentiableAt ℝ y' t :=
      (hreg'.2.differentiableOn (by norm_num) t ht.le).differentiableAt (Ici_mem_nhds ht)
    have hxneg : deriv x' t =
        -(β • gradient Φ (x' t) + a • x' t + b • y' t) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol'.1 t ht.le)
    have hxvel : deriv x' t = -β • gradient Φ (x' t) - a • x' t - b • y' t := by
      calc
        deriv x' t = -(β • gradient Φ (x' t) + a • x' t + b • y' t) := hxneg
        _ = -β • gradient Φ (x' t) - a • x' t - b • y' t := by module
    have hyneg : deriv y' t = -(a • x' t + b • y' t) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol'.2.1 t ht.le)
    have hyvel : deriv y' t = -a • x' t - b • y' t := by
      calc
        deriv y' t = -(a • x' t + b • y' t) := hyneg
        _ = -a • x' t - b • y' t := by module
    have hfield : F (Y' t) = (deriv x' t, deriv y' t) := by
      apply Prod.ext
      · dsimp [F, gdinPhaseField, Y']
        exact hxvel.symm
      · dsimp [F, gdinPhaseField, Y']
        exact hyvel.symm
    rw [hfield]
    simpa [Y'] using hxdiff.hasDerivAt.prodMk hydiff.hasDerivAt
  have hY'right (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt Y' (F (Y' t)) (Set.Ici t) t := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · have hF'cont : ContinuousOn (fun s => F (Y' s)) (Set.Ici 0) :=
        hFcont.comp_continuousOn hY'cont
      exact gdin_hasDerivWithinAt_zero_of_contDiffOn_one
        (hreg'.1.prodMk hyC1') hF'cont hY'ode_pos
    · exact (hY'ode_pos t ht).hasDerivWithinAt
  have hYright (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt Y (F (Y t)) (Set.Ici t) t :=
    (hYglobal t ht).hasDerivWithinAt
  have hpair : Set.EqOn Y' Y (Set.Ici 0) := by
    intro t ht
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · exact hY'zero.trans hYmax.2.1.2.1.symm
    · rcases hFnhds (x₀, y₀) with ⟨U, hU, L, hL, hLip⟩
      let K : NNReal := ⟨L, hL⟩
      have hLipU : LipschitzOnWith K F U := by
        apply LipschitzOnWith.of_dist_le_mul
        intro z hz w hw
        simpa only [dist_eq_norm] using hLip z hz w hw
      have hUY' : U ∈ nhds (Y' 0) := by simpa [hY'zero] using hU
      have hUY : U ∈ nhds (Y 0) := by simpa [hYmax.2.1.2.1] using hU
      have hY'near : Y' ⁻¹' U ∈ nhdsWithin 0 (Set.Ici 0) :=
        (hY'cont 0 (Set.mem_Ici.mpr le_rfl)) hUY'
      have hYnear : Y ⁻¹' U ∈ nhdsWithin 0 (Set.Ici 0) :=
        ((hYglobal 0 le_rfl).continuousAt.continuousWithinAt) hUY
      obtain ⟨δY', hδY', hδY'U⟩ := Metric.mem_nhdsWithin_iff.mp hY'near
      obtain ⟨δY, hδY, hδYU⟩ := Metric.mem_nhdsWithin_iff.mp hYnear
      let δ : ℝ := min (t / 2) (min (δY' / 2) (δY / 2))
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
      have hδt : δ < t := by
        have h := min_le_left (t / 2) (min (δY' / 2) (δY / 2))
        linarith
      have hδY'' : δ < δY' := by
        have h := le_trans (min_le_right (t / 2) (min (δY' / 2) (δY / 2)))
          (min_le_left (δY' / 2) (δY / 2))
        linarith
      have hδY''' : δ < δY := by
        have h := le_trans (min_le_right (t / 2) (min (δY' / 2) (δY / 2)))
          (min_le_right (δY' / 2) (δY / 2))
        linarith
      have hY'U (r : ℝ) (hr : r ∈ Set.Icc 0 δ) : Y' r ∈ U := by
        apply hδY'U
        constructor
        · rw [Metric.mem_ball, Real.dist_eq]
          simp only [sub_zero, abs_of_nonneg hr.1]
          exact hr.2.trans_lt hδY''
        · exact hr.1
      have hYU (r : ℝ) (hr : r ∈ Set.Icc 0 δ) : Y r ∈ U := by
        apply hδYU
        constructor
        · rw [Metric.mem_ball, Real.dist_eq]
          simp only [sub_zero, abs_of_nonneg hr.1]
          exact hr.2.trans_lt hδY'''
        · exact hr.1
      have hlocalEq := ODE_solution_unique_of_mem_Icc_right
        (v := fun _ : ℝ => F) (s := fun _ => U) (K := K)
        (fun _ _ => hLipU)
        (hY'cont.mono Set.Icc_subset_Ici_self)
        (fun r hr => hY'right r hr.1) (fun r hr => hY'U r ⟨hr.1, hr.2.le⟩)
        (hYcontIci.mono Set.Icc_subset_Ici_self)
        (fun r hr => hYright r hr.1) (fun r hr => hYU r ⟨hr.1, hr.2.le⟩)
        (hY'zero.trans hYmax.2.1.2.1.symm)
      have hseed : Y' (δ / 2) = Y (δ / 2) :=
        hlocalEq ⟨by linarith, by linarith⟩
      have hprop := ode_eqOn_Ioo_of_locally_lipschitz F hFnhds
        (show δ / 2 ∈ Set.Ioo 0 (t + 1) by constructor <;> linarith)
        Y' Y
        (fun r hr => hY'ode_pos r hr.1)
        (fun r hr => hYglobal r hr.1.le)
        hseed
      exact hprop ⟨ht, by linarith⟩
  intro t ht
  constructor
  · simpa [x, Y'] using (congrArg Prod.fst (hpair ht)).symm
  · simpa [y, Y'] using (congrArg Prod.snd (hpair ht)).symm

/-- The Lyapunov energy conclusions in part (ii) of Theorem 6.2. -/
theorem gdin_lyapunov_energy_properties
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∀ ell : ℝ,
      β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell →
      ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 →
        AntitoneOn (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) (Set.Ici 0) ∧
        (∃ m : ℝ, ∀ t : ℝ, 0 ≤ t → m ≤ LyapunovEnergy Φ a b ell (x t) (y t)) ∧
        ∃ l : ℝ, Tendsto (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) atTop (nhds l) := by
  intro ell hlow hhigh
  have hxcont : ContinuousOn x (Set.Ici (0 : ℝ)) := hxy.1.continuousOn
  have hycont : ContinuousOn y (Set.Ici (0 : ℝ)) := hxy.2.continuousOn
  have hEcont : ContinuousOn
      (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) (Set.Ici (0 : ℝ)) := by
    unfold LyapunovEnergy
    exact ((hΦ.continuous.continuousOn.comp hxcont (fun _ _ => Set.mem_univ _)).const_smul ell).add
      (((hxcont.const_smul a).add (hycont.const_smul b)).norm.pow 2 |>.const_mul (1 / 2 : ℝ))
  have hEdiff : DifferentiableOn ℝ
      (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) (Set.Ioi (0 : ℝ)) :=
    fun t ht =>
    (gdin_energy_hasDerivAt Φ β a b ell x y hΦ hxy hsol ht).differentiableAt.differentiableWithinAt
  have hEnonpos : ∀ t ∈ Set.Ioi (0 : ℝ),
      deriv (fun s => LyapunovEnergy Φ a b ell (x s) (y s)) t ≤ 0 := by
    intro t ht
    rw [gdin_energy_hasDerivAt Φ β a b ell x y hΦ hxy hsol ht |>.deriv]
    exact gdin_admissible_energy_deriv_nonpos β a b ell hβ hb hab hlow hhigh
      (gradient Φ (x t)) (a • x t + b • y t)
  have hanti : AntitoneOn
      (fun t => LyapunovEnergy Φ a b ell (x t) (y t)) (Set.Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hEcont
    · simpa [interior_Ici] using hEdiff
    simpa [interior_Ici] using hEnonpos
  have hell : 0 ≤ ell :=
    (mul_nonneg hβ.le (sq_nonneg _)).trans hlow
  rcases hbounded with ⟨m, hm⟩
  have hlower : ∃ m' : ℝ, ∀ t : ℝ, 0 ≤ t → m' ≤
      LyapunovEnergy Φ a b ell (x t) (y t) := by
    refine ⟨ell * m, ?_⟩
    intro t ht
    unfold LyapunovEnergy
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖a • x t + b • y t‖ ^ 2 := by positivity
    linarith [mul_le_mul_of_nonneg_left (hm (x t)) hell]
  refine ⟨hanti, hlower, ?_⟩
  exact antitoneOn_Ici_bddBelow_tendsto_atTop hanti hlower

/-- The L2 conclusion for the x derivative in part (ii) of Theorem 6.2. -/
theorem gdin_x_derivative_memL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    MemL2OnNonnegative (deriv x) := by
  unfold MemL2OnNonnegative
  have hsquares := gdin_dissipation_integrableOn_Ioi Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol
  have hsq : IntegrableOn (fun t => ‖deriv x t‖ ^ 2)
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hsquares.1
  let w : ℝ → H := fun t => fderivWithin ℝ x (Set.Ici 0) t 1
  have hw : ContinuousOn w (Set.Ici (0 : ℝ)) := by
    have hcw := hxy.1.continuousOn_fderivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact hcw.clm_apply continuousOn_const
  have hne : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (0 : ℝ))), t ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ 0} = ({0} : Set ℝ) := by ext; simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton 0)]
    simp
  have hwd : w =ᶠ[ae (volume.restrict (Set.Ici (0 : ℝ)))] deriv x := by
    filter_upwards [ae_restrict_mem measurableSet_Ici, hne] with t ht htn
    have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm htn)
    have hdt : DifferentiableAt ℝ x t := by
      have hd := hxy.1.differentiableOn (by norm_num) t ht
      exact hd.differentiableAt (Ici_mem_nhds ht0)
    have hfd := fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) hdt
    dsimp [w]
    rw [hfd, fderiv_apply_one_eq_deriv]
  have hwae : AEStronglyMeasurable w (volume.restrict (Set.Ici (0 : ℝ))) :=
    hw.aestronglyMeasurable measurableSet_Ici
  have hae : AEStronglyMeasurable (deriv x) (volume.restrict (Set.Ici (0 : ℝ))) :=
    hwae.congr hwd
  exact (memLp_two_iff_integrable_sq_norm hae).2 hsq

/-- The L2 conclusion for the gradient in part (ii) of Theorem 6.2. -/
theorem gdin_gradient_memL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    MemL2OnNonnegative (fun t => gradient Φ (x t)) := by
  unfold MemL2OnNonnegative
  have hsquares := gdin_dissipation_integrableOn_Ioi Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol
  have hsq : IntegrableOn (fun t => ‖gradient Φ (x t)‖ ^ 2)
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hsquares.2
  have hgcont : ContinuousOn (fun t => gradient Φ (x t)) (Set.Ici (0 : ℝ)) :=
    (gdin_grad_continuous Φ hΦ).continuousOn.comp hxy.1.continuousOn
      (fun _ _ => Set.mem_univ _)
  have hga : AEStronglyMeasurable (fun t => gradient Φ (x t))
      (volume.restrict (Set.Ici (0 : ℝ))) :=
    hgcont.aestronglyMeasurable measurableSet_Ici
  exact (memLp_two_iff_integrable_sq_norm hga).2 hsq

/-- The convergence of the potential value in part (ii) of Theorem 6.2. -/
theorem gdin_phi_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
  let ellLow : ℝ := β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2
  let ellHigh : ℝ := β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2
  have hgap : ellLow < ellHigh := by
    have hs : 0 < Real.sqrt (a + b) := Real.sqrt_pos.2 hab
    have hb' : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    dsimp [ellLow, ellHigh]
    apply mul_lt_mul_of_pos_left _ hβ
    nlinarith [mul_pos hs hb']
  have hconv : ∀ ell : ℝ, ellLow ≤ ell → ell ≤ ellHigh →
      ∃ l : ℝ, Tendsto (fun t => LyapunovEnergy Φ a b ell (x t) (y t))
        atTop (nhds l) := by
    intro ell hlow hhigh
    exact (gdin_lyapunov_energy_properties Φ β a b hΦ hbounded hβ hb hab
      x₀ y₀ x y hxy hsol ell hlow hhigh).2.2
  rcases hconv ellLow le_rfl hgap.le with ⟨Llow, hLlow⟩
  rcases hconv ellHigh hgap.le le_rfl with ⟨Lhigh, hLhigh⟩
  refine ⟨(1 / (ellHigh - ellLow)) * (Lhigh - Llow), ?_⟩
  have hscaled := (hLhigh.sub hLlow).const_mul (1 / (ellHigh - ellLow))
  refine hscaled.congr' ?_
  filter_upwards with t
  have hgap_ne : ellHigh - ellLow ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  have hs_ne : Real.sqrt (a + b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  have hb_ne : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  dsimp [LyapunovEnergy, ellLow, ellHigh]
  field_simp [hgap_ne, hs_ne, hb_ne]
  ring_nf
  rw [show
    β * Real.sqrt (a + b) * Real.sqrt b * Φ (x t) *
        (Real.sqrt (a + b))⁻¹ * (Real.sqrt b)⁻¹ * 2 =
      β * Φ (x t) * (Real.sqrt (a + b) * (Real.sqrt (a + b))⁻¹) *
        (Real.sqrt b * (Real.sqrt b)⁻¹) * 2 by ring]
  simp [hs_ne, hb_ne]

/-- The residual convergence conclusion in part (ii) of Theorem 6.2. -/
theorem gdin_residual_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
  let ell : ℝ := β * (a + 2 * b)
  let q : ℝ → H := fun t => a • x t + b • y t
  let v : ℝ → H := fun t => deriv x t
  let g : ℝ → H := fun t => gradient Φ (x t)
  have hsquares := gdin_dissipation_integrableOn_Ioi Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol
  have hqcont : ContinuousOn q (Set.Ioi (0 : ℝ)) := by
    exact (hxy.1.continuousOn.mono Set.Ioi_subset_Ici_self |>.const_smul a).add
      (hxy.2.continuousOn.mono Set.Ioi_subset_Ici_self |>.const_smul b)
  have hqint : IntegrableOn (fun t => ‖q t‖ ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn
        (fun t => 2 * ‖v t‖ ^ 2 + 2 * β ^ 2 * ‖g t‖ ^ 2) (Set.Ioi (0 : ℝ)) := by
      exact (hsquares.1.const_mul 2).add (hsquares.2.const_mul (2 * β ^ 2))
    have hqae : AEStronglyMeasurable (fun t => ‖q t‖ ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (hqcont.norm.pow 2).aestronglyMeasurable measurableSet_Ioi
    apply hdom.mono' hqae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hqrel : q t = -(v t + β • g t) := by
      dsimp [q, v, g]
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht.le
    rw [hqrel, norm_neg]
    have hn : ‖v t + β • g t‖ ≤ ‖v t‖ + β * ‖g t‖ := by
      simpa [norm_smul, abs_of_pos hβ] using norm_add_le (v t) (β • g t)
    have hs : 0 ≤ ‖v t + β • g t‖ := norm_nonneg _
    have hr : 0 ≤ ‖v t‖ := norm_nonneg _
    have hg : 0 ≤ ‖g t‖ := norm_nonneg _
    calc
      ‖‖v t + β • g t‖ ^ 2‖ = ‖v t + β • g t‖ ^ 2 :=
        Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (‖v t‖ + β * ‖g t‖) ^ 2 := by nlinarith
      _ ≤ 2 * ‖v t‖ ^ 2 + 2 * β ^ 2 * ‖g t‖ ^ 2 := by
        nlinarith [sq_nonneg (‖v t‖ - β * ‖g t‖)]
  have hmidlow : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  have hmidhigh : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  rcases (gdin_lyapunov_energy_properties Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol ell hmidlow hmidhigh).2.2 with ⟨L, hL⟩
  rcases gdin_phi_limit Φ β a b hΦ hbounded hβ hb hab x₀ y₀ x y hxy hsol with
    ⟨P, hP⟩
  have hdiff := hL.sub ((tendsto_const_nhds : Tendsto (fun _ : ℝ => ell) atTop (nhds ell)).mul hP)
  have hq2lim : Tendsto (fun t => ‖q t‖ ^ 2) atTop
      (nhds (2 * (L - ell * P))) := by
    have hscaled := hdiff.const_mul (2 : ℝ)
    refine hscaled.congr' ?_
    filter_upwards with t
    dsimp [q, ell, LyapunovEnergy]
    ring
  have hq2int : IntegrableAtFilter (fun t => ‖q t‖ ^ 2) atTop volume := by
    exact ⟨Set.Ioi (0 : ℝ), Ioi_mem_atTop 0, hqint⟩
  have htail_full : ∀ s ∈ (atTop : Filter ℝ), volume s = ⊤ := by
    intro s hs
    rcases mem_atTop_sets.mp hs with ⟨c, hc⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := c)]
    exact measure_mono hc
  have hq2zero : 2 * (L - ell * P) = 0 :=
    hq2int.eq_zero_of_tendsto htail_full hq2lim
  have hqnormlim : Tendsto (fun t => ‖q t‖) atTop (nhds 0) := by
    have hsqrt : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    have hq2lim0 : Tendsto (fun t => ‖q t‖ ^ 2) atTop (nhds 0) := by
      simpa [hq2zero] using hq2lim
    have hsq := hsqrt.comp hq2lim0
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsq
  have hqzero : Tendsto q atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hqnormlim
  have hreszero : Tendsto (fun t => -q t) atTop (nhds 0) := by simpa using hqzero.neg
  apply hreszero.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hqrel : q t = -(v t + β • g t) := by
    dsimp [q, v, g]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht
  dsimp [q, v, g] at hqrel ⊢
  rw [hqrel]
  simp

private theorem gdin_uniformContinuousOn_sq_integrable_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (huc : UniformContinuousOn f (Set.Ici (0 : ℝ)))
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Set.Ici (0 : ℝ))) :
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
  have hlow : ∀ z ∈ Set.Ioc u (u + δ / 2), (ε / 2) ^ 2 ≤ ‖f z‖ ^ 2 := by
    intro z hz
    have hzu : |z - u| < δ := by
      rw [abs_of_nonneg (le_of_lt (sub_pos.mpr hz.1))]
      linarith [hz.2, hδ]
    have hdist : dist (f z) (f u) < ε / 2 := by
      exact hδprop z (le_trans hu0 (le_of_lt hz.1)) u hu0
        (by simpa [Real.dist_eq] using hzu)
    have hub : ε ≤ ‖f u‖ := by simpa using hubad
    have htri : ‖f u‖ ≤ ‖f z‖ + ‖f z - f u‖ := by
      calc
        ‖f u‖ = ‖f z + (f u - f z)‖ := by congr 1; abel
        _ ≤ ‖f z‖ + ‖f u - f z‖ := norm_add_le _ _
        _ = ‖f z‖ + ‖f z - f u‖ := by rw [norm_sub_rev]
    have hnorm : ε / 2 < ‖f z‖ := by
      rw [dist_eq_norm] at hdist
      linarith
    nlinarith
  have hfIoc : IntegrableOn (fun z : ℝ => ‖f z‖ ^ 2) (Set.Ioc u (u + δ / 2)) :=
    hint.mono_set (by intro z hz; exact le_trans hu0 hz.1.le)
  have hconst : IntegrableOn (fun _ : ℝ => (ε / 2) ^ 2)
      (Set.Ioc u (u + δ / 2)) := integrableOn_const measure_Ioc_lt_top.ne
  have hIoc : (ε / 2) ^ 2 * (δ / 2) ≤
      ∫ z in Set.Ioc u (u + δ / 2), ‖f z‖ ^ 2 := by
    have hm := setIntegral_mono_on hconst hfIoc measurableSet_Ioc (fun z hz => hlow z hz)
    simpa [integral_const, measureReal_def, smul_eq_mul,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ δ / 2), mul_comm] using hm
  have hsub : Set.Ioc u (u + δ / 2) ⊆ Set.Ici (N : ℝ) := by
    intro z hz
    exact le_trans huN (le_of_lt hz.1)
  have htail_ge : (∫ z in Set.Ioc u (u + δ / 2), ‖f z‖ ^ 2) ≤
      ∫ z in Set.Ici (N : ℝ), ‖f z‖ ^ 2 := by
    apply setIntegral_mono_set
      (hint.mono_set (by
        intro z hz
        have hz' : (N : ℝ) ≤ z := by simpa only [Set.mem_Ici] using hz
        exact (Nat.cast_nonneg N).trans hz'))
      (Filter.Eventually.of_forall (fun z => sq_nonneg (‖f z‖)))
    exact Filter.Eventually.of_forall (fun z hz => hsub hz)
  have htail_nonneg : 0 ≤ ∫ z in Set.Ici (N : ℝ), ‖f z‖ ^ 2 := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => sq_nonneg (‖f z‖)))
  have hdistN : dist (∫ z in Set.Ici (N : ℝ), ‖f z‖ ^ 2) 0 <
      (ε / 2) ^ 2 * (δ / 2) := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg htail_nonneg] at hdistN
  linarith [hIoc, htail_ge]

private theorem gdin_contDiffOn_two_of_hasDerivAt_of_contDiffOn_one
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {f f' : ℝ → H}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContDiffOn ℝ 1 f' s) :
    ContDiffOn ℝ 2 f s := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact hf'.congr (fun t ht => heq t ht)

private theorem gdin_contDiffOn_one_of_hasDerivAt_of_continuousOn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {f f' : ℝ → H}
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hderiv : ∀ t, t ∈ s → HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' s) :
    ContDiffOn ℝ 1 f s := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin hs]
  refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro h
    simp at h
  · have heq : ∀ t, t ∈ s → derivWithin f s t = f' t := by
      intro t ht
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (hs t ht)
    exact contDiffOn_zero.mpr (hf'.congr (fun t ht => heq t ht))

private theorem gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    {K : NNReal} (hLip : LipschitzOnWith K f (Set.Ioi (0 : ℝ)))
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) :
    UniformContinuousOn f (Set.Ici (0 : ℝ)) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁prop⟩ := Metric.uniformContinuousOn_iff.mp
    hLip.uniformContinuousOn (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hδ₂prop⟩ := Metric.continuousWithinAt_iff.mp
    (hcont.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp))
      (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := by simpa only [Set.mem_Ici] using hx
  have hy' : (0 : ℝ) ≤ y := by simpa only [Set.mem_Ici] using hy
  rcases eq_or_lt_of_le hx' with rfl | hxpos
  · rcases eq_or_lt_of_le hy' with rfl | hypos
    · simpa using hε
    · have hxy₂ : dist (0 : ℝ) y < δ₂ :=
        lt_of_lt_of_le hxy (min_le_right δ₁ δ₂)
      have hdy : dist y 0 < δ₂ := by simpa [dist_comm] using hxy₂
      have h := hδ₂prop hy hdy
      calc
        dist (f 0) (f y) = dist (f y) (f 0) := dist_comm _ _
        _ < ε / 2 := h
        _ < ε := by linarith
  · rcases eq_or_lt_of_le hy' with rfl | hypos
    · have hxy₂ : dist x (0 : ℝ) < δ₂ :=
        lt_of_lt_of_le hxy (min_le_right δ₁ δ₂)
      have hdx : dist x 0 < δ₂ := hxy₂
      have h := hδ₂prop hx hdx
      exact h.trans (by linarith)
    · exact (hδ₁prop x (by exact hxpos) y (by exact hypos)
        (lt_of_lt_of_le hxy (min_le_left _ _))).trans (by linarith)

/- The bounded-trajectory conclusions in part (iii) of Theorem 6.2. -/
theorem gdin_bounded_asymptotics
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y)
    (hxbounded : BoundedOnNonnegative x) :
    BoundedOnNonnegative (deriv x) ∧
      BoundedOnNonnegative (fun t => gradient Φ (x t)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
  let q : ℝ → H := fun t => a • x t + b • y t
  let v : ℝ → H := fun t => deriv x t
  let g : ℝ → H := fun t => gradient Φ (x t)
  let ell : ℝ := β * (a + 2 * b)
  have hmidlow : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  have hmidhigh : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  have hell : 0 < ell := by
    dsimp [ell]
    exact mul_pos hβ (by linarith)
  rcases (gdin_lyapunov_energy_properties Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol ell hmidlow hmidhigh).1 with hEanti
  obtain ⟨mΦ, hmΦ⟩ := hbounded
  rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨Cx, hCx⟩
  have hxnorm : ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ Cx := by
    intro t ht
    exact hCx _ ⟨t, ht, rfl⟩
  rcases hloclip (x '' Set.Ici (0 : ℝ)) hxbounded with ⟨K, hK⟩
  have hgrad_bound : ∀ t : ℝ, 0 ≤ t →
      ‖g t‖ ≤ (K : ℝ) * (Cx + ‖x 0‖) + ‖g 0‖ := by
    intro t ht
    have hKt := hK.norm_sub_le ⟨t, ht, rfl⟩ ⟨0, by simp, rfl⟩
    dsimp [g] at hKt ⊢
    calc
      ‖gradient Φ (x t)‖ = ‖gradient Φ (x t) - gradient Φ (x 0) + gradient Φ (x 0)‖ := by
        congr 1; abel
      _ ≤ ‖gradient Φ (x t) - gradient Φ (x 0)‖ + ‖gradient Φ (x 0)‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖x t - x 0‖ + ‖gradient Φ (x 0)‖ := by gcongr
      _ ≤ (K : ℝ) * (Cx + ‖x 0‖) + ‖gradient Φ (x 0)‖ := by
        gcongr
        calc ‖x t - x 0‖ ≤ ‖x t‖ + ‖x 0‖ := norm_sub_le _ _
          _ ≤ Cx + ‖x 0‖ := by
            simpa [add_comm] using add_le_add_right (hxnorm t ht) ‖x 0‖
  let Cg : ℝ := (K : ℝ) * (Cx + ‖x 0‖) + ‖g 0‖
  have hgbdd : BoundedOnNonnegative g := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max Cg 0, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact (hgrad_bound t ht).trans (le_max_left _ _)
  have hE0 : ∀ t : ℝ, 0 ≤ t →
      LyapunovEnergy Φ a b ell (x t) (y t) ≤ LyapunovEnergy Φ a b ell (x 0) (y 0) := by
    intro t ht
    exact hEanti (by simp) ht ht
  have hq_bound : ∀ t : ℝ, 0 ≤ t → ‖q t‖ ^ 2 ≤
      2 * (LyapunovEnergy Φ a b ell (x 0) (y 0) - ell * mΦ) := by
    intro t ht
    have hpot : ell * mΦ ≤ ell * Φ (x t) :=
      mul_le_mul_of_nonneg_left (hmΦ (x t)) hell.le
    have hEt := hE0 t ht
    have hkin0 : 0 ≤ (1 / 2 : ℝ) * ‖a • x 0 + b • y 0‖ ^ 2 := by positivity
    dsimp [q] at hEt ⊢
    dsimp [LyapunovEnergy] at hEt ⊢
    nlinarith
  let Cq : ℝ := max (2 * (LyapunovEnergy Φ a b ell (x 0) (y 0) - ell * mΦ)) 0
  have hqbdd : BoundedOnNonnegative q := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Real.sqrt Cq, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hCq : 0 ≤ Cq := le_max_right _ _
    have hsq : ‖q t‖ ^ 2 ≤ Cq := (hq_bound t ht).trans (le_max_left _ _)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCq]
    exact hsq
  have hybdd : BoundedOnNonnegative y := by
    rcases isBounded_iff_forall_norm_le.mp hqbdd with ⟨Cq', hqC⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(1 / b) * (Cq' + |a| * Cx), ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hbne : b ≠ 0 := ne_of_gt hb
    have hy_eq : y t = (1 / b) • (q t - a • x t) := by
      dsimp [q]
      field_simp [hbne]
      simp [hbne]
    rw [hy_eq, norm_smul]
    have hqnorm := hqC _ ⟨t, ht, rfl⟩
    have hax : ‖a • x t‖ ≤ |a| * Cx := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact hxnorm t ht
    have hqsub : ‖q t - a • x t‖ ≤ Cq' + |a| * Cx := by
      calc ‖q t - a • x t‖ ≤ ‖q t‖ + ‖a • x t‖ := norm_sub_le _ _
        _ ≤ Cq' + |a| * Cx := add_le_add hqnorm hax
    have hbinv : 0 ≤ (1 / b : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hbinv]
    exact mul_le_mul_of_nonneg_left hqsub hbinv
  have hvbdd : BoundedOnNonnegative v := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨β * max Cg 0 + Real.sqrt Cq, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hres : v t = -(β • g t + q t) := by
      dsimp [v, g, q]
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht
    rw [hres, norm_neg]
    calc
      ‖β • g t + q t‖ ≤ ‖β • g t‖ + ‖q t‖ := norm_add_le _ _
      _ = β * ‖g t‖ + ‖q t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      _ ≤ β * max Cg 0 + Real.sqrt Cq := by
        have hgn : ‖g t‖ ≤ max Cg 0 := (hgrad_bound t ht).trans (le_max_left _ _)
        have hqn : ‖q t‖ ≤ Real.sqrt Cq := by
          have hCq : 0 ≤ Cq := le_max_right _ _
          have hsq : ‖q t‖ ^ 2 ≤ Cq := (hq_bound t ht).trans (le_max_left _ _)
          apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
          rw [Real.sq_sqrt hCq]
          exact hsq
        exact add_le_add (mul_le_mul_of_nonneg_left hgn (le_of_lt hβ)) hqn
  rcases isBounded_iff_forall_norm_le.mp hvbdd with ⟨Cv, hCv⟩
  rcases isBounded_iff_forall_norm_le.mp hqbdd with ⟨Cq', hCq'⟩
  have hqcont : ContinuousOn q (Set.Ici (0 : ℝ)) := by
    exact (hxy.1.continuousOn.const_smul a).add (hxy.2.continuousOn.const_smul b)
  have hgcont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    exact (gdin_grad_continuous Φ hΦ).continuousOn.comp hxy.1.continuousOn
      (fun _ _ => Set.mem_univ _)
  have hv_eq (t : ℝ) (ht : 0 ≤ t) : v t = -(β • g t + q t) := by
    dsimp [v, g, q]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht
  have hvcont : ContinuousOn v (Set.Ici (0 : ℝ)) := by
    apply ContinuousOn.congr ((hgcont.const_smul β).add hqcont |>.neg)
    intro t ht
    simp [hv_eq t (Set.mem_Ici.mp ht)]
  let Cvn : NNReal := ⟨max Cv 0, le_max_right _ _⟩
  have hLipx : LipschitzOnWith Cvn x (Set.Ioi (0 : ℝ)) := by
    apply (convex_Ioi 0).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hxy.1.differentiableOn (by norm_num) t
        (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)).differentiableAt
        (Ici_mem_nhds ht)
    · intro t ht
      apply (NNReal.coe_le_coe).mp
      change ‖deriv x t‖ ≤ max Cv 0
      exact (hCv _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
  let Kq : NNReal := ⟨max (|a| * max Cv 0 + b * max Cq' 0) 0,
    le_max_right _ _⟩
  have hLipq : LipschitzOnWith Kq q (Set.Ioi (0 : ℝ)) := by
    apply (convex_Ioi 0).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      have hqC1 : ContDiffOn ℝ 1 q (Set.Ici (0 : ℝ)) := by
        exact (hxy.1.const_smul a).add
          ((hxy.2.of_le (by norm_num)).const_smul b)
      exact (hqC1.differentiableOn (by norm_num) t
        (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)).differentiableAt
          (Ici_mem_nhds ht)
    · intro t ht
      have hxAt : HasDerivAt x (v t) t := by
        have hd := hxy.1.differentiableOn (by norm_num) t
          (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)
        convert (hd.differentiableAt (Ici_mem_nhds ht)).hasDerivAt using 1
      have hyAt : HasDerivAt y (deriv y t) t := by
        have hd := hxy.2.differentiableOn (by norm_num) t
          (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)
        exact (hd.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
      have hyval : deriv y t = -q t := by
        have h : deriv y t = -(a • x t + b • y t) :=
          eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.2.1 t ht.le)
        simpa [q] using h
      have hqAt : HasDerivAt q (a • v t - b • q t) t := by
        have hraw := (hxAt.const_smul a).add (hyAt.const_smul b)
        convert hraw using 1
        rw [hyval]
        module
      rw [hqAt.deriv]
      have hvn : ‖v t‖ ≤ max Cv 0 :=
        (hCv _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
      have hqn : ‖q t‖ ≤ max Cq' 0 :=
        (hCq' _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
      apply (NNReal.coe_le_coe).mp
      change ‖a • v t - b • q t‖ ≤
        max (|a| * max Cv 0 + b * max Cq' 0) 0
      have hreal : ‖a • v t - b • q t‖ ≤
          max (|a| * max Cv 0 + b * max Cq' 0) 0 := by
        calc
          ‖a • v t - b • q t‖ ≤ ‖a • v t‖ + ‖b • q t‖ := norm_sub_le _ _
          _ = |a| * ‖v t‖ + |b| * ‖q t‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ |a| * max Cv 0 + b * max Cq' 0 := by
            have hbabs : |b| = b := abs_of_pos hb
            rw [hbabs]
            gcongr
          _ ≤ max (|a| * max Cv 0 + b * max Cq' 0) 0 := le_max_left _ _
      exact hreal
  have hLipg : LipschitzOnWith
      (K * ⟨max Cv 0, le_max_right _ _⟩) g (Set.Ioi (0 : ℝ)) := by
    have hc := hK.comp hLipx (fun t ht =>
      ⟨t, Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le, rfl⟩)
    simpa [Function.comp_def, g] using hc
  obtain ⟨Kβ, hLipv⟩ : ∃ Kβ : NNReal, LipschitzOnWith Kβ v (Set.Ioi (0 : ℝ)) := by
    let Lβ : H →L[ℝ] H := β • ContinuousLinearMap.id ℝ H
    have hβg : LipschitzOnWith (‖Lβ‖₊ * (K * Cvn))
        (fun t : ℝ => β • g t) (Set.Ioi (0 : ℝ)) := by
      simpa [Lβ, Function.comp_def] using
        Lβ.lipschitz.comp_lipschitzOnWith hLipg
    have hsum := hβg.add hLipq
    have hneg := hsum.neg
    refine ⟨‖Lβ‖₊ * (K * Cvn) + Kq, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have h := hneg.dist_le_mul s hs t ht
    simpa [v, hv_eq s hs.le, hv_eq t ht.le, dist_eq_norm] using h
  have hucg : UniformContinuousOn g (Set.Ici (0 : ℝ)) :=
    gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi g hLipg hgcont
  have hucv : UniformContinuousOn v (Set.Ici (0 : ℝ)) :=
    gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi v hLipv hvcont
  have hvL2 := gdin_x_derivative_memL2 Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
    x₀ y₀ x y hxy hsol
  have hgL2 := gdin_gradient_memL2 Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
    x₀ y₀ x y hxy hsol
  have hvSq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    exact hvL2.integrable_norm_pow (by norm_num)
  have hgSq : IntegrableOn (fun t => ‖g t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    exact hgL2.integrable_norm_pow (by norm_num)
  have hvzero : Tendsto v atTop (nhds 0) :=
    gdin_uniformContinuousOn_sq_integrable_tendsto_zero v hucv hvSq
  have hgzero : Tendsto g atTop (nhds 0) := by
    have hres := gdin_residual_limit Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
      x₀ y₀ x y hxy hsol
    have hbg : Tendsto (fun t => β • g t) atTop (nhds 0) := by
      have hsub := hres.sub hvzero
      simpa [v, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hinv := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (β⁻¹ : ℝ)) atTop (nhds β⁻¹)).smul hbg
    simpa [smul_smul, ne_of_gt hβ] using hinv
  refine ⟨hvbdd, hgbdd, ?_, ?_⟩
  · simpa [v] using hvzero
  · simpa [g] using hgzero

end Alvarez2002
