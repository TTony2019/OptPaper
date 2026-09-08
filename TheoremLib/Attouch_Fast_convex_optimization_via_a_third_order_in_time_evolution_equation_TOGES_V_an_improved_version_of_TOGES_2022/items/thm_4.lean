import Foundation.SetValued.Resolvent
import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_7
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_8
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.thm_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_5

open scoped Pointwise

open Filter

open scoped InnerProductSpace

open ERealFunction

open scoped InnerProductSpace

open ERealFunction

private theorem moreau_formula_toReal_local {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (hLam : 0 < lam)
    (hProper : ERealFunction.IsProper f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f)) (prox : H → H)
    (hres : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x)
    (hformula : ∀ x, f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
      moreauEnvelope f lam x) (x : H) :
    (moreauEnvelope f lam x).toReal = (f (prox x)).toReal +
      1 / (2 * lam) * ‖x - prox x‖ ^ 2 := by
  have hpx := hres x
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hpx
  dsimp [SetValuedOperator.identityAddScaled] at hpx
  rcases hpx with ⟨v, hv, hvx⟩
  have hpdom : prox x ∈ ERealFunction.dom f :=
    mem_subdifferential_dom_of_mem_subdifferential f hProper hv
  have hpfin : ((f (prox x)).toReal : EReal) = f (prox x) :=
    EReal.coe_toReal (ne_of_lt hpdom) (hProper.1 _)
  have htop : moreauEnvelope f lam x ≠ ⊤ := by
    rcases hProper.2 with ⟨z, hz⟩
    have hbound := moreau_proximal_objective_le f lam hLam hProper hConvex prox
      (by
        intro y
        exact hres y) x z
    apply ne_of_lt
    calc
      moreauEnvelope f lam x = f (prox x) +
          ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) := (hformula x).symm
      _ ≤ f z + ((1 / (2 * lam) * ‖x - z‖ ^ 2 : ℝ) : EReal) := hbound
      _ < ⊤ := EReal.add_lt_top (ne_of_lt hz) (EReal.coe_ne_top _)
  have hbot : moreauEnvelope f lam x ≠ ⊥ := by
    intro h
    rw [(hformula x).symm, EReal.add_eq_bot_iff] at h
    exact hProper.1 _ (h.resolve_right (EReal.coe_ne_bot _))
  have h := congrArg EReal.toReal (hformula x)
  rw [EReal.toReal_add, EReal.toReal_coe] at h
  · exact h.symm
  · exact ne_of_lt hpdom
  · exact hProper.1 _
  · exact EReal.coe_ne_top _
  · exact EReal.coe_ne_bot _

private theorem moreau_prox_gap_le_envelope_gap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (lam : ℝ) (prox : H → H) (m : ℝ)
    (hLam : 0 < lam)
    (hformula : ∀ x, (moreauEnvelope f lam x).toReal = (f (prox x)).toReal +
      1 / (2 * lam) * ‖x - prox x‖ ^ 2) (x : H) :
    (f (prox x)).toReal - m ≤ (moreauEnvelope f lam x).toReal - m := by
  rw [hformula x]
  have hcoef : 0 ≤ 1 / (2 * lam) := le_of_lt (by positivity)
  have hsq : 0 ≤ ‖x - prox x‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hcoef hsq]

private theorem littleO_of_nonneg_le {P A B : ℝ → ℝ}
    (hA : Asymptotics.IsLittleO atTop A B)
    (hP0 : ∀ᶠ t in atTop, 0 ≤ P t) (hA0 : ∀ᶠ t in atTop, 0 ≤ A t)
    (hPA : ∀ᶠ t in atTop, P t ≤ A t) : Asymptotics.IsLittleO atTop P B := by
  apply Asymptotics.isLittleO_iff.2
  intro eps heps
  filter_upwards [Asymptotics.isLittleO_iff.1 hA heps, hP0, hA0, hPA] with t hA' hP hA0' hle
  have hA'' : A t ≤ eps * ‖B t‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hA0'] using hA'
  simpa only [Real.norm_eq_abs, abs_of_nonneg hP] using hle.trans hA''

/-- The Moreau-regularized rate and weak convergence conclusions of Theorem 6.1. -/
private theorem togesVR_rate_and_weak_convergence_core {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (prox : H → H)
    (u firstDerivative secondDerivative thirdDerivative : ℝ → H) (envelopeGradient : H → H)
    (alpha lam t0 : ℝ)
    (hLam : 0 < lam) (hProper : ERealFunction.IsProper f) (hlsc : LowerSemicontinuous f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f))
    (hArgmin : ∃ x : H, f x = sInf (Set.range f))
    (hProx : IsProximalMapping f lam prox hProper hConvex)
    (hFConvex : ConvexOn ℝ Set.univ (fun x => (moreauEnvelope f lam x).toReal))
    (hFGradient : ∀ x, HasFDerivAt (fun x => (moreauEnvelope f lam x).toReal)
      (innerSL ℝ (envelopeGradient x)) x)
    (hFMin : ∃ z, IsMinOn (fun x => (moreauEnvelope f lam x).toReal) Set.univ z)
    (hFInf : sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)) =
      (sInf (Set.range f)).toReal) (ht0pos : 0 < t0)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (firstDerivative t) t)
    (hFirst : ∀ t, t0 ≤ t → HasDerivAt firstDerivative (secondDerivative t) t)
    (hSecond : ∀ t, t0 ≤ t → HasDerivAt secondDerivative (thirdDerivative t) t)
    (hDerivative : ∀ t, t0 ≤ t →
      deriv u t = firstDerivative t ∧ deriv (deriv u) t = secondDerivative t ∧
        deriv (deriv (deriv u)) t = thirdDerivative t)
    (hAuxiliaryStrict : 3 < alpha → ∃ vInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t : ℝ => (moreauEnvelope f lam (u t + (t / 4) • firstDerivative t)).toReal -
          sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal))) (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t + (t / 4) • firstDerivative t)) atTop
        (nhds (toWeakSpace ℝ H vInfinity)) ∧
      (moreauEnvelope f lam vInfinity).toReal =
        sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)))
    (hTrajectory : IsTOGESV alpha u (fun x => (moreauEnvelope f lam x).toReal) t0) :
    (3 ≤ alpha → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ t0,
      (moreauEnvelope f lam (u t + (t / 4) • firstDerivative t)).toReal -
      (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t + (t / 4) • firstDerivative t))).toReal -
      (sInf (Set.range f)).toReal ≤ C / t ^ 3
      ∧ (moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t))).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3) ∧
    (3 < alpha → ∃ uInfinity : H,
      Asymptotics.IsLittleO atTop (fun t : ℝ => (moreauEnvelope f lam (u t + (t / 4) •
      firstDerivative t)).toReal - (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop (fun t : ℝ => (f (prox (u t + (t / 4) •
      firstDerivative t))).toReal - (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop (fun t : ℝ => (moreauEnvelope f lam (u t)).toReal -
      (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop (fun t : ℝ => (f (prox (u t))).toReal -
      (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t)) atTop (nhds (toWeakSpace ℝ H uInfinity)) ∧
      f uInfinity = sInf (Set.range f)) := by
  have hres : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x := by
    intro x
    rw [show SetValuedOperator.resolvent ((lam) • (subdifferential f)) x =
      {prox x} from (hProx.2 x).2]
    simp
  have hformula : ∀ x, f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
      moreauEnvelope f lam x := fun x => (hProx.2 x).1
  have hrealformula : ∀ x, (moreauEnvelope f lam x).toReal = (f (prox x)).toReal +
      1 / (2 * lam) * ‖x - prox x‖ ^ 2 :=
    moreau_formula_toReal_local f lam hLam hProper hConvex prox hres hformula
  rcases hFMin with ⟨z, hz⟩
  rcases moreau_envelope_regularity_and_minimizers f lam hLam hProper hlsc hConvex
    (moreauEnvelope f lam) prox hres (fun x => (hformula x).symm) with ⟨_, _, hInfE, hMinSet, _⟩
  have hzGlobal : ∀ x : H, (moreauEnvelope f lam z).toReal ≤ (moreauEnvelope f lam x).toReal := by
    intro x
    simpa [IsMinOn, IsMinFilter] using hz (show x ∈ Set.univ by simp)
  have hsF : sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)) =
      (moreauEnvelope f lam z).toReal := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨(moreauEnvelope f lam z).toReal, fun y hy => by
          rcases hy with ⟨x, rfl⟩
          exact hzGlobal x⟩
      · exact ⟨z, rfl⟩
    · apply le_csInf
      · exact ⟨(moreauEnvelope f lam z).toReal, ⟨z, rfl⟩⟩
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hzGlobal x
  have hBase := togesV_rate_and_weak_convergence_core
    (fun x => (moreauEnvelope f lam x).toReal) u firstDerivative secondDerivative thirdDerivative
    envelopeGradient alpha t0
    hFConvex hFGradient ⟨z, hz⟩ ht0pos hu hFirst hSecond hDerivative hAuxiliaryStrict hTrajectory
  have hproxDom : ∀ x, prox x ∈ ERealFunction.dom f := by
    intro x
    have hpx := hres x
    rw [SetValuedOperator.mem_resolvent_smul_iff] at hpx
    dsimp [SetValuedOperator.identityAddScaled] at hpx
    rcases hpx with ⟨v, hv, hvx⟩
    exact mem_subdifferential_dom_of_mem_subdifferential f hProper hv
  have hgap : ∀ x, (f (prox x)).toReal - (sInf (Set.range f)).toReal ≤
      (moreauEnvelope f lam x).toReal - (sInf (Set.range f)).toReal := fun x =>
    moreau_prox_gap_le_envelope_gap f lam prox (sInf (Set.range f)).toReal hLam hrealformula x
  constructor
  · intro ha
    rcases hBase.1 ha with ⟨C, hC, hCbound⟩
    refine ⟨C, hC.le, ?_⟩
    intro t ht
    rcases hCbound t ht with ⟨hv, hu'⟩
    refine ⟨by simpa [hFInf] using hv, ?_, by simpa [hFInf] using hu', ?_⟩
    · exact (hgap _).trans (by simpa [hFInf] using hv)
    · exact (hgap _).trans (by simpa [hFInf] using hu')
  · intro ha
    rcases hBase.2 ha with ⟨uInfinity, hv, hu', huweak, humin⟩
    have hEnvNonneg : ∀ x, 0 ≤ (moreauEnvelope f lam x).toReal - (sInf (Set.range f)).toReal := by
      intro x
      rw [← hFInf, hsF]
      exact sub_nonneg.mpr (hzGlobal x)
    have hproxNonneg : ∀ x, 0 ≤ (f (prox x)).toReal - (sInf (Set.range f)).toReal := by
      intro x
      rcases hArgmin with ⟨w, hw⟩
      have hinfbot : sInf (Set.range f) ≠ ⊥ := by rw [← hw]; exact hProper.1 _
      exact sub_nonneg.mpr (EReal.toReal_le_toReal
        ((isGLB_sInf (Set.range f)).1 ⟨prox x, rfl⟩) hinfbot (ne_of_lt (hproxDom x)))
    have hv' : Asymptotics.IsLittleO atTop
        (fun t : ℝ => (moreauEnvelope f lam (u t + (t / 4) • firstDerivative t)).toReal -
          (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) := by simpa [hFInf] using hv
    have hu'' : Asymptotics.IsLittleO atTop
        (fun t : ℝ => (moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal)
          (fun t => 1 / t ^ 3) := by simpa [hFInf] using hu'
    refine ⟨uInfinity, hv', ?_, hu'', ?_, huweak, ?_⟩
    · apply littleO_of_nonneg_le hv'
      · exact Filter.Eventually.of_forall (fun t => hproxNonneg _)
      · exact Filter.Eventually.of_forall (fun t => hEnvNonneg _)
      · exact Filter.Eventually.of_forall (fun t => hgap _)
    · apply littleO_of_nonneg_le hu''
      · exact Filter.Eventually.of_forall (fun t => hproxNonneg _)
      · exact Filter.Eventually.of_forall (fun t => hEnvNonneg _)
      · exact Filter.Eventually.of_forall (fun t => hgap _)
    · have henv : moreauEnvelope f lam uInfinity = sInf (Set.range (moreauEnvelope f lam)) := by
        rcases hProper.2 with ⟨p, hp⟩
        have henvtop : moreauEnvelope f lam uInfinity ≠ ⊤ := by
          have hbound := moreau_proximal_objective_le f lam hLam hProper hConvex prox hres
            uInfinity p
          apply ne_of_lt
          calc
            moreauEnvelope f lam uInfinity = f (prox uInfinity) +
                ((1 / (2 * lam) * ‖uInfinity - prox uInfinity‖ ^ 2 : ℝ) : EReal) :=
              (hformula uInfinity).symm
            _ ≤ f p + ((1 / (2 * lam) * ‖uInfinity - p‖ ^ 2 : ℝ) : EReal) := hbound
            _ < ⊤ := EReal.add_lt_top (ne_of_lt hp) (EReal.coe_ne_top _)
        have henvbot : moreauEnvelope f lam uInfinity ≠ ⊥ := by
          intro h
          rw [(hformula uInfinity).symm, EReal.add_eq_bot_iff] at h
          exact hProper.1 _ (h.resolve_right (EReal.coe_ne_bot _))
        rcases hArgmin with ⟨w, hw⟩
        have hinfbot : sInf (Set.range f) ≠ ⊥ := by rw [← hw]; exact hProper.1 _
        have hinftop : sInf (Set.range f) ≠ ⊤ :=
          ne_of_lt ((isGLB_sInf (Set.range f)).1 ⟨p, rfl⟩ |>.trans_lt hp)
        have hreal : (moreauEnvelope f lam uInfinity).toReal =
            (sInf (Set.range f)).toReal := by
          calc
            (moreauEnvelope f lam uInfinity).toReal =
                sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)) := humin
            _ = (sInf (Set.range f)).toReal := hFInf
        have hcoe := congrArg (fun r : ℝ => (r : EReal)) hreal
        change ((moreauEnvelope f lam uInfinity).toReal : EReal) =
          ((sInf (Set.range f)).toReal : EReal) at hcoe
        rw [EReal.coe_toReal henvtop henvbot, EReal.coe_toReal hinftop hinfbot] at hcoe
        exact hcoe.trans hInfE.symm
      have : uInfinity ∈ {x | moreauEnvelope f lam x =
      sInf (Set.range (moreauEnvelope f lam))} := henv
      change uInfinity ∈ {x | f x = sInf (Set.range f)}
      rw [← hMinSet]
      exact this

/--
Theorem 6.1:
Moreau-regularized TOGES-V estimates with direct trajectory derivatives.
-/
theorem togesVR_rate_and_weak_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (prox : H → H)
    (u : ℝ → H) (alpha lam t0 : ℝ)
    (hLam : 0 < lam) (hProper : ERealFunction.IsProper f) (hlsc : LowerSemicontinuous f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f))
    (hArgmin : ∃ x : H, f x = sInf (Set.range f))
    (hProx : IsProximalMapping f lam prox hProper hConvex) --recall
    (hFConvex : ConvexOn ℝ Set.univ (fun x => (moreauEnvelope f lam x).toReal)) --merge
    (hFMin : ∃ z, IsMinOn (fun x => (moreauEnvelope f lam x).toReal) Set.univ z) --merge
    (hFInf : sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)) = --merge
      (sInf (Set.range f)).toReal) (ht0pos : 0 < t0)
    (hUContDiff : ContDiff ℝ 3 u)
    (hAuxiliaryStrict : 3 < alpha → ∃ vInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t => (moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)))
        (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t + (t / 4) • deriv u t)) atTop
        (nhds (toWeakSpace ℝ H vInfinity)) ∧
      (moreauEnvelope f lam vInfinity).toReal =
        sInf (Set.range (fun x => (moreauEnvelope f lam x).toReal)))
    (hTrajectory : IsTOGESV alpha u (fun x => (moreauEnvelope f lam x).toReal) t0) :
    (3 ≤ alpha → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ t0,
      (moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t + (t / 4) • deriv u t))).toReal -
          (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t))).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3) ∧
    (3 < alpha → ∃ uInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t => (moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (f (prox (u t + (t / 4) • deriv u t))).toReal -
          (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal)
          (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (f (prox (u t))).toReal - (sInf (Set.range f)).toReal)
          (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t)) atTop
      (nhds (toWeakSpace ℝ H uInfinity)) ∧
      f uInfinity = sInf (Set.range f)) := by
  have hres : ∀ x, prox x ∈ SetValuedOperator.resolvent
      (lam • subdifferential f) x := by
    intro x
    rw [show SetValuedOperator.resolvent ((lam) • (subdifferential f)) x =
      {prox x} from (hProx.2 x).2]
    simp
  have hformula : ∀ x, f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) =
      moreauEnvelope f lam x := fun x => (hProx.2 x).1
  have hFContDiff : ContDiff ℝ 1 (fun x => (moreauEnvelope f lam x).toReal) :=
    (moreau_envelope_regularity_and_minimizers f lam hLam hProper hlsc hConvex
      (moreauEnvelope f lam) prox hres (fun x => (hformula x).symm)).2.1
  have hFGradient : ∀ x, HasFDerivAt (fun x => (moreauEnvelope f lam x).toReal)
      (innerSL ℝ (gradient (fun x => (moreauEnvelope f lam x).toReal) x)) x := by
    intro x
    simpa [innerSL_apply_apply] using
      ((hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have huDiff : Differentiable ℝ u := hUContDiff.differentiable (by norm_num)
  have hFirstDiff : Differentiable ℝ (deriv u) :=
    (hUContDiff.of_le (by norm_num)).differentiable_deriv_two
  have hSecondDiff : Differentiable ℝ (deriv (deriv u)) := by
    exact hUContDiff.deriv'.differentiable_deriv_two
  have hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      exact (huDiff t).hasDerivAt
    · intro t _
      exact (hFirstDiff t).hasDerivAt
    · intro t _
      exact (hSecondDiff t).hasDerivAt
  exact togesVR_rate_and_weak_convergence_core f prox u (deriv u) (deriv (deriv u))
    (deriv (deriv (deriv u)))
    (gradient (fun x => (moreauEnvelope f lam x).toReal)) alpha lam t0 hLam hProper hlsc
    hConvex hArgmin hProx hFConvex hFGradient hFMin hFInf ht0pos
    hRegularity.1 hRegularity.2.1 hRegularity.2.2
    (fun t ht => ⟨rfl, rfl, rfl⟩) hAuxiliaryStrict hTrajectory
