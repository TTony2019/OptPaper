import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_3
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_4
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_lem_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.lem_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.thm_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_5
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.lem_2

set_option maxHeartbeats 5000000

namespace Alvarez2000

open Filter
open MeasureTheory
open scoped InnerProductSpace Topology

/-- Removing the coercivity constant from the damping operator leaves a positive
quadratic form.  This is the operator positivity used in the comparison estimate. -/
theorem operator_damping_remainder_nonnegative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Gamma : H →L[ℝ] H} {gamma : ℝ}
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ) (x : H) :
    0 ≤ ⟪(Gamma - gamma • ContinuousLinearMap.id ℝ H) x, x⟫_ℝ := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left,
    real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]
  linarith [hcoercive x]

/-- The trajectory of an operator-damped system is differentiable at every
strictly positive time. -/
private theorem operatorSystem_differentiableAt_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ sys.u t := by
  exact (sys.contDiff.contDiffAt (Ici_mem_nhds ht)).differentiableAt (by norm_num)

/-- At positive times the ordinary derivative of the trajectory agrees with
the Fréchet derivative used in the system equation. -/
private theorem operatorSystem_deriv_eq_fderiv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) : deriv sys.u t = fderiv ℝ sys.u t 1 := by
  exact (operatorSystem_differentiableAt_pos sys ht).hasDerivAt.deriv

/-- Chain rule for the potential along an operator-damped trajectory. -/
private theorem operatorSystem_potential_deriv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun s => Phi (sys.u s)) t =
      ⟪gradPhi (sys.u t), fderiv ℝ sys.u t 1⟫_ℝ := by
  have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
    (operatorSystem_differentiableAt_pos sys ht).hasDerivAt
  have hPhi : HasGradientAt Phi (gradPhi (sys.u t)) (sys.u t) := sys.is_gradient _
  simpa using (hPhi.hasFDerivAt.comp_hasDerivAt t hu).deriv

/-- The velocity has the derivative appearing in the operator-damped equation
at each strictly positive time. -/
private theorem operatorSystem_velocity_hasDerivAt_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => fderiv ℝ sys.u s 1)
      (fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1) t := by
  have hu := sys.contDiff.contDiffAt (Ici_mem_nhds ht)
  have hv : ContDiffAt ℝ 1 (fun s => fderiv ℝ sys.u s 1) t := by
    exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  exact (hv.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasDerivAt

/-- The operator-damped energy has derivative given by the damping quadratic
form away from the endpoint. -/
private theorem operatorSystem_energy_deriv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun s => (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 + Phi (sys.u s)) t =
      -⟪Gamma (fderiv ℝ sys.u t 1), fderiv ℝ sys.u t 1⟫_ℝ := by
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : H := fderiv ℝ v t 1
  have hv : HasDerivAt v a t := by
    simpa only [v, a] using operatorSystem_velocity_hasDerivAt_pos sys ht
  have hk : HasDerivAt (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2)
      ((1 / 2 : ℝ) * (2 * ⟪v t, a⟫_ℝ)) t := by
    simpa using (hasDerivAt_const t (1 / 2 : ℝ)).mul (hv.norm_sq)
  have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
    (operatorSystem_differentiableAt_pos sys ht).hasDerivAt
  have hp : HasDerivAt (fun s => Phi (sys.u s))
      ⟪gradPhi (sys.u t), fderiv ℝ sys.u t 1⟫_ℝ t := by
    simpa using ((sys.is_gradient _).hasFDerivAt.comp_hasDerivAt t hu)
  have hderiv : HasDerivAt (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2 + Phi (sys.u s))
      ((1 / 2 : ℝ) * (2 * ⟪v t, a⟫_ℝ) +
        ⟪gradPhi (sys.u t), fderiv ℝ sys.u t 1⟫_ℝ) t := by
    simpa only [Pi.add_apply] using hk.add hp
  have heq := sys.equation t (le_of_lt ht)
  have hinner := congrArg (fun z : H => ⟪z, fderiv ℝ sys.u t 1⟫_ℝ) heq
  change deriv (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2 + Phi (sys.u s)) t = _
  rw [hderiv.deriv]
  simp only [v, a] at hinner ⊢
  rw [inner_add_left, inner_add_left] at hinner
  rw [real_inner_comm] at hinner
  norm_num at hinner ⊢
  linarith

/-- On a closed interval contained in the positive-time interior, energy
dissipation controls the accumulated squared velocity. -/
private theorem operator_energy_integral_le_on_Icc_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {gamma m : ℝ}
    (hPhiDiff : ContDiff ℝ 1 Phi) (hm : ∀ y : H, m ≤ Phi y) (hgamma : 0 < gamma)
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) {eps T : ℝ}
    (heps : 0 < eps) (hET : eps ≤ T) :
    gamma * (∫ t in eps..T, ‖fderiv ℝ sys.u t 1‖ ^ 2) ≤
      ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u eps 1‖ ^ 2 + Phi (sys.u eps)) - m := by
  rcases hET.eq_or_lt with rfl | hET
  · have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u eps 1‖ ^ 2 := by positivity
    simp only [intervalIntegral.integral_same, mul_zero]
    linarith [hm (sys.u eps)]
  let E : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  have hE : ContDiffOn ℝ 1 E (Set.Icc eps T) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le heps ht.1
    have hu := sys.contDiff.contDiffAt (Ici_mem_nhds htpos)
    have hv : ContDiffAt ℝ 1 (fun s => fderiv ℝ sys.u s 1) t := by
      exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
        contDiffAt_const
    have hk : ContDiffAt ℝ 1 (fun s =>
        (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2) t := by
      exact contDiffAt_const.mul (hv.norm_sq ℝ)
    have hp : ContDiffAt ℝ 1 (fun s => Phi (sys.u s)) t := by
      exact hPhiDiff.contDiffAt.comp t (hu.of_le (by norm_num))
    have hsum : ContDiffAt ℝ 1 E t := by
      simpa only [E] using hk.add hp
    exact hsum.contDiffWithinAt
  have hderivInt : IntervalIntegrable (deriv E) volume eps T := by
    have hcont :=
      (hE.derivWithin (m := 0) (uniqueDiffOn_Icc hET) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hET.le).congr_ae
    simp only [hET.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hsqInt : IntervalIntegrable (fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2)
      volume eps T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hET.le
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le heps ht.1
    have hu := sys.contDiff.contDiffAt (Ici_mem_nhds htpos)
    have hv : ContDiffAt ℝ 1 (fun s => fderiv ℝ sys.u s 1) t := by
      exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
        contDiffAt_const
    exact (hv.norm_sq ℝ).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo eps T,
      deriv E t ≤ -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    have htpos : 0 < t := lt_trans heps ht.1
    rw [show deriv E t = -⟪Gamma (fderiv ℝ sys.u t 1), fderiv ℝ sys.u t 1⟫_ℝ by
      exact operatorSystem_energy_deriv_pos sys htpos]
    linarith [hcoercive (fderiv ℝ sys.u t 1)]
  have hFTC : E T - E eps = ∫ t in eps..T, deriv E t := by
    simpa only [E] using
      (intervalIntegral.integral_deriv_of_contDiffOn_Icc hE hET.le).symm
  have hmono : (∫ t in eps..T, deriv E t) ≤
      ∫ t in eps..T, -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2 :=
    intervalIntegral.integral_mono_on_of_le_Ioo hET.le hderivInt
      (hsqInt.const_mul (-gamma)) hderiv
  have hterminal : m ≤ E T := by
    dsimp [E]
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u T 1‖ ^ 2 := by positivity
    linarith [hm (sys.u T)]
  rw [← hFTC] at hmono
  have hfactor : (∫ t in eps..T, -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2) =
      -gamma * (∫ t in eps..T, ‖fderiv ℝ sys.u t 1‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hfactor] at hmono
  dsimp [E] at hmono hterminal ⊢
  linarith

/-- On positive time intervals, coercive damping makes the mechanical energy
nonincreasing. -/
private theorem operator_energy_antitone_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {gamma : ℝ}
    (hPhi : HasPotentialAssumption Phi) (hgamma : 0 < gamma)
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u b 1‖ ^ 2 + Phi (sys.u b) ≤
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u a 1‖ ^ 2 + Phi (sys.u a) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  let E : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  have hE : ContDiffOn ℝ 1 E (Set.Icc a b) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hu := sys.contDiff.contDiffAt (Ici_mem_nhds htpos)
    have hv : ContDiffAt ℝ 1 (fun s => fderiv ℝ sys.u s 1) t := by
      exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
        contDiffAt_const
    have hk : ContDiffAt ℝ 1 (fun s =>
        (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2) t := by
      exact contDiffAt_const.mul (hv.norm_sq ℝ)
    have hp : ContDiffAt ℝ 1 (fun s => Phi (sys.u s)) t := by
      exact hPhi.contDiff.contDiffAt.comp t (hu.of_le (by norm_num))
    exact (show ContDiffAt ℝ 1 E t from by simpa [E] using hk.add hp).contDiffWithinAt
  have hderivInt : IntervalIntegrable (deriv E) volume a b := by
    have hcont :=
      (hE.derivWithin (m := 0) (uniqueDiffOn_Icc hab) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hab.le).congr_ae
    simp only [Set.uIoc_of_le hab.le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hderiv : ∀ t ∈ Set.Ioo a b, deriv E t ≤ 0 := by
    intro t ht
    rw [show deriv E t = -⟪Gamma (fderiv ℝ sys.u t 1), fderiv ℝ sys.u t 1⟫_ℝ by
      exact operatorSystem_energy_deriv_pos sys (lt_trans ha ht.1)]
    have := hcoercive (fderiv ℝ sys.u t 1)
    nlinarith [sq_nonneg ‖fderiv ℝ sys.u t 1‖]
  have hFTC : E b - E a = ∫ t in a..b, deriv E t := by
    exact (intervalIntegral.integral_deriv_of_contDiffOn_Icc hE hab.le).symm
  have hnonpos : (∫ t in a..b, deriv E t) ≤ ∫ _t in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab.le hderivInt
      intervalIntegrable_const
    exact hderiv
  simp only [intervalIntegral.integral_zero] at hnonpos
  rw [← hFTC] at hnonpos
  simpa [E] using sub_nonpos.mp hnonpos

/-- A positive-time antitone energy bounded below by the potential has a finite
limit at infinity. -/
private theorem operator_energy_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {gamma : ℝ}
    (hPhi : HasPotentialAssumption Phi) (hgamma : 0 < gamma)
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    ∃ L : ℝ, Tendsto (fun t =>
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) atTop (nhds L) := by
  let E : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let Epos : ℝ → ℝ := fun t => E (max t 1)
  have hanti : Antitone Epos := by
    intro s t hst
    apply operator_energy_antitone_pos hPhi hgamma hcoercive sys
    · dsimp [Epos]
      linarith [le_max_right s 1]
    · dsimp [Epos]
      exact max_le_max_right 1 hst
  obtain ⟨m, hm⟩ := potential_lower_bound_le_sInf hPhi
  have hbelow : BddBelow (Set.range Epos) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp [Epos, E]
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (max t 1) 1‖ ^ 2 := by positivity
    have hpot := potential_sInf_le hPhi (sys.u (max t 1))
    linarith
  have hlim : Tendsto Epos atTop (nhds (⨅ t : ℝ, Epos t)) :=
    tendsto_atTop_ciInf hanti hbelow
  refine ⟨⨅ t : ℝ, Epos t, ?_⟩
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp [Epos, E, max_eq_left ht]

/-- Away from the endpoint, the velocity is continuously differentiable.  This
is the regularity needed to treat its squared norm as an ordinary integrand on
compact positive-time intervals. -/
theorem operatorSystem_velocity_contDiffOn_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    ContDiffOn ℝ 1 (fun t => fderiv ℝ sys.u t 1) (Set.Ioi 0) := by
  have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
    sys.contDiff.mono Set.Ioi_subset_Ici_self
  exact (hu.fderiv_of_isOpen isOpen_Ioi
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffOn_const

/-- The squared velocity is integrable on every compact interval lying in the
positive-time interior of an operator-damped trajectory. -/
theorem operator_velocity_sq_intervalIntegrable_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {eps T : ℝ}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (heps : 0 < eps)
    (hET : eps ≤ T) :
    IntervalIntegrable (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) volume eps T := by
  apply ContinuousOn.intervalIntegrable_of_Icc hET
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le heps ht.1
  have hv := (operatorSystem_velocity_contDiffOn_pos sys).contDiffAt (Ioi_mem_nhds htpos)
  exact (hv.norm_sq ℝ).continuousAt.continuousWithinAt

/-- Set-integrability form of the compact positive-time velocity estimate. -/
theorem operator_velocity_sq_integrableOn_Icc_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {eps T : ℝ}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (heps : 0 < eps)
    (hET : eps ≤ T) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Icc eps T) := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hET).mp
    (operator_velocity_sq_intervalIntegrable_pos sys heps hET)

/-- Energy dissipation makes the squared velocity integrable on the positive
tail.  The improper-integral lemma packages the increasing compact cover. -/
private theorem operator_velocity_sq_integrableOn_Ioi_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {gamma m : ℝ}
    (hPhiDiff : ContDiff ℝ 1 Phi) (hm : ∀ y : H, m ≤ Phi y) (hgamma : 0 < gamma)
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 1) := by
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
  let C : ℝ := (((1 / 2 : ℝ) * ‖fderiv ℝ sys.u 1 1‖ ^ 2 + Phi (sys.u 1)) - m) / gamma
  have hbound : ∀ n : ℕ, (∫ t in 1..(n + 1 : ℝ), ‖q t‖) ≤ C := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have henergy := operator_energy_integral_le_on_Icc_pos hPhiDiff hm hgamma hcoercive sys
      (eps := 1) (T := (n + 1 : ℝ)) (by norm_num) hn
    have hnonneg : ∀ t : ℝ, 0 ≤ q t := fun t => sq_nonneg _
    rw [show (fun t => ‖q t‖) = q by funext t; exact Real.norm_of_nonneg (hnonneg t)]
    dsimp [q, C]
    apply (le_div_iff₀ hgamma).2
    simpa [mul_comm] using henergy
  have hlocal : ∀ n : ℕ, IntegrableOn q (Set.Ioc 1 (n + 1 : ℝ)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (operator_velocity_sq_integrableOn_Icc_pos sys (by norm_num)
      (by linarith)).mono_set
      Set.Ioc_subset_Icc_self
  have hTendsto : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := integrableOn_Ioi_of_intervalIntegral_norm_bounded C 1 hlocal hTendsto
    (Filter.Eventually.of_forall hbound)
  simpa only [q] using h

/-- The one-sided `C²` hypothesis controls the initial finite interval.  At
strictly positive times the ordinary derivative agrees with the derivative
within the half-line, whose continuity is supplied by `ContDiffOn`. -/
private theorem operator_velocity_sq_integrableOn_Ioc_zero_one {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioc 0 1) := by
  let w : ℝ → H := fun t => fderivWithin ℝ sys.u (Set.Ici 0) t 1
  have hw : ContinuousOn w (Set.Icc 0 1) := by
    have hcont : ContinuousOn (fderivWithin ℝ sys.u (Set.Ici 0)) (Set.Ici 0) :=
      sys.contDiff.continuousOn_fderivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact (hcont.mono Set.Icc_subset_Ici_self).clm_apply continuousOn_const
  have hsqcont : ContinuousOn (fun t => ‖w t‖ ^ 2) (Set.Icc 0 1) := by
    intro t ht
    exact (continuous_norm.continuousAt.comp_continuousWithinAt (hw t ht)).pow 2
  have hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Icc 0 1) :=
    hsqcont.integrableOn_Icc
  have hsq' : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Ioc 0 1) :=
    hsq.mono_set Set.Ioc_subset_Icc_self
  apply hsq'.congr_fun
  · intro t ht
    have hdiff : DifferentiableAt ℝ sys.u t :=
      operatorSystem_differentiableAt_pos sys ht.1
    have hfd : fderivWithin ℝ sys.u (Set.Ici 0) t = fderiv ℝ sys.u t :=
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t (le_of_lt ht.1)) hdiff
    simp only [w]
    rw [hfd]
  · exact measurableSet_Ioc

/-- Combining the one-sided initial interval with the dissipative tail. -/
private theorem operator_velocity_sq_integrableOn_Ioi_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} {gamma m : ℝ}
    (hPhiDiff : ContDiff ℝ 1 Phi) (hm : ∀ y : H, m ≤ Phi y) (hgamma : 0 < gamma)
    (hcoercive : ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (operator_velocity_sq_integrableOn_Ioc_zero_one sys).union
    (operator_velocity_sq_integrableOn_Ioi_one hPhiDiff hm hgamma hcoercive sys)

/-- The quadratic distance identity underlying the operator-damped comparison
estimate.  Keeping the coercive remainder explicit is useful in the subsequent
convolution argument. -/
private theorem operator_distance_identity_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (gamma : ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (x : H) {t : ℝ} (ht : 0 < t) :
    let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
    let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2
    let rho : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ⟪A (sys.u s - x), sys.u s - x⟫_ℝ
    deriv (deriv phi) t + gamma * deriv phi t + deriv rho t =
      ⟪gradPhi (sys.u t), x - sys.u t⟫_ℝ + ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
  dsimp
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : H := fderiv ℝ v t 1
  let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2
  let rho : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ⟪A (sys.u s - x), sys.u s - x⟫_ℝ
  have hu : HasDerivAt sys.u (v t) t := by
    simpa only [v] using (operatorSystem_differentiableAt_pos sys ht).hasDerivAt
  have hv : HasDerivAt v a t := by
    simpa only [v, a] using operatorSystem_velocity_hasDerivAt_pos sys ht
  have hphi : HasDerivAt phi ⟪v t, sys.u t - x⟫_ℝ t := by
    have hsub : HasDerivAt (fun s => sys.u s - x) (v t) t := by
      simpa using hu.sub_const x
    have hsq := (hasDerivAt_const t (1 / 2 : ℝ)).mul hsub.norm_sq
    convert hsq using 1 <;> simp [phi, real_inner_comm] <;> ring
  have hfirst : ∀ᶠ s in nhds t, deriv phi s = ⟪v s, sys.u s - x⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hus : HasDerivAt sys.u (v s) s := by
      simpa only [v] using (operatorSystem_differentiableAt_pos sys hs).hasDerivAt
    have hsubs : HasDerivAt (fun r => sys.u r - x) (v s) s := by
      simpa using hus.sub_const x
    have hsqs := (hasDerivAt_const s (1 / 2 : ℝ)).mul hsubs.norm_sq
    have : HasDerivAt phi ⟪v s, sys.u s - x⟫_ℝ s := by
      convert hsqs using 1 <;> simp [phi, real_inner_comm] <;> ring
    exact this.deriv
  have hsecond : deriv (deriv phi) t =
      ⟪a, sys.u t - x⟫_ℝ + ‖v t‖ ^ 2 := by
    rw [show deriv (deriv phi) t = deriv (fun s => ⟪v s, sys.u s - x⟫_ℝ) t by
      exact Filter.EventuallyEq.deriv_eq hfirst]
    simpa only [real_inner_self_eq_norm_sq, add_comm] using (hv.inner ℝ (hu.sub_const x)).deriv
  have hAself : IsSelfAdjoint A := by
    dsimp [A]
    apply sys.self_adjoint.sub
    rw [IsSelfAdjoint]
    rw [star_smul]
    simp only [starRingEnd_apply, star_trivial]
    change gamma • ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ H) =
      gamma • ContinuousLinearMap.id ℝ H
    rw [ContinuousLinearMap.adjoint_id]
  have hrho : HasDerivAt rho ⟪A (v t), sys.u t - x⟫_ℝ t := by
    have hsub : HasDerivAt (fun s => sys.u s - x) (v t) t := by
      simpa using hu.sub_const x
    have hAderiv : HasDerivAt (fun s => A (sys.u s - x)) (A (v t)) t := by
      simpa only [Function.comp_apply] using (A.hasFDerivAt.comp_hasDerivAt t hsub)
    have hquad := hAderiv.inner ℝ hsub
    have hsymm : ⟪A (sys.u t - x), v t⟫_ℝ = ⟪A (v t), sys.u t - x⟫_ℝ := by
      calc
        _ = ⟪sys.u t - x, ContinuousLinearMap.adjoint A (v t)⟫_ℝ :=
          (ContinuousLinearMap.adjoint_inner_right A (sys.u t - x) (v t)).symm
        _ = ⟪sys.u t - x, A (v t)⟫_ℝ := by
          rw [show ContinuousLinearMap.adjoint A = A by simpa [IsSelfAdjoint] using hAself]
        _ = _ := real_inner_comm _ _
    have hscaled := (hasDerivAt_const t (1 / 2 : ℝ)).mul hquad
    rw [hsymm] at hscaled
    convert hscaled using 1 <;> dsimp [rho] <;> ring
  have heq := sys.equation t (le_of_lt ht)
  have hinnerEq := congrArg (fun z : H => ⟪z, sys.u t - x⟫_ℝ) heq
  have hGamma : gamma * ⟪v t, sys.u t - x⟫_ℝ +
      ⟪A (v t), sys.u t - x⟫_ℝ = ⟪Gamma (v t), sys.u t - x⟫_ℝ := by
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left]
    ring
  change deriv (deriv phi) t + gamma * deriv phi t + deriv rho t = _
  rw [hsecond, hphi.deriv, hrho.deriv]
  simp only [v, a] at hinnerEq ⊢
  rw [inner_add_left, inner_add_left] at hinnerEq
  have hneg : ⟪gradPhi (sys.u t), x - sys.u t⟫_ℝ =
      -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    rw [show x - sys.u t = -(sys.u t - x) by abel, inner_neg_right]
  have hEq : ⟪a, sys.u t - x⟫_ℝ + ⟪Gamma (v t), sys.u t - x⟫_ℝ =
      -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    simp only [inner_zero_left] at hinnerEq
    simpa only [v, a] using (show
      ⟪(fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t) 1, sys.u t - x⟫_ℝ +
          ⟪Gamma (fderiv ℝ sys.u t 1), sys.u t - x⟫_ℝ =
        -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ by linarith [hinnerEq])
  calc
    _ = ⟪a, sys.u t - x⟫_ℝ + ‖v t‖ ^ 2 +
        (gamma * ⟪v t, sys.u t - x⟫_ℝ + ⟪A (v t), sys.u t - x⟫_ℝ) := by ring
    _ = ⟪a, sys.u t - x⟫_ℝ + ‖v t‖ ^ 2 + ⟪Gamma (v t), sys.u t - x⟫_ℝ := by rw [hGamma]
    _ = (⟪a, sys.u t - x⟫_ℝ + ⟪Gamma (v t), sys.u t - x⟫_ℝ) + ‖v t‖ ^ 2 := by ring
    _ = -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ + ‖v t‖ ^ 2 := by rw [hEq]
    _ = _ := by simpa only [v] using congrArg (fun r : ℝ => r + ‖v t‖ ^ 2) hneg.symm

/-- Convexity turns the operator quadratic identity into the scalar differential
inequality used by the exponentially weighted comparison argument. -/
private theorem operator_distance_damped_ineq_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi) (gamma : ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (x : H) {t : ℝ} (ht : 0 < t) :
    let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
    let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2
    let rho : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ⟪A (sys.u s - x), sys.u s - x⟫_ℝ
    deriv (deriv phi) t + gamma * deriv phi t + deriv rho t ≤
      Phi x - Phi (sys.u t) + ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
  dsimp
  have hident := operator_distance_identity_pos gamma sys x ht
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hident
  have hsupp := scalar_convex_gradient_support hPhi.convex sys.is_gradient (sys.u t) x
  linarith

/-- Translating a scalar function one unit to the right commutes with its
ordinary derivative wherever the translated point is an interior point.  This
small endpoint-safe lemma is used for the comparison functions below. -/
private theorem deriv_comp_add_one {f : ℝ → ℝ} {s : ℝ}
    (hf : DifferentiableAt ℝ f (s + 1)) :
    deriv (fun r => f (r + 1)) s = deriv f (s + 1) := by
  have hadd : HasDerivAt (fun r : ℝ => r + 1) 1 s := by
    simpa using (hasDerivAt_id s).add_const 1
  simpa using (hf.hasDerivAt.comp s hadd).deriv

/-- A translated `C²` scalar function has the expected second derivative.
The proof rewrites the outer derivative only through an eventual equality;
this is essential because derivative equality is a local, rather than global,
fact. -/
private theorem deriv_deriv_comp_add_one {f : ℝ → ℝ} {s : ℝ}
    (hfirst : ∀ᶠ r in nhds s, deriv (fun q => f (q + 1)) r = deriv f (r + 1))
    (hderiv : DifferentiableAt ℝ (deriv f) (s + 1)) :
    deriv (deriv (fun r => f (r + 1))) s = deriv (deriv f) (s + 1) := by
  rw [Filter.EventuallyEq.deriv_eq hfirst]
  exact deriv_comp_add_one hderiv

/-- The operator distance inequality, shifted away from the one-sided endpoint.
This is the form in which the exponential comparison argument can be applied
on the ordinary half-line `Ici 0`. -/
private theorem operator_shifted_distance_damped_ineq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi) (gamma : ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (x : H) {s : ℝ} (hs : 0 ≤ s) :
    let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
    let phi0 : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2
    let rho0 : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ⟪A (sys.u r - x), sys.u r - x⟫_ℝ
    let phi : ℝ → ℝ := fun r => phi0 (r + 1)
    let rho : ℝ → ℝ := fun r => rho0 (r + 1)
    deriv (deriv phi) s + gamma * deriv phi s + deriv rho s ≤
      Phi x - Phi (sys.u (s + 1)) + ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
  dsimp
  let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
  let phi0 : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2
  let rho0 : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ⟪A (sys.u r - x), sys.u r - x⟫_ℝ
  have hspos : 0 < s + 1 := by linarith
  have hd := operator_distance_damped_ineq_pos hPhi gamma sys x hspos
  have hphi : deriv (fun r => phi0 (r + 1)) s = deriv phi0 (s + 1) := by
    apply deriv_comp_add_one
    have hu := sys.contDiff.contDiffAt (Ici_mem_nhds hspos)
    exact (contDiffAt_const.mul ((hu.sub contDiffAt_const).norm_sq ℝ)).differentiableAt
      (by norm_num)
  have hphi2 : deriv (deriv (fun r => phi0 (r + 1))) s = deriv (deriv phi0) (s + 1) := by
    apply deriv_deriv_comp_add_one
    · filter_upwards [Ioi_mem_nhds (show -1 < s by linarith)] with r hr
      change -1 < r at hr
      apply deriv_comp_add_one
      have hrpos : 0 < r + 1 := by linarith
      have hu := sys.contDiff.contDiffAt (Ici_mem_nhds hrpos)
      exact (contDiffAt_const.mul ((hu.sub contDiffAt_const).norm_sq ℝ)).differentiableAt
        (by norm_num)
    · have hu := sys.contDiff.contDiffAt (Ici_mem_nhds hspos)
      exact (contDiffAt_const.mul ((hu.sub contDiffAt_const).norm_sq ℝ)).derivWithin
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.differentiableAt (by norm_num)
  have hrho : deriv (fun r => rho0 (r + 1)) s = deriv rho0 (s + 1) := by
    apply deriv_comp_add_one
    have hu := sys.contDiff.contDiffAt (Ici_mem_nhds hspos)
    have hw : ContDiffAt ℝ 2 (fun r => sys.u r - x) (s + 1) := hu.sub contDiffAt_const
    have hAw : ContDiffAt ℝ 2 (fun r => A (sys.u r - x)) (s + 1) :=
      contDiffAt_const.clm_apply hw
    exact (contDiffAt_const.mul (hAw.inner ℝ hw)).differentiableAt (by norm_num)
  change deriv (deriv (fun r => phi0 (r + 1))) s +
      gamma * deriv (fun r => phi0 (r + 1)) s + deriv (fun r => rho0 (r + 1)) s ≤ _
  rw [hphi2, hphi, hrho]
  simpa only [A, phi0, rho0] using hd

/-- Freeze the decreasing energy at a later time in the shifted distance
inequality.  This is the operator analogue of the scalar comparison input. -/
private theorem operator_shifted_distance_damped_frozen_energy_ineq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    {gamma a s t : ℝ} (hPhi : HasPotentialAssumption Phi) (hgamma : 0 < gamma)
    (hcoercive : ∀ y : H, gamma * ‖y‖ ^ 2 ≤ ⟪Gamma y, y⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    (ha : 0 ≤ a) (hat : a ≤ t) (hs : s ∈ Set.Ioc a t) :
    let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
    let phi0 : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2
    let rho0 : ℝ → ℝ := fun r =>
      (1 / 2 : ℝ) * ⟪A (sys.u r - x), sys.u r - x⟫_ℝ
    let phi : ℝ → ℝ := fun r => phi0 (r + 1)
    let rho : ℝ → ℝ := fun r => rho0 (r + 1)
    deriv (deriv phi) s + gamma * deriv phi s + deriv rho s ≤
      Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u (t + 1) 1‖ ^ 2 +
        Phi (sys.u (t + 1))) +
        (3 / 2 : ℝ) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
  dsimp
  have hd := operator_shifted_distance_damped_ineq hPhi gamma sys x
    (show 0 ≤ s by exact le_trans ha (le_of_lt hs.1))
  have hanti := operator_energy_antitone_pos hPhi hgamma hcoercive sys
    (show 0 < s + 1 by linarith [ha, hs.1])
    (show s + 1 ≤ t + 1 by linarith [hs.2])
  dsimp at hd
  calc
    _ ≤ Phi x - Phi (sys.u (s + 1)) + ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := hd
    _ ≤ _ := by linarith [hanti]

/-- Coercive operator damping makes the squared velocity integrable on the
closed time half-line.  This packages the endpoint and positive-tail estimates
for use by later operator-damped results. -/
theorem operator_velocity_sq_integrableOn_Ici_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (hGamma : HasCoerciveDamping Gamma)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) := by
  rcases hGamma with ⟨gamma, hgamma, hcoercive⟩
  rcases hPhi.bounded_below with ⟨m, hm⟩
  exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (operator_velocity_sq_integrableOn_Ioi_zero hPhi.contDiff hm hgamma hcoercive sys)

/-- Integration by parts for the exponentially weighted causal convolution.
This is the scalar identity used to absorb the derivative of the coercive
quadratic remainder in the operator-damped comparison estimate. -/
private theorem operator_exp_convolution_deriv_eq (rho : ℝ → ℝ) (gamma T : ℝ)
    (hT : 0 ≤ T) (hrho : ContDiffOn ℝ 1 rho (Set.Icc 0 T)) :
    (∫ r in 0..T, Real.exp (-gamma * (T - r)) * deriv rho r) =
      rho T - Real.exp (-gamma * T) * rho 0 -
        gamma * (∫ r in 0..T, Real.exp (-gamma * (T - r)) * rho r) := by
  rcases hT.eq_or_lt with rfl | hT
  · simp
  let G : ℝ → ℝ := fun r => Real.exp (gamma * r) * rho r
  have hG : ContDiffOn ℝ 1 G (Set.Icc 0 T) := by
    dsimp [G]
    exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn).mul hrho
  have hderiv : ∀ r ∈ Set.Ioo 0 T,
      deriv G r = Real.exp (gamma * r) * (gamma * rho r + deriv rho r) := by
    intro r hr
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (gamma * y))
        (gamma * Real.exp (gamma * r)) r := by
      convert (Real.hasDerivAt_exp (gamma * r)).comp r
        ((hasDerivAt_const (c := gamma) (x := r)).mul (hasDerivAt_id r)) using 1 <;> ring
    have hrho' : HasDerivAt rho (deriv rho r) r :=
      ((hrho.contDiffAt (Icc_mem_nhds hr.1 hr.2)).differentiableAt
        (by norm_num)).hasDerivAt
    convert (hexp.mul hrho').deriv using 1 <;> dsimp [G] <;> ring
  have hFTC : G T - G 0 = ∫ r in 0..T, deriv G r := by
    simpa [G] using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hG hT.le).symm
  have hGderivInt : IntervalIntegrable (deriv G) volume 0 T := by
    have hcont :=
      (hG.derivWithin (m := 0) (uniqueDiffOn_Icc hT) (by norm_num)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hT.le).congr_ae
    simp only [Set.uIoc_of_le hT.le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)
  have hDerivIntegral : (∫ r in 0..T, deriv G r) =
      ∫ r in 0..T, Real.exp (gamma * r) * (gamma * rho r + deriv rho r) := by
    apply intervalIntegral.integral_congr_ae
    simp only [Set.uIoc_of_le hT.le]
    apply MeasureTheory.ae_iff.mpr
    apply measure_mono_null ?_ (MeasureTheory.measure_singleton T)
    rintro r hr
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hr
    rcases hr with ⟨hrIoc, hbad⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hrT
    apply hbad
    exact hderiv r ⟨hrIoc.1, lt_of_le_of_ne hrIoc.2 hrT⟩
  have hexpCont : Continuous (fun r : ℝ => Real.exp (gamma * r)) := by
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hfirstInt : IntervalIntegrable (fun r => Real.exp (gamma * r) * (gamma * rho r))
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT.le
    simpa only [mul_assoc] using
      hexpCont.continuousOn.mul (continuousOn_const.mul hrho.continuousOn)
  have hrhoDerivInt : IntervalIntegrable (deriv rho) volume 0 T := by
    have hcont :=
      (hrho.derivWithin (m := 0) (uniqueDiffOn_Icc hT) (by norm_num)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hT.le).congr_ae
    simp only [Set.uIoc_of_le hT.le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)
  have hsecondInt : IntervalIntegrable (fun r => Real.exp (gamma * r) * deriv rho r)
      volume 0 T := by
    simpa only [mul_comm] using hrhoDerivInt.mul_continuousOn
      hexpCont.continuousOn
  have hsplit := intervalIntegral.integral_add hfirstInt hsecondInt
  have hsum : (∫ r in 0..T, Real.exp (gamma * r) *
      (gamma * rho r + deriv rho r)) =
      (∫ r in 0..T, Real.exp (gamma * r) * (gamma * rho r)) +
        ∫ r in 0..T, Real.exp (gamma * r) * deriv rho r := by
    rw [← hsplit]
    apply intervalIntegral.integral_congr_ae
    simp only [Set.uIoc_of_le hT.le]
    filter_upwards with r hr
    ring
  have hbaseInt : IntervalIntegrable (fun r => Real.exp (gamma * r) * rho r) volume 0 T :=
    hG.continuousOn.intervalIntegrable_of_Icc hT.le
  have hscale : (∫ r in 0..T, Real.exp (gamma * r) * (gamma * rho r)) =
      gamma * (∫ r in 0..T, Real.exp (gamma * r) * rho r) := by
    rw [show (fun r => Real.exp (gamma * r) * (gamma * rho r)) =
      fun r => gamma * (Real.exp (gamma * r) * rho r) by funext r; ring,
      intervalIntegral.integral_const_mul]
  have hmain : G T - G 0 = gamma * (∫ r in 0..T, Real.exp (gamma * r) * rho r) +
      ∫ r in 0..T, Real.exp (gamma * r) * deriv rho r := by
    rw [hFTC, hDerivIntegral, hsum, hscale]
  have hkernel : ∀ r : ℝ, Real.exp (-gamma * T) * Real.exp (gamma * r) =
      Real.exp (-gamma * (T - r)) := by
    intro r
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := congrArg (fun z : ℝ => Real.exp (-gamma * T) * z) hmain
  simp only [mul_sub, mul_add, mul_assoc] at hmul
  rw [show Real.exp (-gamma * T) * G T = rho T by
      dsimp [G]; rw [← mul_assoc, hkernel T]; simp,
    show Real.exp (-gamma * T) * G 0 = Real.exp (-gamma * T) * rho 0 by
      dsimp [G]; simp] at hmul
  have hweight (f : ℝ → ℝ) : Real.exp (-gamma * T) *
      (∫ r in 0..T, Real.exp (gamma * r) * f r) =
      ∫ r in 0..T, Real.exp (-gamma * (T - r)) * f r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    simp only [Set.uIoc_of_le hT.le]
    filter_upwards with r hr
    rw [← mul_assoc, hkernel]
  have hmul' : rho T - Real.exp (-gamma * T) * rho 0 =
      gamma * (∫ r in 0..T, Real.exp (-gamma * (T - r)) * rho r) +
        ∫ r in 0..T, Real.exp (-gamma * (T - r)) * deriv rho r := by
    rw [hmul, show Real.exp (-gamma * T) *
        (gamma * ∫ r in 0..T, Real.exp (gamma * r) * rho r) =
        gamma * (Real.exp (-gamma * T) *
          ∫ r in 0..T, Real.exp (gamma * r) * rho r) by ring,
      hweight, hweight]
  linarith

/-- Translating the velocity-square estimate to the positive shifted time axis.
This form is needed by the causal convolutions in the minimizing comparison. -/
theorem operator_shifted_velocity_sq_integrableOn_Ici_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    (hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0)) :
    IntegrableOn (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) (Set.Ici 0) := by
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
  have htail : IntegrableOn q (Set.Ici 1) :=
    hvel.mono_set (Set.Ici_subset_Ici.mpr (by norm_num))
  have hmap : IntegrableOn q (Set.Ici 1) (volume.map fun s : ℝ => s + 1) := by
    rwa [map_add_right_eq_self]
  have hshift :=
    ((Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding.integrableOn_map_iff).mp
      hmap
  simpa [q, Function.comp_def] using hshift

/-- A causal exponential convolution preserves integrability on the positive
half-line.  This is the measure-theoretic tail estimate used after shifting
the trajectory away from the endpoint. -/
theorem operator_causal_exp_convolution_integrable (g : ℝ → ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma) (hg : IntegrableOn g (Set.Ici 0)) :
    IntegrableOn (fun t : ℝ =>
      ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s|) (Set.Ici 0) := by
  have hG : IntegrableOn (fun s : ℝ => |g s|) (Set.Ici 0) := hg.abs
  have hkernel : IntegrableOn (fun t : ℝ => Real.exp ((-gamma) * t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hG' : IntegrableOn (fun s : ℝ => |g s|) (Set.Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp hG
  have hkernel' : IntegrableOn (fun s : ℝ => Real.exp ((-gamma) * s)) (Set.Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp hkernel
  have hconv := integrable_posConvolution hG' hkernel'
    (ContinuousLinearMap.mul ℝ ℝ)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply hconv.integrableOn.congr
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [posConvolution]
  simp only [Set.indicator_of_mem ht]
  change (∫ s in 0..t, |g s| * Real.exp ((-gamma) * (t - s))) = _
  simpa [mul_comm, mul_left_comm, mul_assoc]

/-- The twice-integrated shifted velocity error has a finite limit. -/
theorem operator_shifted_causal_velocity_error_converges
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H} {gamma : ℝ}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) (hgamma : 0 < gamma)
    (hvel : IntegrableOn (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) (Set.Ici 0)) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => (3 / 2 : ℝ) *
      ∫ theta in 0..t, ∫ s in 0..theta,
        Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2)
      atTop (nhds L) := by
  let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2
  have hqabs : ∀ s : ℝ, |q s| = q s := fun s => abs_of_nonneg (sq_nonneg _)
  have hq : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s) (Set.Ici 0) := by
    have h := operator_causal_exp_convolution_integrable q gamma hgamma hvel
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    simp only [hqabs]
  let L : ℝ := ∫ theta in Set.Ioi 0,
    ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s
  have hL : Tendsto (fun t : ℝ => ∫ theta in 0..t,
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s)
      atTop (nhds L) := by
    simpa [L] using intervalIntegral_tendsto_integral_Ioi 0
      ((integrableOn_Ici_iff_integrableOn_Ioi).mp hq) tendsto_id
  refine ⟨(3 / 2 : ℝ) * L, ?_⟩
  have hscale := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 / 2 : ℝ)) atTop
    (nhds (3 / 2))).mul hL
  simpa [q, mul_assoc] using hscale

/-- Once the operator-damped energy and potential have the same limit, the
kinetic part vanishes. -/
private theorem operator_velocity_tendsto_zero_of_energy_potential_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H} {m : ℝ}
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    (henergy : Tendsto (fun t =>
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) atTop (nhds m))
    (hpotential : Tendsto (fun t => Phi (sys.u t)) atTop (nhds m)) :
    Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) := by
  have hkinetic : Tendsto (fun t =>
      ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) - Phi (sys.u t))
      atTop (nhds 0) := by
    simpa using henergy.sub hpotential
  have hsq : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) atTop (nhds 0) := by
    have h := hkinetic.const_mul (2 : ℝ)
    convert h using 1 <;> ring
  have hnorm : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-! The shifted distance inequality can be integrated directly.  The coercive
quadratic remainder is kept on the left, where its endpoint contribution is
bounded below by zero. -/
private theorem operator_shifted_distance_frozen_integral
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    {gamma a T : ℝ} (hPhi : HasPotentialAssumption Phi) (hgamma : 0 < gamma)
    (hcoercive : ∀ y : H, gamma * ‖y‖ ^ 2 ≤ ⟪Gamma y, y⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    (ha : 0 ≤ a) (hTa : a ≤ T) :
    let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
    let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u (s + 1) - x‖ ^ 2
    let rho : ℝ → ℝ := fun s =>
      (1 / 2 : ℝ) * ⟪A (sys.u (s + 1) - x), sys.u (s + 1) - x⟫_ℝ
    deriv phi T - deriv phi a + gamma * (phi T - phi a) + rho T - rho a ≤
      (Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 +
        Phi (sys.u (T + 1)))) * (T - a) +
        (3 / 2 : ℝ) * (∫ s in a..T, ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) := by
  dsimp
  rcases hTa.eq_or_lt with rfl | hTa
  · simp
  let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u (s + 1) - x‖ ^ 2
  let rho : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * ⟪A (sys.u (s + 1) - x), sys.u (s + 1) - x⟫_ℝ
  have hphi : ContDiffOn ℝ 2 phi (Set.Icc a T) := by
    dsimp [phi]
    have hu : ContDiffOn ℝ 2 (fun s : ℝ => sys.u (s + 1)) (Set.Icc a T) :=
      sys.contDiff.comp ((contDiff_id.add contDiff_const).contDiffOn)
        (fun s hs => by
          exact add_nonneg (le_trans ha hs.1) (by norm_num))
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hphi' : ContDiffOn ℝ 1 (deriv phi) (Set.Icc a T) := by
    have hw := hphi.derivWithin (m := 1) (uniqueDiffOn_Icc hTa) (by norm_num)
    refine hw.congr ?_
    intro s hs
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Icc hTa) s hs)]
    have hspos : 0 < s + 1 := by
      linarith [ha, hs.1]
    have hglobal : ContDiffAt ℝ 2 phi s := by
      dsimp [phi]
      have hu : ContDiffAt ℝ 2 (fun r : ℝ => sys.u (r + 1)) s := by
        exact sys.contDiff.contDiffAt (Ici_mem_nhds hspos) |>.comp s
          (contDiffAt_id.add contDiffAt_const)
      exact contDiffAt_const.mul (ContDiffAt.norm_sq ℝ (hu.sub contDiffAt_const))
    exact hglobal.differentiableAt (by norm_num)
  have hrho : ContDiffOn ℝ 2 rho (Set.Icc a T) := by
    dsimp [rho]
    have hu : ContDiffOn ℝ 2 (fun s : ℝ => sys.u (s + 1)) (Set.Icc a T) :=
      sys.contDiff.comp ((contDiff_id.add contDiff_const).contDiffOn)
        (fun s hs => by
          exact add_nonneg (le_trans ha hs.1) (by norm_num))
    have hw : ContDiffOn ℝ 2 (fun s : ℝ =>
        A (sys.u (s + 1) - x)) (Set.Icc a T) :=
      contDiffOn_const.clm_apply (hu.sub contDiffOn_const)
    exact contDiffOn_const.mul (hw.inner ℝ (hu.sub contDiffOn_const))
  have hq : IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2)
      volume a T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hTa)).mpr
    exact (operator_shifted_velocity_sq_integrableOn_Ici_zero sys
      (operator_velocity_sq_integrableOn_Ici_zero hPhi ⟨gamma, hgamma, hcoercive⟩ sys)).mono_set
      (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr ha))
  have hineq : ∀ s ∈ Set.Ioo a T,
      deriv (deriv phi) s + gamma * deriv phi s + deriv rho s ≤
        Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 +
          Phi (sys.u (T + 1))) + (3 / 2 : ℝ) *
            ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    simpa [phi, rho, A] using
      (operator_shifted_distance_damped_frozen_energy_ineq hPhi hgamma hcoercive sys
        (x := x) (a := a) (s := s) (t := T) ha (le_of_lt hTa) ⟨hs.1, le_of_lt hs.2⟩)
  let c : ℝ := Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 +
    Phi (sys.u (T + 1)))
  have hineq' : ∀ s ∈ Set.Ioo a T,
      deriv (deriv phi) s + gamma * deriv phi s + deriv rho s ≤
        c + (3 / 2 : ℝ) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    simpa [c] using hineq s hs
  have hineq'' : ∀ s ∈ Set.Ioo a T,
      deriv (deriv phi) s + (gamma * deriv phi s + deriv rho s) ≤
        c + (3 / 2 : ℝ) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    simpa [add_assoc] using hineq' s hs
  have hderivphi : IntervalIntegrable (deriv (deriv phi)) volume a T := by
    have hc := (hphi'.derivWithin (m := 0) (uniqueDiffOn_Icc hTa) (by simp)).continuousOn
    apply (hc.intervalIntegrable_of_Icc hTa.le).congr_ae
    simp only [Set.uIoc_of_le hTa.le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  have hderivrho : IntervalIntegrable (deriv rho) volume a T := by
    have hc := (hrho.derivWithin (m := 0) (uniqueDiffOn_Icc hTa) (by simp)).continuousOn
    apply (hc.intervalIntegrable_of_Icc hTa.le).congr_ae
    simp only [Set.uIoc_of_le hTa.le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  have hgammaInt : IntervalIntegrable (fun s : ℝ => gamma * deriv phi s) volume a T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTa.le
    exact continuousOn_const.mul hphi'.continuousOn
  have hcInt : IntervalIntegrable (fun _ : ℝ => c) volume a T := intervalIntegrable_const
  have hrhsInt : IntervalIntegrable (fun s : ℝ => c +
      (3 / 2 : ℝ) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) volume a T :=
    hcInt.add (hq.const_mul (3 / 2 : ℝ))
  have hmain := intervalIntegral.integral_mono_on_of_le_Ioo hTa.le
    (hderivphi.add (hgammaInt.add hderivrho)) hrhsInt hineq''
  have hphiFTC : (∫ s in a..T, deriv phi s) = phi T - phi a := by
    simpa using intervalIntegral.integral_deriv_of_contDiffOn_Icc
      (hphi.of_le (by norm_num)) hTa.le
  have hphi2FTC : (∫ s in a..T, deriv (deriv phi) s) = deriv phi T - deriv phi a := by
    simpa using intervalIntegral.integral_deriv_of_contDiffOn_Icc hphi' hTa.le
  have hrhoFTC : (∫ s in a..T, deriv rho s) = rho T - rho a := by
    simpa using intervalIntegral.integral_deriv_of_contDiffOn_Icc
      (hrho.of_le (by norm_num)) hTa.le
  have hgammaFTC : (∫ s in a..T, gamma * deriv phi s) =
      gamma * (phi T - phi a) := by
    rw [intervalIntegral.integral_const_mul, hphiFTC]
  rw [intervalIntegral.integral_add hderivphi (hgammaInt.add hderivrho)] at hmain
  rw [intervalIntegral.integral_add hgammaInt hderivrho] at hmain
  rw [intervalIntegral.integral_add hcInt (hq.const_mul (3 / 2 : ℝ))] at hmain
  rw [hgammaFTC, hrhoFTC, intervalIntegral.integral_const] at hmain
  rw [intervalIntegral.integral_const_mul] at hmain
  rw [hphi2FTC] at hmain
  convert hmain using 1 <;>
    simp [phi, rho, A, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;>
    ring

/- The operator version of the distance-limit argument.  The quantity which
  has a directly controlled positive derivative is

      phi + (phi' + rho) / gamma,

  while the Gamma-distance is obtained from it after the velocity term has
  been shown to vanish. -/
private theorem operator_distance_to_minimizer_converges
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Gamma : H →L[ℝ] H} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    {gamma : ℝ}
    (hPhi : HasPotentialAssumption Phi) (hgamma : 0 < gamma)
    (hcoercive : ∀ y : H, gamma * ‖y‖ ^ 2 ≤ ⟪Gamma y, y⟫_ℝ)
    (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0)
    (hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0))
    (hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0))
    (z : H) (hz : z ∈ argmin Phi (potential_range_bddBelow hPhi)) :
    ∃ l : ℝ, Tendsto (fun t => (1 / (2 * gamma : ℝ)) *
      ⟪Gamma (sys.u t - z), sys.u t - z⟫_ℝ) atTop (nhds l) := by
  rcases hPhi.bounded_below with ⟨m, hm⟩
  let energy : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u (t + 1) 1‖ ^ 2
  let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
  let phi : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u (t + 1) - z‖ ^ 2
  let rho : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ⟪A (sys.u (t + 1) - z), sys.u (t + 1) - z⟫_ℝ
  let theta : ℝ → ℝ := fun t => phi t + gamma⁻¹ * (deriv phi t + rho t)
  have hvelShift : IntegrableOn q (Set.Ici 0) :=
    operator_shifted_velocity_sq_integrableOn_Ici_zero sys hvel
  have hu : ContDiffOn ℝ 2 (fun t : ℝ => sys.u (t + 1)) (Set.Ici 0) := by
    exact sys.contDiff.comp ((contDiff_id.add contDiff_const).contDiffOn)
      (fun t ht => by
        change 0 ≤ t at ht
        exact add_nonneg ht (by norm_num))
  have hphi : ContDiffOn ℝ 2 phi (Set.Ici 0) := by
    dsimp [phi]
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hrho : ContDiffOn ℝ 2 rho (Set.Ici 0) := by
    dsimp [rho]
    have hw : ContDiffOn ℝ 2 (fun t : ℝ => A (sys.u (t + 1) - z)) (Set.Ici 0) :=
      contDiffOn_const.clm_apply (hu.sub contDiffOn_const)
    exact contDiffOn_const.mul (hw.inner ℝ (hu.sub contDiffOn_const))
  have hphiDiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ phi t := by
    intro t ht
    change 0 ≤ t at ht
    have hu' : DifferentiableAt ℝ (fun s : ℝ => sys.u (s + 1)) t := by
      exact (operatorSystem_differentiableAt_pos sys (by linarith)).comp t
        (differentiableAt_id.add_const 1)
    simpa [phi] using (differentiableAt_const (c := (1 / 2 : ℝ))).mul
      ((hu'.sub_const z).norm_sq ℝ)
  have hphi' : ContDiffOn ℝ 1 (deriv phi) (Set.Ici 0) := by
    have hw := hphi.derivWithin (m := 1) (uniqueDiffOn_Ici 0)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    refine hw.congr ?_
    intro t ht
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) (hphiDiff t ht)]
  have htheta : ContDiffOn ℝ 1 theta (Set.Ici 0) := by
    dsimp [theta]
    convert (hphi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).add
      ((hphi'.add (hrho.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))).const_smul gamma⁻¹)
      using 1 <;> simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  have hthetaDiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ theta t := by
    intro t ht
    change 0 ≤ t at ht
    have hp : HasDerivAt phi (deriv phi t) t := (hphiDiff t ht).hasDerivAt
    have hphiGlobal : ContDiffAt ℝ 2 phi t := by
      have huG := sys.contDiff.contDiffAt (Ici_mem_nhds (by linarith : 0 < t + 1)) |>.comp t
        (contDiffAt_id.add contDiffAt_const)
      simpa [phi] using contDiffAt_const.mul (ContDiffAt.norm_sq ℝ (huG.sub contDiffAt_const))
    have hrhoGlobal : ContDiffAt ℝ 2 rho t := by
      have huG := sys.contDiff.contDiffAt (Ici_mem_nhds (by linarith : 0 < t + 1)) |>.comp t
        (contDiffAt_id.add contDiffAt_const)
      have hwG : ContDiffAt ℝ 2 (fun s : ℝ => A (sys.u (s + 1) - z)) t :=
        contDiffAt_const.clm_apply (huG.sub contDiffAt_const)
      simpa [rho] using contDiffAt_const.mul (hwG.inner ℝ (huG.sub contDiffAt_const))
    have hcdp := hphiGlobal.derivWithin (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpp : HasDerivAt (deriv phi) (deriv (deriv phi) t) t :=
      (hcdp.differentiableAt (by norm_num)).hasDerivAt
    have hr : HasDerivAt rho (deriv rho t) t :=
      (hrhoGlobal.differentiableAt (by norm_num)).hasDerivAt
    have hder := hp.add ((hpp.add hr).const_smul gamma⁻¹)
    have hfun : phi + gamma⁻¹ • (deriv phi + rho) =
        (fun s : ℝ => phi s + gamma⁻¹ * (deriv phi s + rho s)) := by
      funext s
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc, add_comm,
        add_left_comm]
      ring
    rw [hfun] at hder
    have hder' : HasDerivAt theta
        (deriv phi t + gamma⁻¹ * (deriv (deriv phi) t + deriv rho t)) t := by
      simpa [theta, div_eq_mul_inv, smul_eq_mul, mul_comm, add_comm, add_left_comm,
        add_assoc] using hder
    exact hder'.differentiableAt
  have htheta_deriv : ∀ t ∈ Set.Ici (0 : ℝ),
      deriv theta t = deriv phi t + (deriv (deriv phi) t + deriv rho t) / gamma := by
    intro t ht
    change 0 ≤ t at ht
    have hp : HasDerivAt phi (deriv phi t) t := (hphiDiff t ht).hasDerivAt
    have hphiGlobal : ContDiffAt ℝ 2 phi t := by
      have huG := sys.contDiff.contDiffAt (Ici_mem_nhds (by linarith : 0 < t + 1)) |>.comp t
        (contDiffAt_id.add contDiffAt_const)
      simpa [phi] using contDiffAt_const.mul (ContDiffAt.norm_sq ℝ (huG.sub contDiffAt_const))
    have hrhoGlobal : ContDiffAt ℝ 2 rho t := by
      have huG := sys.contDiff.contDiffAt (Ici_mem_nhds (by linarith : 0 < t + 1)) |>.comp t
        (contDiffAt_id.add contDiffAt_const)
      have hwG : ContDiffAt ℝ 2 (fun s : ℝ => A (sys.u (s + 1) - z)) t :=
        contDiffAt_const.clm_apply (huG.sub contDiffAt_const)
      simpa [rho] using contDiffAt_const.mul (hwG.inner ℝ (huG.sub contDiffAt_const))
    have hcdp := hphiGlobal.derivWithin (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpp : HasDerivAt (deriv phi) (deriv (deriv phi) t) t :=
      (hcdp.differentiableAt (by norm_num)).hasDerivAt
    have hr : HasDerivAt rho (deriv rho t) t :=
      (hrhoGlobal.differentiableAt (by norm_num)).hasDerivAt
    have hder := (hp.add ((hpp.add hr).const_smul gamma⁻¹)).deriv
    have hfun : phi + gamma⁻¹ • (deriv phi + rho) =
        (fun s : ℝ => phi s + gamma⁻¹ * (deriv phi s + rho s)) := by
      funext s
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc, add_comm,
        add_left_comm]
      ring
    rw [hfun] at hder
    have hder' : deriv theta t =
        deriv phi t + gamma⁻¹ * (deriv (deriv phi) t + deriv rho t) := by
      simpa [theta, div_eq_mul_inv, smul_eq_mul, mul_comm, add_comm, add_left_comm,
        add_assoc] using hder
    rw [hder']
    field_simp [hgamma.ne']
  have hineq : ∀ t ∈ Set.Ici (0 : ℝ),
      deriv (deriv phi) t + gamma * deriv phi t + deriv rho t ≤ q t := by
    intro t ht
    have hbase := operator_shifted_distance_damped_ineq hPhi gamma sys z ht
    have hzmin : Phi z = sInf (Set.range Phi) := hz
    have hpot := potential_sInf_le hPhi (sys.u (t + 1))
    dsimp [phi, rho, q, A] at hbase ⊢
    linarith
  have henergy_le_one : ∀ T : ℝ, 0 ≤ T → energy (T + 1) ≤ energy 1 := by
    intro T hT
    have hE := operator_energy_antitone_pos hPhi hgamma hcoercive sys
      (a := 1) (b := T + 1) (by norm_num) (by linarith)
    simpa [energy] using hE
  have hrho_nonneg : ∀ T : ℝ, 0 ≤ T → 0 ≤ rho T := by
    intro T hT
    have hA := operator_damping_remainder_nonnegative hcoercive
      (sys.u (T + 1) - z)
    have hA' : 0 ≤ ⟪A (sys.u (T + 1) - z), sys.u (T + 1) - z⟫_ℝ := by
      simpa [A] using hA
    dsimp [rho]
    nlinarith
  have hphi_deriv : ∀ T : ℝ, 0 ≤ T →
      deriv phi T = ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ := by
    intro T hT
    have hu' : HasDerivAt (fun s : ℝ => sys.u (s + 1) - z)
        (fderiv ℝ sys.u (T + 1) 1) T := by
      have hb := (operatorSystem_differentiableAt_pos sys (by linarith : 0 < T + 1)).hasFDerivAt
      exact (HasFDerivAt.comp_hasDerivAt T hb
        ((hasDerivAt_id T).add_const 1)).sub_const z
    have hs := (hasDerivAt_const T (1 / 2 : ℝ)).mul hu'.norm_sq
    convert hs.deriv using 1 <;> simp [phi, real_inner_comm] <;> ring
  let K : ℝ := (energy 1 - m) / gamma
  have hLB : ∀ T : ℝ, 0 ≤ T →
      -K ≤ deriv phi T + gamma * phi T + rho T := by
    intro T hT
    have hkin : (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 ≤ energy 1 - m := by
      have hE := henergy_le_one T hT
      have hmT := hm (sys.u (T + 1))
      dsimp [energy] at hE ⊢
      linarith
    have hinner := real_inner_le_norm
      (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - z)
    have hinner' : -‖fderiv ℝ sys.u (T + 1) 1‖ * ‖sys.u (T + 1) - z‖ ≤
        ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ := by
      simpa [mul_comm] using
        (neg_le_of_abs_le (abs_real_inner_le_norm
          (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - z)))
    have hsq : 0 ≤ (‖fderiv ℝ sys.u (T + 1) 1‖ -
        gamma * ‖sys.u (T + 1) - z‖) ^ 2 := sq_nonneg _
    have hA := hrho_nonneg T hT
    rw [hphi_deriv T hT]
    dsimp [K, phi] at ⊢
    rw [← neg_div]
    apply (div_le_iff₀ hgamma).2
    dsimp [rho] at hA ⊢
    nlinarith [hkin, hinner', hsq]
  have hthetaLower : ∃ c : ℝ, ∀ t ∈ Set.Ici (0 : ℝ), c ≤ theta t := by
    refine ⟨-K / gamma, ?_⟩
    intro t ht
    apply (div_le_iff₀ hgamma).2
    rw [show theta t * gamma = deriv phi t + gamma * phi t + rho t by
      dsimp [theta]
      field_simp [hgamma.ne']
      ring]
    exact hLB t ht
  have htheta_ineq : ∀ t ∈ Set.Ici (0 : ℝ), deriv theta t ≤ q t / gamma := by
    intro t ht
    have hid : deriv phi t + (deriv (deriv phi) t + deriv rho t) / gamma =
        (gamma * deriv phi t + deriv (deriv phi) t + deriv rho t) / gamma := by
      field_simp [hgamma.ne']
      ring
    rw [htheta_deriv t ht, hid]
    apply (div_le_div_iff_of_pos_right hgamma).2
    have hi := hineq t ht
    dsimp [q]
    nlinarith
  have hthetaDerivCont : ContinuousOn (deriv theta) (Set.Ici 0) := by
    have hw := htheta.derivWithin (m := 0) (uniqueDiffOn_Ici 0)
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)
    refine hw.continuousOn.congr ?_
    intro t ht
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) (hthetaDiff t ht)]
  have hpositive : IntegrableOn (fun t => max (deriv theta t) 0) (Set.Ici 0) := by
    have hmaj : IntegrableOn (fun t : ℝ => gamma⁻¹ * q t) (Set.Ici 0) :=
      hvelShift.const_mul gamma⁻¹
    have hmeas : AEStronglyMeasurable (fun t : ℝ => max (deriv theta t) 0)
        (volume.restrict (Set.Ici 0)) := by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
      exact fun t ht => (hthetaDerivCont t ht).max continuousWithinAt_const
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
        ‖max (deriv theta t) 0‖ ≤ gamma⁻¹ * q t := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have hi := htheta_ineq t ht
      have hq0 : 0 ≤ q t := sq_nonneg _
      have hg0 : 0 ≤ gamma⁻¹ := le_of_lt (inv_pos.mpr hgamma)
      exact max_le (by simpa [div_eq_mul_inv, mul_comm] using hi) (by positivity)
    exact hmaj.mono' hmeas hbound
  obtain ⟨thetaLimit, hthetaLimit⟩ :=
    converges_of_integrable_positive_derivative theta htheta hthetaLower hpositive
  have hthetaUpper : ∀ᶠ T in atTop, theta T ≤ thetaLimit + 1 := by
    have hev := (tendsto_order.1 hthetaLimit).2 (thetaLimit + 1) (by linarith)
    filter_upwards [hev] with T hT
    linarith
  let B : ℝ := energy 1 - m
  let V : ℝ := 1 + 2 * B
  let C : ℝ := thetaLimit + 1
  let Y : ℝ := 1 + 2 * (V + |gamma * C| + 1) / gamma
  have hB : 0 ≤ B := by
    dsimp [B, energy]
    have hm1 := hm (sys.u 1)
    have hkin0 : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u 1 1‖ ^ 2 := by positivity
    linarith
  have hV_nonneg : 0 ≤ V := by dsimp [V]; nlinarith
  have hV_bound : ∀ T : ℝ, 0 ≤ T → ‖fderiv ℝ sys.u (T + 1) 1‖ ≤ V := by
    intro T hT
    have hkin : (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 ≤ B := by
      have hE := henergy_le_one T hT
      have hmT := hm (sys.u (T + 1))
      dsimp [energy, B] at hE ⊢
      linarith
    dsimp [V]
    nlinarith [sq_nonneg (B - 1), sq_nonneg ‖fderiv ℝ sys.u (T + 1) 1‖]
  have hphi_bound_eventually : ∀ᶠ T in atTop,
      ‖sys.u (T + 1) - z‖ ≤ Y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hthetaUpper] with T hT hC
    by_contra hnot
    have hY : Y < ‖sys.u (T + 1) - z‖ := lt_of_not_ge hnot
    let y : ℝ := ‖sys.u (T + 1) - z‖
    let vnorm : ℝ := ‖fderiv ℝ sys.u (T + 1) 1‖
    have hYpos : 0 < Y := by
      dsimp [Y]
      have hsum : 0 < V + |gamma * C| + 1 := by
        nlinarith [hV_nonneg, abs_nonneg (gamma * C)]
      have htmp : 0 < 2 * (V + |gamma * C| + 1) / gamma :=
        div_pos (mul_pos (by norm_num) hsum) hgamma
      linarith
    have hy0 : 0 < y := lt_trans hYpos hY
    have hY1 : 1 < y := by
      have hsum : 0 < V + |gamma * C| + 1 := by
        nlinarith [hV_nonneg, abs_nonneg (gamma * C)]
      have htmp : 0 < 2 * (V + |gamma * C| + 1) / gamma :=
        div_pos (mul_pos (by norm_num) hsum) hgamma
      have hone : 1 < Y := by dsimp [Y]; linarith
      exact lt_trans hone hY
    have hv : vnorm ≤ V := hV_bound T hT
    have hinner : -vnorm * y ≤
        ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ := by
      simpa [y, vnorm, mul_comm] using
        (neg_le_of_abs_le (abs_real_inner_le_norm
          (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - z)))
    have hinnerV : -V * y ≤
        ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ :=
      le_trans (mul_le_mul_of_nonneg_right (neg_le_neg hv) (le_of_lt hy0)) hinner
    have hquad : gamma / 2 * y ^ 2 - V * y ≤ gamma * C := by
      have hmul := mul_le_mul_of_nonneg_left hC hgamma.le
      rw [show gamma * theta T = gamma * phi T + deriv phi T + rho T by
        dsimp [theta]
        field_simp [hgamma.ne']
        ring] at hmul
      rw [hphi_deriv T hT] at hmul
      dsimp [phi, C, y, vnorm] at hmul ⊢
      have hρ := hrho_nonneg T hT
      nlinarith [hinnerV, hρ]
    have hVD : V + |gamma * C| + 1 < gamma * y / 2 := by
      have hquot : 2 * (V + |gamma * C| + 1) / gamma < y := by
        dsimp [Y] at hY
        linarith
      have hquot' := (div_lt_iff₀ hgamma).mp hquot
      nlinarith
    have hD : gamma * C < |gamma * C| + 1 := by
      have := le_abs_self (gamma * C)
      linarith
    have hprod1 : (|gamma * C| + 1) * y < gamma / 2 * y ^ 2 - V * y := by
      have := mul_lt_mul_of_pos_right hVD hy0
      nlinarith
    have hprod2 : gamma * C < (|gamma * C| + 1) * y := by
      have hDpos : 0 < |gamma * C| + 1 := by positivity
      have hDy : |gamma * C| + 1 < (|gamma * C| + 1) * y := by
        have := mul_lt_mul_of_pos_left hY1 hDpos
        simpa using this
      exact hD.trans hDy
    linarith
  have hvelShift0 : Tendsto (fun T : ℝ => fderiv ℝ sys.u (T + 1) 1) atTop (nhds 0) := by
    exact hvel0.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have hphiDeriv0 : Tendsto (fun T : ℝ => deriv phi T) atTop (nhds 0) := by
    have hvn : Tendsto (fun T : ℝ => ‖fderiv ℝ sys.u (T + 1) 1‖) atTop (nhds 0) := by
      simpa [Function.comp_def] using (tendsto_norm.comp hvelShift0)
    have hprod : Tendsto (fun T : ℝ => Y * ‖fderiv ℝ sys.u (T + 1) 1‖)
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hvn)
    have hnegprod : Tendsto (fun T : ℝ => -(Y * ‖fderiv ℝ sys.u (T + 1) 1‖))
        atTop (nhds 0) := by simpa using hprod.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegprod hprod
    · filter_upwards [hphi_bound_eventually, eventually_ge_atTop (0 : ℝ)] with T hT hT0
      have hi := abs_real_inner_le_norm
        (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - z)
      rw [hphi_deriv T hT0]
      have hiY : |⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ| ≤
          Y * ‖fderiv ℝ sys.u (T + 1) 1‖ := by
        calc
          _ ≤ ‖fderiv ℝ sys.u (T + 1) 1‖ * ‖sys.u (T + 1) - z‖ := hi
          _ ≤ ‖fderiv ℝ sys.u (T + 1) 1‖ * Y :=
            mul_le_mul_of_nonneg_left hT (norm_nonneg _)
          _ = _ := by ring
      exact neg_le_of_abs_le hiY
    · filter_upwards [hphi_bound_eventually, eventually_ge_atTop (0 : ℝ)] with T hT hT0
      have hi := abs_real_inner_le_norm
        (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - z)
      rw [hphi_deriv T hT0]
      have hiY : |⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - z⟫_ℝ| ≤
          Y * ‖fderiv ℝ sys.u (T + 1) 1‖ := by
        calc
          _ ≤ ‖fderiv ℝ sys.u (T + 1) 1‖ * ‖sys.u (T + 1) - z‖ := hi
          _ ≤ ‖fderiv ℝ sys.u (T + 1) 1‖ * Y :=
            mul_le_mul_of_nonneg_left hT (norm_nonneg _)
          _ = _ := by ring
      exact (le_abs_self _).trans hiY
  let mu : ℝ → ℝ := fun t => phi t + rho t / gamma
  have hmu : Tendsto mu atTop (nhds thetaLimit) := by
    have hid : ∀ t : ℝ, mu t = theta t - deriv phi t / gamma := by
      intro t
      dsimp [mu, theta]
      field_simp [hgamma.ne']
      ring
    have hlim : Tendsto (fun t => theta t - deriv phi t / gamma) atTop
        (nhds thetaLimit) := by
      simpa using (hthetaLimit.sub (hphiDeriv0.div_const gamma))
    apply hlim.congr'
    filter_upwards with t
    rw [hid]
  have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  refine ⟨thetaLimit, ?_⟩
  apply (hmu.comp hshift).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht_eq : t - 1 + 1 = t := by ring
  dsimp [mu, phi, rho, A]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left]
  rw [ht_eq]
  field_simp [hgamma.ne']
  have hinner : ⟪sys.u t - z, sys.u t - z⟫_ℝ = ‖sys.u t - z‖ ^ 2 :=
    real_inner_self_eq_norm_sq (sys.u t - z)
  have hsplit : ⟪sys.u t, sys.u t - z⟫_ℝ - ⟪z, sys.u t - z⟫_ℝ =
      ⟪sys.u t - z, sys.u t - z⟫_ℝ := by
    rw [← inner_sub_left]
  nlinarith [hinner, hsplit]

/-- Theorem 2.6: the minimizing and weak-convergence conclusions persist for coercive
self-adjoint operator damping. -/
theorem operator_damped_minimizing_property {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (hGamma : HasCoerciveDamping Gamma) (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) ∧
    Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) ∧
    Tendsto (fun t => Phi (sys.u t)) atTop (nhds (sInf (Set.range Phi))) ∧
    ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty →
      ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi),
      Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop (nhds (toWeakSpace ℝ H uhat))) := by
  rcases hGamma with ⟨gamma, hgamma, hcoercive⟩
  have hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    operator_velocity_sq_integrableOn_Ici_zero hPhi ⟨gamma, hgamma, hcoercive⟩ sys
  have hvelShift : IntegrableOn (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) (Set.Ici 0) :=
    operator_shifted_velocity_sq_integrableOn_Ici_zero sys hvel
  obtain ⟨velocityErrorLimit, hvelocityErrorLimit⟩ :=
    operator_shifted_causal_velocity_error_converges sys hgamma hvelShift
  obtain ⟨energyLimit, henergyLimit⟩ :=
    operator_energy_converges hPhi hgamma hcoercive sys
  let energy : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let velocityError : ℝ → ℝ := fun t => (3 / 2 : ℝ) *
    ∫ theta in 0..t, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2
  have henergy : Tendsto energy atTop (nhds energyLimit) := by
    simpa [energy] using henergyLimit
  have hvelocityError : Tendsto velocityError atTop (nhds velocityErrorLimit) := by
    simpa [velocityError] using hvelocityErrorLimit
  have henergyLower : ∀ t : ℝ, sInf (Set.range Phi) ≤ energy t := by
    intro t
    dsimp [energy]
    have hpotential := potential_sInf_le hPhi (sys.u t)
    have hkinetic : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      positivity
    linarith
  have hpotential_le_energy : ∀ t : ℝ, Phi (sys.u t) ≤ energy t := by
    intro t
    dsimp [energy]
    have hkinetic : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      positivity
    linarith
  have henergyLowerLimit : sInf (Set.range Phi) ≤ energyLimit := by
    exact ge_of_tendsto henergy (Filter.Eventually.of_forall henergyLower)
  let comparisonCoefficient : ℝ → ℝ := fun t =>
    (gamma * t - 1 + Real.exp (-gamma * t)) / gamma ^ 2
  have hcomparisonCoefficient : Tendsto comparisonCoefficient atTop atTop := by
    let lower : ℝ → ℝ := fun t => (1 / gamma) * t + (-1 / gamma ^ 2)
    have hlower : Tendsto lower atTop atTop := by
      have hlinear : Tendsto (fun t : ℝ => (1 / gamma) * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos (one_div_pos.mpr hgamma)).mpr tendsto_id
      exact tendsto_atTop_add_const_right atTop (-1 / gamma ^ 2) hlinear
    apply Filter.tendsto_atTop_mono _ hlower
    intro t
    have hsq : 0 < gamma ^ 2 := sq_pos_of_pos hgamma
    have hexp : 0 ≤ Real.exp (-gamma * t) := (Real.exp_pos _).le
    have hrewrite : lower t = (gamma * t - 1) / gamma ^ 2 := by
      dsimp [lower]
      field_simp [hgamma.ne']
      ring
    rw [hrewrite]
    dsimp [comparisonCoefficient]
    exact (div_le_div_iff_of_pos_right hsq).mpr (by linarith)
  refine ⟨hvel, ?_⟩
  rcases hPhi.bounded_below with ⟨m, hm⟩
  have henergyEq : energyLimit = sInf (Set.range Phi) := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < energyLimit - sInf (Set.range Phi) := by
        linarith [henergyLowerLimit]
      let delta : ℝ := (energyLimit - sInf (Set.range Phi)) / 4
      have hdelta : 0 < delta := by
        dsimp [delta]
        linarith
      rcases exists_lt_of_csInf_lt (b := sInf (Set.range Phi) + delta)
        (Set.range_nonempty Phi) (by
          dsimp [delta]
          linarith) with ⟨_, ⟨x, rfl⟩, hx⟩
      have henergyShift : Tendsto (fun T : ℝ => energy (T + 1)) atTop
          (nhds energyLimit) := by
        have hshift : Tendsto (fun T : ℝ => T + 1) atTop atTop := by
          simpa [add_comm] using
            (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
        exact henergy.comp hshift
      have hcx : ∀ᶠ T in atTop, Phi x - energy (T + 1) ≤ -delta := by
        have hev := (tendsto_order.1 henergyShift).1 (energyLimit - delta) (by
          linarith)
        filter_upwards [hev] with T hT
        have hx' : Phi x ≤ sInf (Set.range Phi) + delta := hx.le
        have hrel : energyLimit - sInf (Set.range Phi) = 4 * delta := by
          dsimp [delta]
          ring
        linarith [hx, hT, hrel]
      let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2
      have hqIoi : IntegrableOn q (Set.Ioi 0) := by
        exact (integrableOn_Ici_iff_integrableOn_Ioi).mp hvelShift
      let Q : ℝ := ∫ s in Set.Ioi 0, q s
      have hQ : ∀ T : ℝ, 0 ≤ T → (∫ s in 0..T, q s) ≤ Q := by
        intro T hT
        have htail : 0 ≤ ∫ s in Set.Ioi T, q s := by
          exact MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
        have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hqIoi hT
        linarith
      let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
      let phi : ℝ → ℝ := fun s =>
        (1 / 2 : ℝ) * ‖sys.u (s + 1) - x‖ ^ 2
      let rho : ℝ → ℝ := fun s =>
        (1 / 2 : ℝ) * ⟪A (sys.u (s + 1) - x), sys.u (s + 1) - x⟫_ℝ
      have hphi_deriv : ∀ T : ℝ, 0 ≤ T →
          deriv phi T = ⟪fderiv ℝ sys.u (T + 1) 1,
            sys.u (T + 1) - x⟫_ℝ := by
        intro T hT
        have hu : HasDerivAt (fun s : ℝ => sys.u (s + 1) - x)
            (fderiv ℝ sys.u (T + 1) 1) T := by
          have hcomp : HasDerivAt (fun s : ℝ => sys.u (s + 1))
              (fderiv ℝ sys.u (T + 1) 1) T := by
            have hbase := (operatorSystem_differentiableAt_pos sys (t := T + 1)
              (by linarith)).hasFDerivAt
            have hcomp' : HasDerivAt (fun s : ℝ => sys.u (s + 1))
                (fderiv ℝ sys.u (T + 1) 1) T := by
              simpa [Function.comp_def] using
                HasFDerivAt.comp_hasDerivAt T hbase
                  ((hasDerivAt_id T).add_const 1)
            exact hcomp'
          exact hcomp.sub_const x
        have hsquare := (hasDerivAt_const T (1 / 2 : ℝ)).mul (hu.norm_sq)
        convert hsquare.deriv using 1 <;> simp [phi, real_inner_comm] <;> ring
      have hrho_nonneg : ∀ T : ℝ, 0 ≤ rho T := by
        intro T
        have hA := operator_damping_remainder_nonnegative hcoercive
          (sys.u (T + 1) - x)
        have hA' : 0 ≤ ⟪A (sys.u (T + 1) - x),
            sys.u (T + 1) - x⟫_ℝ := by
          simpa [A] using hA
        dsimp [rho]
        nlinarith
      have henergy_le_one : ∀ T : ℝ, 0 ≤ T → energy (T + 1) ≤ energy 1 := by
        intro T hT
        have hE := operator_energy_antitone_pos hPhi hgamma hcoercive sys
          (a := 1) (b := T + 1) (by norm_num) (by linarith)
        simpa [energy] using hE
      let K : ℝ := (energy 1 - m) / gamma
      have hLB : ∀ T : ℝ, 0 ≤ T →
          -K ≤ deriv phi T + gamma * phi T + rho T := by
        intro T hT
        have hkin : (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 ≤
            energy 1 - m := by
          have hE := henergy_le_one T hT
          have hmT := hm (sys.u (T + 1))
          dsimp [energy] at hE ⊢
          linarith
        have hinner := real_inner_le_norm
          (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - x)
        have hinner' : -‖fderiv ℝ sys.u (T + 1) 1‖ *
            ‖sys.u (T + 1) - x‖ ≤
            ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - x⟫_ℝ := by
          simpa [mul_comm] using
            (neg_le_of_abs_le (abs_real_inner_le_norm
              (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - x)))
        have hsq : 0 ≤ (‖fderiv ℝ sys.u (T + 1) 1‖ -
            gamma * ‖sys.u (T + 1) - x‖) ^ 2 := sq_nonneg _
        have hA := hrho_nonneg T
        rw [hphi_deriv T hT]
        dsimp [K, phi] at ⊢
        rw [← neg_div]
        apply (div_le_iff₀ hgamma).2
        dsimp [rho] at hA ⊢
        nlinarith [hkin, hinner', hsq]
      let C : ℝ := deriv phi 0 + gamma * phi 0 + rho 0
      have hlarge : ∀ᶠ T in atTop,
          (K + C + (3 / 2 : ℝ) * Q + 1) / delta < T := eventually_gt_atTop _
      obtain ⟨T, hT0, hTx, hTlarge⟩ :=
        ((eventually_ge_atTop (0 : ℝ)).and (hcx.and hlarge)).exists
      have hfreeze := operator_shifted_distance_frozen_integral hPhi hgamma
        hcoercive sys (x := x) (gamma := gamma) (a := 0) (T := T)
        (by norm_num) hT0
      have hfreeze' : deriv phi T - deriv phi 0 +
          gamma * (phi T - phi 0) + rho T - rho 0 ≤
          (Phi x - energy (T + 1)) * T +
            (3 / 2 : ℝ) * (∫ s in 0..T, q s) := by
        dsimp [phi, rho, A, energy, q] at hfreeze ⊢
        linarith
      have hlower : -K - C ≤ deriv phi T - deriv phi 0 +
          gamma * (phi T - phi 0) + rho T - rho 0 := by
        have h := hLB T hT0
        dsimp [C]
        linarith
      have hupper : (Phi x - energy (T + 1)) * T +
          (3 / 2 : ℝ) * (∫ s in 0..T, q s) ≤
            -delta * T + (3 / 2 : ℝ) * Q := by
        have hq := hQ T hT0
        have hq' := mul_le_mul_of_nonneg_left hq
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        nlinarith [hTx, hq']
      have hcontr : -K - C ≤ -delta * T + (3 / 2 : ℝ) * Q :=
        le_trans hlower (le_trans hfreeze' hupper)
      have hdeltaT : K + C + (3 / 2 : ℝ) * Q + 1 < delta * T := by
        have := (div_lt_iff₀ hdelta).mp hTlarge
        linarith
      linarith
    · exact henergyLowerLimit
  have hpotential : Tendsto (fun t => Phi (sys.u t)) atTop
      (nhds (sInf (Set.range Phi))) := by
    have henergy' : Tendsto energy atTop
        (nhds (sInf (Set.range Phi))) := by
      simpa [henergyEq] using henergy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => sInf (Set.range Phi)) atTop
        (nhds (sInf (Set.range Phi)))) henergy'
    · intro t
      exact potential_sInf_le hPhi (sys.u t)
    · exact hpotential_le_energy
  have hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) := by
    exact operator_velocity_tendsto_zero_of_energy_potential_tendsto sys henergy
      (by simpa [henergyEq] using hpotential)
  refine ⟨hvel0, hpotential, ?_⟩
  intro hne
  let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
  let d : H → H → ℝ := fun x z =>
    (1 / (2 * gamma : ℝ)) * ⟪Gamma (x - z), x - z⟫_ℝ
  have hd_nonneg : ∀ x z : H, 0 ≤ d x z := by
    intro x z
    have hi : 0 ≤ ⟪Gamma (x - z), x - z⟫_ℝ := by
      exact le_trans (by positivity) (hcoercive (x - z))
    exact mul_nonneg (by positivity) hi
  have hd_limit : ∀ z ∈ S, ∃ l : ℝ,
      Tendsto (fun t => d (sys.u t) z) atTop (nhds l) := by
    intro z hz
    simpa [d, S] using
      (operator_distance_to_minimizer_converges hPhi hgamma hcoercive sys hvel hvel0 z hz)
  have hcluster_time : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (sys.u (u n))) atTop (nhds (f z))) → z ∈ S := by
    intro z hz
    rcases hz with ⟨u, hu, hweak⟩
    have hphiSeq : Tendsto (fun n => Phi (sys.u (u n))) atTop
        (nhds (sInf (Set.range Phi))) := by
      simpa [Function.comp_def] using hpotential.comp hu
    have hweak' : Tendsto (fun n => toWeakSpace ℝ H (sys.u (u n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right _ z).2
      intro y
      let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) y
      have hf := hweak f
      simpa [f, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
    have hzle : Phi z ≤ sInf (Set.range Phi) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hev := (tendsto_order.1 hphiSeq).2 (sInf (Set.range Phi) + ε) (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      let v : ℕ → H := fun n => sys.u (u (n + N))
      have hv_mem : ∀ n : ℕ, v n ∈ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        intro n
        dsimp [v]
        exact le_of_lt (hN (n + N) (by omega))
      have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        exact eventually_atTop.2 ⟨b, fun n hn => le_trans hn (Nat.le_add_right n N)⟩
      have hvweak : Tendsto (fun n => toWeakSpace ℝ H (v n)) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [v, Function.comp_def] using hweak'.comp hshift
      have hclosed : IsClosed {w : H | Phi w ≤ sInf (Set.range Phi) + ε} :=
        isClosed_le hPhi.contDiff.continuous continuous_const
      have hconvex : Convex ℝ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        simpa only [Set.mem_univ, true_and] using hPhi.convex.convex_le
          (sInf (Set.range Phi) + ε)
      exact mem_of_tendsto_weakly_of_isClosed_convex hclosed hconvex hv_mem hvweak
    have hzmin : Phi z = sInf (Set.range Phi) :=
      le_antisymm hzle (potential_sInf_le hPhi z)
    simpa [S, argmin] using hzmin
  have htime_sequence : ∀ (t : ℕ → ℝ), Tendsto t atTop atTop →
      ∃ z ∈ S, Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
    intro t ht
    let x : ℕ → H := fun n => sys.u (t n)
    have hdist_seq : ∀ z ∈ S, ∃ l : ℝ,
        Tendsto (fun n => d (x n) z) atTop (nhds l) := by
      intro z hz
      rcases hd_limit z hz with ⟨l, hl⟩
      exact ⟨l, by simpa [x, Function.comp_def] using hl.comp ht⟩
    rcases hne with ⟨z0, hz0⟩
    rcases hd_limit z0 hz0 with ⟨l0, hl0⟩
    have hq0 : Tendsto (fun n => d (x n) z0) atTop (nhds l0) := by
      simpa [x, Function.comp_def] using hl0.comp ht
    have hq_bounded : Bornology.IsBounded (Set.range (fun n => d (x n) z0)) :=
      Metric.isBounded_range_of_tendsto _ hq0
    rcases isBounded_iff_forall_norm_le.mp hq_bounded with ⟨C, hC⟩
    have hbounded : Bornology.IsBounded (Set.range x) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨1 + 2 * C + ‖z0‖, ?_⟩
      rintro y ⟨n, rfl⟩
      have hqC := hC (d (x n) z0) (Set.mem_range_self n)
      have hqC' : d (x n) z0 ≤ C := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg _ _)] at hqC
        exact hqC
      have hden : 0 < 2 * gamma := by positivity
      have hinnerC : ⟪Gamma (x n - z0), x n - z0⟫_ℝ ≤ 2 * gamma * C := by
        have hqC'' : ⟪Gamma (x n - z0), x n - z0⟫_ℝ / (2 * gamma) ≤ C := by
          rw [show ⟪Gamma (x n - z0), x n - z0⟫_ℝ / (2 * gamma) =
              d (x n) z0 by
            dsimp [d]
            field_simp [hgamma.ne']
            ]
          exact hqC'
        simpa [mul_comm] using (div_le_iff₀ hden).mp hqC''
      have hnormsq : ‖x n - z0‖ ^ 2 ≤ 2 * C := by
        have hc := hcoercive (x n - z0)
        nlinarith
      have hCnonneg : 0 ≤ C := by
        have hqC0 := hC (d (x 0) z0) (Set.mem_range_self 0)
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg _ _)] at hqC0
        exact le_trans (hd_nonneg _ _) hqC0
      have hnorm : ‖x n - z0‖ ≤ 1 + 2 * C := by
        nlinarith [sq_nonneg ‖x n - z0‖, norm_nonneg (x n - z0)]
      calc
        ‖x n‖ = ‖(x n - z0) + z0‖ := by abel_nf
        _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
        _ ≤ 1 + 2 * C + ‖z0‖ := by linarith
    have hcluster_seq : ∀ z,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H z) → z ∈ S := by
      intro z hz
      rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφweak⟩
      apply hcluster_time z
      refine ⟨t ∘ φ, ?_, ?_⟩
      · simpa [Function.comp_def] using ht.comp hφ.tendsto_atTop
      · intro f
        exact tendsto_apply_of_tendsto_toWeakSpace hφweak f
    have hunique : ∀ y z : H,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H z) → y = z := by
      intro y z hy hz
      have hyS := hcluster_seq y hy
      have hzS := hcluster_seq z hz
      rcases hdist_seq y hyS with ⟨ly, hly⟩
      rcases hdist_seq z hzS with ⟨lz, hlz⟩
      have hdiff := hlz.sub hly
      have hscaled := hdiff.const_mul (2 * gamma)
      let c : ℝ := ⟪Gamma z, z⟫_ℝ - ⟪Gamma y, y⟫_ℝ
      have hrel : ∀ n : ℕ,
          2 * gamma * (d (x n) z - d (x n) y) =
            2 * ⟪Gamma (x n), y - z⟫_ℝ + c := by
        intro n
        have hsxy := sys.self_adjoint.isSymmetric (x n) (y - z)
        dsimp [d, c]
        field_simp [hgamma.ne']
        simp only [ContinuousLinearMap.map_sub, inner_sub_left, inner_sub_right]
        have hzx : ⟪Gamma z, x n⟫_ℝ = ⟪Gamma (x n), z⟫_ℝ := by
          calc
            ⟪Gamma z, x n⟫_ℝ = ⟪z, Gamma (x n)⟫_ℝ :=
              sys.self_adjoint.isSymmetric z (x n)
            _ = ⟪Gamma (x n), z⟫_ℝ := real_inner_comm _ _
        have hyx : ⟪Gamma y, x n⟫_ℝ = ⟪Gamma (x n), y⟫_ℝ := by
          calc
            ⟪Gamma y, x n⟫_ℝ = ⟪y, Gamma (x n)⟫_ℝ :=
              sys.self_adjoint.isSymmetric y (x n)
            _ = ⟪Gamma (x n), y⟫_ℝ := real_inner_comm _ _
        rw [hzx, hyx]
        ring
      have hlin : Tendsto (fun n => 2 * ⟪Gamma (x n), y - z⟫_ℝ) atTop
          (nhds (2 * gamma * (lz - ly) - c)) := by
        have htmp := hscaled.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
        apply htmp.congr'
        filter_upwards with n
        rw [hrel n]
        ring
      rcases hy with ⟨φ, hφ, hφweak⟩
      rcases hz with ⟨ψ, hψ, hψweak⟩
      let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) (Gamma (y - z))
      have hf_y : Tendsto (fun n => ⟪Gamma (x (φ n)), y - z⟫_ℝ) atTop
          (nhds (⟪Gamma y, y - z⟫_ℝ)) := by
        have hf := tendsto_apply_of_tendsto_toWeakSpace hφweak f
        have heq : ∀ v : H, f v = ⟪Gamma v, y - z⟫_ℝ := by
          intro v
          dsimp [f]
          rw [real_inner_comm]
          exact (sys.self_adjoint.isSymmetric v (y - z)).symm
        have hf' : Tendsto (fun n => f (x (φ n))) atTop
            (nhds (⟪Gamma y, y - z⟫_ℝ)) := by
          simpa [heq y] using hf
        apply hf'.congr'
        filter_upwards with n
        rw [heq]
      have hf_z : Tendsto (fun n => ⟪Gamma (x (ψ n)), y - z⟫_ℝ) atTop
          (nhds (⟪Gamma z, y - z⟫_ℝ)) := by
        have hf := tendsto_apply_of_tendsto_toWeakSpace hψweak f
        have heq : ∀ v : H, f v = ⟪Gamma v, y - z⟫_ℝ := by
          intro v
          dsimp [f]
          rw [real_inner_comm]
          exact (sys.self_adjoint.isSymmetric v (y - z)).symm
        have hf' : Tendsto (fun n => f (x (ψ n))) atTop
            (nhds (⟪Gamma z, y - z⟫_ℝ)) := by
          simpa [heq z] using hf
        apply hf'.congr'
        filter_upwards with n
        rw [heq]
      have hfy2 := hf_y.const_mul (2 : ℝ)
      have hfz2 := hf_z.const_mul (2 : ℝ)
      have hy_eq : 2 * ⟪Gamma y, y - z⟫_ℝ = 2 * gamma * (lz - ly) - c :=
        tendsto_nhds_unique hfy2 (hlin.comp hφ.tendsto_atTop)
      have hz_eq : 2 * ⟪Gamma z, y - z⟫_ℝ = 2 * gamma * (lz - ly) - c :=
        tendsto_nhds_unique hfz2 (hlin.comp hψ.tendsto_atTop)
      have hcross : ⟪Gamma y, y - z⟫_ℝ - ⟪Gamma z, y - z⟫_ℝ = 0 := by
        linarith [hy_eq, hz_eq]
      have hzero : ⟪y - z, Gamma (y - z)⟫_ℝ = 0 := by
        rw [inner_sub_left]
        calc
          ⟪y, Gamma (y - z)⟫_ℝ - ⟪z, Gamma (y - z)⟫_ℝ =
              ⟪Gamma y, y - z⟫_ℝ - ⟪Gamma z, y - z⟫_ℝ := by
                congr 1
                · exact (sys.self_adjoint.isSymmetric y (y - z)).symm
                · exact (sys.self_adjoint.isSymmetric z (y - z)).symm
          _ = 0 := hcross
      have hcoer := hcoercive (y - z)
      have hnormsq : ‖y - z‖ ^ 2 ≤ 0 := by
        rw [real_inner_comm] at hzero
        nlinarith
      have hnorm : ‖y - z‖ = 0 := by
        nlinarith [sq_nonneg ‖y - z‖, norm_nonneg (y - z)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x).2
        ⟨hbounded, hunique⟩ with ⟨z, hz⟩
    have hzcluster : IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
        (toWeakSpace ℝ H z) := by
      exact ⟨id, strictMono_id, by simpa using hz⟩
    exact ⟨z, hcluster_seq z hzcluster, by simpa [x] using hz⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  obtain ⟨uhat, hUhat, hUweak⟩ := htime_sequence (fun n : ℕ => (n : ℝ)) hnat
  have h_all_sequences : ∀ t : ℕ → ℝ, Tendsto t atTop atTop →
      Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H uhat)) := by
    intro t ht
    let q : ℕ → ℝ := fun n => if Even n then ((n / 2 : ℕ) : ℝ) else t (n / 2)
    have hinterleave : Tendsto q atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro R
      obtain ⟨N, hN⟩ := exists_nat_ge R
      rcases (eventually_atTop.1 (ht.eventually (eventually_ge_atTop R))) with ⟨M, hM⟩
      refine ⟨2 * max N M, ?_⟩
      intro k hk
      have hdiv : max N M ≤ k / 2 := by omega
      by_cases he : Even k
      · simp [q, he]
        exact le_trans hN (Nat.cast_le.2 (le_trans (le_max_left _ _) hdiv))
      · simp [q, he]
        exact hM _ (le_trans (le_max_right _ _) hdiv)
    have hq : Tendsto q atTop atTop := hinterleave
    obtain ⟨w, hwS, hqweak⟩ := htime_sequence q hq
    have hEven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn => by omega⟩
    have hOdd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn => by omega⟩
    have hq_even : ∀ n : ℕ, q (2 * n) = (n : ℝ) := by
      intro n
      simp only [q, if_pos (even_two_mul n)]
      norm_cast
      omega
    have hq_odd : ∀ n : ℕ, q (2 * n + 1) = t n := by
      intro n
      simp only [q, if_neg (Nat.not_even_two_mul_add_one n)]
      congr 1
      omega
    have hnat_w : Tendsto (fun n : ℕ => toWeakSpace ℝ H (sys.u (n : ℝ))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hEven using 1
      ext n
      simp [Function.comp, hq_even]
    have hzw : uhat = w :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique hUweak hnat_w)
    have ht_w : Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hOdd using 1
      ext n
      simp [Function.comp, hq_odd]
    simpa [hzw] using ht_w
  refine ⟨uhat, hUhat, ?_⟩
  apply (weakConvergence_iff_forall_tendsto_inner_right sys.u uhat).2
  intro y
  have hreal : Tendsto (fun t : ℝ => ⟪sys.u t, y⟫_ℝ) atTop
      (nhds (⟪uhat, y⟫_ℝ)) := by
    by_contra hg
    rw [Metric.tendsto_atTop] at hg
    push Not at hg
    rcases hg with ⟨ε, hε, hbad⟩
    choose s hs_ge hs_bad using hbad
    have hs : Tendsto (fun n : ℕ => s n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro R
      obtain ⟨N, hN⟩ := exists_nat_ge R
      refine ⟨N, fun n hn => le_trans (le_trans hN (Nat.cast_le.2 hn)) (hs_ge n)⟩
    have hseq := h_all_sequences (fun n : ℕ => s n) hs
    have hf := tendsto_apply_of_tendsto_toWeakSpace hseq
      ((InnerProductSpace.toDual ℝ H) y)
    have hseq' : Tendsto (fun n : ℕ => ⟪sys.u (s n), y⟫_ℝ) atTop
        (nhds (⟪uhat, y⟫_ℝ)) := by
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
    rw [Metric.tendsto_atTop] at hseq'
    rcases hseq' ε hε with ⟨N, hN⟩
    exact (not_lt_of_ge (hs_bad N)) (by simpa using hN N le_rfl)
  exact hreal

end Alvarez2000
