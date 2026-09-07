import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_lem_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.lem_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.lem_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_5
import Foundation.Convex.ArgminExistence

namespace Alvarez2000

open Filter
open MeasureTheory
open scoped InnerProductSpace Topology

/-- The pointwise lower bound in `(h_Phi)` supplies the boundedness required by `argmin`. -/
theorem potential_range_bddBelow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Phi : H → ℝ} (hPhi : HasPotentialAssumption Phi) : BddBelow (Set.range Phi) := by
  rcases hPhi.bounded_below with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hm x

/-- The infimum of a potential range is below every potential value. -/
theorem potential_sInf_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Phi : H → ℝ} (hPhi : HasPotentialAssumption Phi) (x : H) :
    sInf (Set.range Phi) ≤ Phi x :=
  csInf_le (potential_range_bddBelow hPhi) (Set.mem_range_self x)

/-- A pointwise lower bound on a potential is also a lower bound for its infimum. -/
theorem potential_lower_bound_le_sInf {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Phi : H → ℝ} (hPhi : HasPotentialAssumption Phi) :
    ∃ m : ℝ, m ≤ sInf (Set.range Phi) := by
  rcases hPhi.bounded_below with ⟨m, hm⟩
  refine ⟨m, le_csInf ?_ ?_⟩
  · exact Set.range_nonempty Phi
  · rintro _ ⟨x, rfl⟩
    exact hm x

/-- The trajectory is differentiable at every strictly positive time. -/
theorem dissipativeSystem_differentiableAt_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ sys.u t := by
  exact (sys.contDiff.contDiffAt (Ici_mem_nhds ht)).differentiableAt (by norm_num)

/-- On the interior of the time domain, `fderiv` is the ordinary trajectory derivative. -/
theorem dissipativeSystem_deriv_eq_fderiv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {t : ℝ} (ht : 0 < t) :
    deriv sys.u t = fderiv ℝ sys.u t 1 := by
  exact (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt.deriv

/-- Chain rule for the potential along a scalar-damped trajectory away from the endpoint. -/
theorem dissipativeSystem_potential_deriv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => Phi (sys.u s)) t =
      ⟪gradPhi (sys.u t), fderiv ℝ sys.u t 1⟫_ℝ := by
  have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
    (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
  have hPhi : HasGradientAt Phi (gradPhi (sys.u t)) (sys.u t) := sys.is_gradient _
  simpa using (hPhi.hasFDerivAt.comp_hasDerivAt t hu).deriv

/-- The velocity has the derivative occurring in the scalar-damped equation at
every strictly positive time. -/
theorem dissipativeSystem_velocity_hasDerivAt_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => fderiv ℝ sys.u s 1)
      (fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1) t := by
  have hu := sys.contDiff.contDiffAt (Ici_mem_nhds ht)
  have hv : ContDiffAt ℝ 1 (fun s => fderiv ℝ sys.u s 1) t := by
    exact (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  exact (hv.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasDerivAt

/-- Away from the endpoint, the scalar-damped energy dissipates at rate
`gamma * ‖u'‖²`. -/
theorem scalar_damped_energy_deriv_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 + Phi (sys.u s)) t =
      -gamma * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : H := fderiv ℝ v t 1
  have hv : HasDerivAt v a t := by
    simpa only [v, a] using dissipativeSystem_velocity_hasDerivAt_pos sys ht
  have hk : HasDerivAt (fun s => (1 / 2 : ℝ) * ‖v s‖ ^ 2)
      ((1 / 2 : ℝ) * (2 * ⟪v t, a⟫_ℝ)) t := by
    simpa using (hasDerivAt_const t (1 / 2 : ℝ)).mul (hv.norm_sq)
  have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
    (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
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
  rw [inner_smul_left, real_inner_self_eq_norm_sq] at hinner
  norm_num at hinner ⊢
  linarith

/-- The first-order support inequality for the differentiable convex potential. -/
theorem scalar_convex_gradient_support {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Phi : H → ℝ} {gradPhi : H → H}
    (hconv : ConvexOn ℝ Set.univ Phi) (hgrad : ∀ x, HasGradientAt Phi (gradPhi x) x)
    (x y : H) : Phi x + ⟪gradPhi x, y - x⟫_ℝ ≤ Phi y := by
  let q : ℝ → ℝ := fun s => Phi (x + s • (y - x))
  have hqconv : ConvexOn ℝ Set.univ q := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb α β hα0 hβ0 hab
    have h := hconv.2 (Set.mem_univ (x + a • (y - x)))
      (Set.mem_univ (x + b • (y - x))) hα0 hβ0 hab
    change q (α * a + β * b) ≤ α • q a + β • q b
    dsimp [q]
    have hcomb : α • (x + a • (y - x)) + β • (x + b • (y - x)) =
        x + (α * a + β * b) • (y - x) := by
      calc
        _ = (α + β) • x + (α * a + β * b) • (y - x) := by module
        _ = _ := by rw [hab, one_smul]
    rw [hcomb] at h
    exact h
  have hline : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (y - x)).const_add x using 1 <;> simp
  have hqderiv : HasDerivAt q ⟪gradPhi x, y - x⟫_ℝ 0 := by
    have h := (hgrad (x + 0 • (y - x))).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa [q, InnerProductSpace.toDual_apply] using h
  have hslope := hqconv.le_slope_of_hasDerivAt (by simp) (by simp)
    (show (0 : ℝ) < 1 by norm_num) hqderiv
  dsimp [q, slope] at hslope
  norm_num at hslope
  linarith

/-- The squared distance to an arbitrary point satisfies the damped differential
inequality used in the minimizing-property argument. -/
private theorem scalar_distance_damped_ineq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (x : H) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2)) t +
        gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - x‖ ^ 2) t ≤
      Phi x - Phi (sys.u t) + ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
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
    convert hsq using 1 <;> simp [phi, real_inner_comm] <;> ring
  have hfirst : ∀ᶠ s in nhds t,
      deriv phi s = ⟪v s, sys.u s - x⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hus : HasDerivAt sys.u (v s) s := by
      simpa only [v] using (dissipativeSystem_differentiableAt_pos sys hs).hasDerivAt
    have hsubs : HasDerivAt (fun r => sys.u r - x) (v s) s := by
      simpa only using hus.sub_const x
    have hsqs := (hasDerivAt_const s (1 / 2 : ℝ)).mul hsubs.norm_sq
    have : HasDerivAt phi ⟪v s, sys.u s - x⟫_ℝ s := by
      convert hsqs using 1 <;> simp [phi, real_inner_comm] <;> ring
    exact this.deriv
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
  change deriv (deriv phi) t + gamma * deriv phi t ≤ _
  rw [hsecond, hphi.deriv]
  simp only [v, a] at hinnerEq ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left] at hinnerEq
  simp only [inner_zero_left, add_zero] at hinnerEq
  have hneg : ⟪gradPhi (sys.u t), x - sys.u t⟫_ℝ =
      -⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    rw [show x - sys.u t = -(sys.u t - x) by abel, inner_neg_right]
  have hgrad : Phi (sys.u t) - Phi x ≤ ⟪gradPhi (sys.u t), sys.u t - x⟫_ℝ := by
    rw [hneg] at hsupp
    linarith [hsupp]
  have hdamped :
      ⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, sys.u t - x⟫_ℝ +
          gamma * ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ ≤ Phi x - Phi (sys.u t) := by
    linarith [hinnerEq, hgrad]
  linarith

/-- Energy balance on a compact interval lying strictly inside the time domain. -/
private theorem scalar_energy_interval {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u b 1‖ ^ 2 + Phi (sys.u b)) +
        gamma * (∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2) =
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u a 1‖ ^ 2 + Phi (sys.u a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 + Phi (sys.u s)
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

/-- On strictly positive time intervals, the mechanical energy is antitone.  This
is kept public because later results use the same dissipation comparison. -/
theorem scalar_energy_antitone_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u b 1‖ ^ 2 + Phi (sys.u b) ≤
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u a 1‖ ^ 2 + Phi (sys.u a) := by
  have hbalance := scalar_energy_interval hPhi sys ha hab
  have hint_nonneg : 0 ≤ ∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    exact intervalIntegral.integral_nonneg_of_forall hab
      (fun t => sq_nonneg ‖fderiv ℝ sys.u t 1‖)
  have hdiss_nonneg : 0 ≤ gamma * (∫ t in a..b, ‖fderiv ℝ sys.u t 1‖ ^ 2) :=
    mul_nonneg (le_of_lt sys.gamma_pos) hint_nonneg
  linarith

/-- The mechanical energy is bounded below by the infimum of the potential. -/
theorem potential_sInf_le_scalar_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (t : ℝ) :
    sInf (Set.range Phi) ≤
      (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t) := by
  have hpot := potential_sInf_le hPhi (sys.u t)
  have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by positivity
  linarith

/-- Dissipation and the lower potential bound give a finite limit for the
mechanical energy.  Identifying this limit with `inf Phi` is the remaining
minimizing-property argument. -/
theorem scalar_energy_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    ∃ L : ℝ, Tendsto
      (fun t => (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) atTop (nhds L) := by
  let E : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let Epos : ℝ → ℝ := fun t => E (max t 1)
  have hanti : Antitone Epos := by
    intro s t hst
    apply scalar_energy_antitone_pos hPhi sys
    · dsimp [Epos]
      linarith [le_max_right s 1]
    · dsimp [Epos]
      exact max_le_max_right 1 hst
  obtain ⟨m, hm⟩ := potential_lower_bound_le_sInf hPhi
  have hbelow : BddBelow (Set.range Epos) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hm.trans (potential_sInf_le_scalar_energy hPhi sys (max t 1))
  have hlim : Tendsto Epos atTop (nhds (⨅ t : ℝ, Epos t)) :=
    tendsto_atTop_ciInf hanti hbelow
  refine ⟨⨅ t : ℝ, Epos t, ?_⟩
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp [Epos, E, max_eq_left ht]

/-- Away from the initial endpoint, the velocity is continuously differentiable. -/
private theorem scalarSystem_velocity_contDiffOn_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    ContDiffOn ℝ 1 (fun t => fderiv ℝ sys.u t 1) (Set.Ioi 0) := by
  have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
    sys.contDiff.mono Set.Ioi_subset_Ici_self
  exact (hu.fderiv_of_isOpen isOpen_Ioi
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffOn_const

/-- The squared velocity is integrable on compact intervals in positive time. -/
private theorem scalar_velocity_sq_integrableOn_Icc_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} {eps T : ℝ} (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (heps : 0 < eps) (hET : eps ≤ T) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Icc eps T) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hET).mp
  apply ContinuousOn.intervalIntegrable_of_Icc hET
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le heps ht.1
  have hv := (scalarSystem_velocity_contDiffOn_pos sys).contDiffAt (Ioi_mem_nhds htpos)
  exact (hv.norm_sq ℝ).continuousAt.continuousWithinAt

/-- The scalar energy balance controls the squared velocity on the positive tail. -/
private theorem scalar_velocity_sq_integrableOn_Ioi_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 1) := by
  rcases hPhi.bounded_below with ⟨m, hm⟩
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
  let C : ℝ := (((1 / 2 : ℝ) * ‖fderiv ℝ sys.u 1 1‖ ^ 2 + Phi (sys.u 1)) - m) / gamma
  have hbound : ∀ n : ℕ, (∫ t in 1..(n + 1 : ℝ), ‖q t‖) ≤ C := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have henergy := scalar_energy_interval hPhi sys (a := 1) (b := (n + 1 : ℝ))
      (by norm_num) hn
    have hmend : m ≤ Phi (sys.u ((n : ℝ) + 1)) := hm _
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u ((n : ℝ) + 1) 1‖ ^ 2 := by positivity
    have hnonneg : ∀ t : ℝ, 0 ≤ q t := fun t => sq_nonneg _
    rw [show (fun t => ‖q t‖) = q by funext t; exact Real.norm_of_nonneg (hnonneg t)]
    dsimp [q, C]
    apply (le_div_iff₀ sys.gamma_pos).2
    nlinarith [henergy]
  have hlocal : ∀ n : ℕ, IntegrableOn q (Set.Ioc 1 (n + 1 : ℝ)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (scalar_velocity_sq_integrableOn_Icc_pos sys (by norm_num)
      (by linarith)).mono_set Set.Ioc_subset_Icc_self
  have hTendsto : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := integrableOn_Ioi_of_intervalIntegral_norm_bounded C 1 hlocal hTendsto
    (Filter.Eventually.of_forall hbound)
  simpa only [q] using h

/-- One-sided regularity controls the finite initial interval. -/
private theorem scalar_velocity_sq_integrableOn_Ioc_zero_one {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioc 0 1) := by
  let w : ℝ → H := fun t => fderivWithin ℝ sys.u (Set.Ici 0) t 1
  have hw : ContinuousOn w (Set.Icc 0 1) := by
    have hcont : ContinuousOn (fderivWithin ℝ sys.u (Set.Ici 0)) (Set.Ici 0) :=
      sys.contDiff.continuousOn_fderivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact (hcont.mono Set.Icc_subset_Ici_self).clm_apply continuousOn_const
  have hsqcont : ContinuousOn (fun t => ‖w t‖ ^ 2) (Set.Icc 0 1) := by
    intro t ht
    exact (continuous_norm.continuousAt.comp_continuousWithinAt (hw t ht)).pow 2
  have hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Icc 0 1) := hsqcont.integrableOn_Icc
  have hsq' : IntegrableOn (fun t => ‖w t‖ ^ 2) (Set.Ioc 0 1) :=
    hsq.mono_set Set.Ioc_subset_Icc_self
  apply hsq'.congr_fun
  · intro t ht
    have hdiff : DifferentiableAt ℝ sys.u t :=
      dissipativeSystem_differentiableAt_pos sys ht.1
    have hfd : fderivWithin ℝ sys.u (Set.Ici 0) t = fderiv ℝ sys.u t :=
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t (le_of_lt ht.1)) hdiff
    simp only [w]
    rw [hfd]
  · exact measurableSet_Ioc

/-- Combining the finite initial interval with the dissipative tail. -/
private theorem scalar_velocity_sq_integrableOn_Ioi_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (scalar_velocity_sq_integrableOn_Ioc_zero_one sys).union
    (scalar_velocity_sq_integrableOn_Ioi_one hPhi sys)

/-- Once a minimizer is fixed, the damped distance inequality and the
integrability of the velocity show that the distance to that minimizer has a
limit.  The shift by one avoids differentiating the trajectory at its
one-sided initial endpoint. -/
theorem scalar_distance_to_minimizer_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0))
    (z : H) (hz : z ∈ argmin Phi (potential_range_bddBelow hPhi)) :
    ∃ l : ℝ, Tendsto (fun t => ‖sys.u t - z‖) atTop (nhds l) := by
  let theta : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u (t + 1) - z‖ ^ 2
  have htheta : ContDiffOn ℝ 2 theta (Set.Ici 0) := by
    have hu : ContDiffOn ℝ 2 (fun t : ℝ => sys.u (t + 1)) (Set.Ici 0) := by
      exact sys.contDiff.comp ((contDiff_id.add contDiff_const).contDiffOn)
        (fun t ht => by
          change 0 ≤ t at ht
          simpa only [Set.mem_Ici] using add_nonneg ht (by norm_num))
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hthetaDiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ theta t := by
    intro t ht
    change 0 ≤ t at ht
    have hu : DifferentiableAt ℝ (fun s : ℝ => sys.u (s + 1)) t :=
      (dissipativeSystem_differentiableAt_pos sys (by linarith : 0 < t + 1)).comp t
        (differentiableAt_id.add_const 1)
    simpa [theta] using (differentiableAt_const (c := (1 / 2 : ℝ))).mul
      ((hu.sub_const z).norm_sq ℝ)
  have homega : ContDiffOn ℝ 1 (fun t => deriv theta t) (Set.Ici 0) := by
    have hwithin : ContDiffOn ℝ 1 (derivWithin theta (Set.Ici 0)) (Set.Ici 0) :=
      htheta.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact hwithin.congr fun t ht => by
      rw [deriv, derivWithin,
        fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) (hthetaDiff t ht)]
  have hthetaDeriv : ∀ s : ℝ, -1 < s →
      deriv theta s = deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by linarith
    have hphiDiff : DifferentiableAt ℝ (fun r =>
        (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2) (s + 1) := by
      have hu := dissipativeSystem_differentiableAt_pos sys hspos
      simpa using (differentiableAt_const (c := (1 / 2 : ℝ))).mul
        ((hu.sub_const z).norm_sq ℝ)
    change deriv ((fun r => (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2) ∘ fun r : ℝ => r + 1) s = _
    convert deriv_comp s hphiDiff (differentiableAt_id.add_const 1) using 1 <;> simp
  have hthetaSecond : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s =
        deriv (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2)) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by
      change 0 ≤ s at hs
      linarith
    have hderivDiff : DifferentiableAt ℝ
        (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2)) (s + 1) := by
      have hcd : ContDiffAt ℝ 2 (fun r => (1 / 2 : ℝ) * ‖sys.u r - z‖ ^ 2) (s + 1) := by
        have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
          sys.contDiff.mono Set.Ioi_subset_Ici_self
        exact (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))).contDiffAt
          (Ioi_mem_nhds hspos)
      exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hevent : deriv theta =ᶠ[nhds s] fun r =>
        deriv (fun q => (1 / 2 : ℝ) * ‖sys.u q - z‖ ^ 2) (r + 1) := by
      filter_upwards [Ioi_mem_nhds (by linarith : -1 < s)] with r hr
      exact hthetaDeriv r hr
    rw [Filter.EventuallyEq.deriv_eq hevent]
    convert deriv_comp s hderivDiff (differentiableAt_id.add_const 1) using 1 <;> simp
  have hforce : IntegrableOn (fun s : ℝ => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2)
      (Set.Ici 0) := by
    have heq := (measurePreserving_add_right volume (1 : ℝ)).integrableOn_comp_preimage
      (Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding
        (f := fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) (s := Set.Ici 0)
    rw [Set.preimage_add_const_Ici] at heq
    have hfull : IntegrableOn ((fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) ∘
        fun s : ℝ => s + 1) (Set.Ici (0 - 1)) := heq.mpr hvel
    exact hfull.mono_set (Set.Ici_subset_Ici.mpr (by norm_num : (0 - 1 : ℝ) ≤ 0))
  have hmin : ∀ t : ℝ, Phi z ≤ Phi (sys.u t) := by
    intro t
    rw [hz]
    exact potential_sInf_le hPhi _
  have hineq : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s + gamma * deriv theta s ≤
        ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    rw [hthetaSecond s hs, hthetaDeriv s (by
      change 0 ≤ s at hs
      linarith)]
    have hd := scalar_distance_damped_ineq hPhi sys z (by
      change 0 ≤ s at hs
      linarith : 0 < s + 1)
    have hgap : Phi z - Phi (sys.u (s + 1)) ≤ 0 := by linarith [hmin (s + 1)]
    exact hd.trans (by linarith)
  have hpositive : IntegrableOn (fun s => max (deriv theta s) 0) (Set.Ici 0) :=
    positive_part_integrable_of_damped_inequality (fun s => deriv theta s)
      (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) gamma homega sys.gamma_pos hineq hforce
  obtain ⟨ell, hell⟩ := converges_of_integrable_positive_derivative theta
    (htheta.of_le (by norm_num)) (by
      refine ⟨0, ?_⟩
      intro s hs
      dsimp [theta]
      positivity) hpositive
  have hsqShift : Tendsto (fun s : ℝ => ‖sys.u (s + 1) - z‖ ^ 2) atTop
      (nhds (2 * ell)) := by
    have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul hell
    simpa [theta] using hscaled
  have hnormShift : Tendsto (fun s : ℝ => ‖sys.u (s + 1) - z‖) atTop
      (nhds (Real.sqrt (2 * ell))) := by
    have hsqrt := Real.continuous_sqrt.tendsto (2 * ell) |>.comp hsqShift
    apply hsqrt.congr'
    filter_upwards with s
    simp only [Function.comp_apply, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  refine ⟨Real.sqrt (2 * ell), ?_⟩
  convert hnormShift.comp hshift using 1
  ext t
  congr 2
  ring

/-- Once the energy and the potential have the same limit, the kinetic part
vanishes.  Keeping this elementary limit conversion separate makes the
minimizing comparison responsible only for identifying the common limit. -/
private theorem scalar_velocity_tendsto_zero_of_energy_potential_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma m : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
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

/-- Freezing the decreasing energy at a later time gives the inhomogeneous
damped distance inequality used in the two integrations of the minimizing
comparison.  This form is reusable by later continuous-time arguments. -/
theorem scalar_distance_damped_frozen_energy_ineq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {a s t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (hs : s ∈ Set.Ioc a t) :
    deriv (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2)) s +
        gamma * deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) s ≤
      Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) +
        (3 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 := by
  have hspos : 0 < s := lt_of_lt_of_le ha (le_of_lt hs.1)
  have hd := scalar_distance_damped_ineq hPhi sys x hspos
  have hanti := scalar_energy_antitone_pos hPhi sys hspos hs.2
  linarith

/-- The causal exponential convolution of an integrable forcing is integrable
on the positive half-line.  It supplies the bounded error term in the
twice-integrated scalar comparison. -/
theorem scalar_causal_exp_convolution_integrable (g : ℝ → ℝ) (gamma : ℝ)
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

/-- The triangular exponential error generated by the squared velocity has a
finite limit.  This is the Fubini/Tonelli boundedness input in (2.3). -/
theorem scalar_causal_velocity_error_converges
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel : IntegrableOn (fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2) (Set.Ici 0)) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => (3 / 2 : ℝ) *
      ∫ theta in 1..t, ∫ s in 0..theta,
        Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2)
      atTop (nhds L) := by
  let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2
  have hqabs : ∀ s : ℝ, |q s| = q s := by
    intro s
    exact abs_of_nonneg (sq_nonneg _)
  have hq : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s) (Set.Ici 0) := by
    have h := scalar_causal_exp_convolution_integrable q gamma sys.gamma_pos hvel
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    simp only [hqabs]
  have hqIoi : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s) (Set.Ioi 1) :=
    hq.mono_set (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr (by norm_num)))
  let L : ℝ := ∫ theta in Set.Ioi 1,
    ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s
  have hL : Tendsto (fun t : ℝ => ∫ theta in 1..t,
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s)
      atTop (nhds L) := by
    simpa [L] using intervalIntegral_tendsto_integral_Ioi 1 hqIoi tendsto_id
  refine ⟨(3 / 2 : ℝ) * L, ?_⟩
  have hscale := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 / 2 : ℝ)) atTop
    (nhds (3 / 2))).mul hL
  simpa [q, mul_assoc] using hscale

/-- A compact-interval integrating-factor estimate for the frozen-energy
distance inequality.  Keeping the forcing under the integral avoids any
endpoint differentiability issue and is the first half of Alvarez' (2.3). -/
private theorem scalar_frozen_energy_first_integral
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 x : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {theta t : ℝ}
    (h1theta : 1 ≤ theta) (htheta : theta ≤ t) :
    deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) theta ≤
      Real.exp (-gamma * (theta - 1)) *
          deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
        ∫ s in 1..theta, Real.exp (-gamma * (theta - s)) *
          (Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) +
            (3 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2) := by
  rcases h1theta.eq_or_lt with rfl | h1theta
  · simp
  let p : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2
  let c : ℝ := Phi x - ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t))
  let g : ℝ → ℝ := fun s => c + (3 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2
  let F : ℝ → ℝ := fun s => Real.exp (gamma * (s - 1)) * deriv p s
  have hp : ContDiffOn ℝ 2 p (Set.Icc 1 theta) := by
    have hu : ContDiffOn ℝ 2 sys.u (Set.Icc 1 theta) :=
      sys.contDiff.mono (fun s hs => le_trans (by norm_num) hs.1)
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hderivp : ContDiffOn ℝ 1 (deriv p) (Set.Icc 1 theta) := by
    have hwithin := hp.derivWithin (m := 1) (uniqueDiffOn_Icc h1theta) (by norm_num)
    refine hwithin.congr ?_
    intro s hs
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Icc h1theta) s hs)]
    have hpdiff : DifferentiableAt ℝ p s := by
      dsimp [p]
      have hu : DifferentiableAt ℝ sys.u s :=
        dissipativeSystem_differentiableAt_pos sys (by linarith [hs.1])
      exact (differentiableAt_const (c := (1 / 2 : ℝ))).mul
        ((hu.sub_const x).norm_sq ℝ)
    exact hpdiff
  have hF : ContDiffOn ℝ 1 F (Set.Icc 1 theta) := by
    dsimp [F]
    exact (Real.contDiff_exp.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))).contDiffOn.mul hderivp
  have hg : ContinuousOn g (Set.Icc 1 theta) := by
    dsimp [g, c]
    have hu : ContDiffOn ℝ 2 sys.u (Set.Icc 1 theta) :=
      sys.contDiff.mono (fun s hs => le_trans (by norm_num) hs.1)
    have hv : ContDiffOn ℝ 1 (fun s => fderiv ℝ sys.u s 1) (Set.Icc 1 theta) := by
      intro s hs
      have hlocal : ContDiffAt ℝ 2 sys.u s :=
        sys.contDiff.contDiffAt (Ici_mem_nhds (by linarith [hs.1]))
      have hvelocity : ContDiffAt ℝ 1 (fun r => fderiv ℝ sys.u r 1) s :=
        (hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))
      exact hvelocity.contDiffWithinAt
    exact continuousOn_const.add (continuousOn_const.mul (ContDiffOn.norm_sq ℝ hv).continuousOn)
  have hFint : IntervalIntegrable (deriv F) volume 1 theta := by
    have hc := (hF.derivWithin (m := 0) (uniqueDiffOn_Icc h1theta) (by simp)).continuousOn
    apply (hc.intervalIntegrable_of_Icc h1theta.le).congr_ae
    simp only [h1theta.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  have hgint : IntervalIntegrable (fun s => Real.exp (gamma * (s - 1)) * g s)
      volume 1 theta := by
    exact (ContinuousOn.mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_id.sub continuous_const)) |>.continuousOn) hg).intervalIntegrable_of_Icc h1theta.le
  have hpoint : ∀ s ∈ Set.Ioo 1 theta,
      deriv F s ≤ Real.exp (gamma * (s - 1)) * g s := by
    intro s hs
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (gamma * (r - 1)))
        (gamma * Real.exp (gamma * (s - 1))) s := by
      convert (Real.hasDerivAt_exp (gamma * (s - 1))).comp s
        ((hasDerivAt_const (c := gamma) (x := s)).mul ((hasDerivAt_id s).sub_const 1)) using 1 <;> ring
    have hpderiv : HasDerivAt (deriv p) (deriv (deriv p) s) s :=
      (hp.contDiffAt (Icc_mem_nhds hs.1 hs.2)).derivWithin (m := 1) (by norm_num) |>.differentiableAt
        (by norm_num) |>.hasDerivAt
    have hFderiv : deriv F s = Real.exp (gamma * (s - 1)) *
        (deriv (deriv p) s + gamma * deriv p s) := by
      convert (hexp.mul hpderiv).deriv using 1 <;> dsimp [F] <;> ring
    rw [hFderiv]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
    simpa [p, g, c] using scalar_distance_damped_frozen_energy_ineq hPhi sys
      (x := x) (a := 1) (t := t) (s := s) (by norm_num) (le_trans h1theta.le htheta)
      ⟨hs.1, le_trans (le_of_lt hs.2) htheta⟩
  have hFTC : F theta - F 1 = ∫ s in 1..theta, deriv F s := by
    simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hF h1theta.le).symm
  have hbound : F theta - F 1 ≤ ∫ s in 1..theta,
      Real.exp (gamma * (s - 1)) * g s := by
    rw [hFTC]
    exact intervalIntegral.integral_mono_on_of_le_Ioo h1theta.le hFint hgint hpoint
  have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt (Real.exp_pos (-gamma * (theta - 1))))
  rw [← intervalIntegral.integral_const_mul] at hmul
  have hcancel : Real.exp (-gamma * (theta - 1)) * Real.exp (gamma * (theta - 1)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hkernel : (∫ s in 1..theta, Real.exp (-gamma * (theta - 1)) *
      (Real.exp (gamma * (s - 1)) * g s)) =
      ∫ s in 1..theta, Real.exp (-gamma * (theta - s)) * g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  dsimp [F] at hmul
  rw [mul_sub, ← mul_assoc, hcancel] at hmul
  simp only [one_mul, Real.exp_zero] at hmul
  rw [hkernel] at hmul
  simpa [p, g, c, add_comm] using hmul

/-- The coefficient produced by the second integration grows without bound.
The nonnegative exponential term is deliberately retained as a lower-order
term; this avoids needing an exact antiderivative merely to identify its
asymptotic behaviour. -/
private theorem scalar_A_tendsto_atTop {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (fun t : ℝ =>
      (gamma * (t - 1) - 1 + Real.exp (-gamma * (t - 1))) / gamma ^ 2)
      atTop atTop := by
  let L : ℝ → ℝ := fun t => (1 / gamma) * t + (-(gamma + 1) / gamma ^ 2)
  have hL : Tendsto L atTop atTop := by
    have hmul : Tendsto (fun t : ℝ => (1 / gamma) * t) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (one_div_pos.mpr hgamma)).mpr tendsto_id
    simpa [L] using
      (tendsto_atTop_add_const_right atTop (-(gamma + 1) / gamma ^ 2) hmul)
  apply Filter.tendsto_atTop_mono _ hL
  intro t
  have hsq : 0 < gamma ^ 2 := sq_pos_of_pos hgamma
  have hexp : 0 ≤ Real.exp (-gamma * (t - 1)) := (Real.exp_pos _).le
  dsimp [L]
  have hrewrite : (1 / gamma) * t + (-(gamma + 1) / gamma ^ 2) =
      (gamma * (t - 1) - 1) / gamma ^ 2 := by
    field_simp [hgamma.ne']
    ring
  rw [hrewrite]
  exact (div_le_div_iff_of_pos_right hsq).mpr (by linarith)

/-- The coefficient of the frozen-energy comparison is nonnegative after the
initial time.  This is the elementary exponential convexity estimate needed
to replace energy by potential on the left of that comparison. -/
private theorem scalar_frozen_energy_coefficient_nonneg {gamma t : ℝ}
    (hgamma : 0 < gamma) (ht : 1 ≤ t) :
    0 ≤ (gamma * (t - 1) - 1 + Real.exp (-gamma * (t - 1))) / gamma ^ 2 := by
  have hr : 0 ≤ gamma * (t - 1) :=
    mul_nonneg (le_of_lt hgamma) (sub_nonneg.mpr ht)
  have hexp : 1 - gamma * (t - 1) ≤ Real.exp (-gamma * (t - 1)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Real.add_one_le_exp (-gamma * (t - 1)))
  apply div_nonneg
  · linarith
  · exact sq_nonneg gamma

set_option maxHeartbeats 5000000 in
/-- Theorem 2.1: a scalar-damped trajectory has the minimizing property and, when minimizers
exist, converges weakly to one of them. -/
theorem scalar_damped_minimizing_property {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) ∧
    Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) ∧
    Tendsto (fun t => Phi (sys.u t)) atTop (nhds (sInf (Set.range Phi))) ∧
    ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty →
      ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi),
      Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop (nhds (toWeakSpace ℝ H uhat))) := by
  have hvelIoi : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 0) :=
    scalar_velocity_sq_integrableOn_Ioi_zero hPhi sys
  have hvelIci : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hvelIoi
  obtain ⟨energyLimit, henergyLimit⟩ := scalar_energy_converges hPhi sys
  obtain ⟨errorLimit, herrorLimit⟩ :=
    scalar_causal_velocity_error_converges sys hvelIci
  let energy : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let error : ℝ → ℝ := fun t => (3 / 2 : ℝ) *
    ∫ theta in 1..t, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2
  have henergy : Tendsto energy atTop (nhds energyLimit) := by
    simpa [energy] using henergyLimit
  have herror : Tendsto error atTop (nhds errorLimit) := by
    simpa [error] using herrorLimit
  have henergyLower : ∀ t : ℝ, sInf (Set.range Phi) ≤ energy t := by
    intro t
    simpa [energy] using potential_sInf_le_scalar_energy hPhi sys t
  refine ⟨hvelIci, ?_⟩
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
  let p : H → ℝ → ℝ := fun x t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2
  let A : ℝ → ℝ := fun t =>
    (gamma * (t - 1) - 1 + Real.exp (-gamma * (t - 1))) / gamma ^ 2
  let B : ℝ → ℝ := fun t =>
    (1 - Real.exp (-gamma * (t - 1))) / gamma
  have hq_nonneg (t : ℝ) : 0 ≤ q t := sq_nonneg _
  have hpotential_le_energy (t : ℝ) : Phi (sys.u t) ≤ energy t := by
    dsimp [energy, q]
    nlinarith [sq_nonneg ‖fderiv ℝ sys.u t 1‖]
  have henergyLowerLimit : sInf (Set.range Phi) ≤ energyLimit := by
    exact ge_of_tendsto henergy (Filter.Eventually.of_forall henergyLower)
  have hA_pos : ∀ᶠ t in atTop, 0 < A t := by
    filter_upwards [eventually_ge_atTop (1 + 2 / gamma)] with t ht
    have hgamma : 0 < gamma := sys.gamma_pos
    have harg : 2 ≤ gamma * (t - 1) := by
      rw [mul_comm]
      apply (div_le_iff₀ hgamma).mp
      linarith
    have hexp : 0 < Real.exp (-gamma * (t - 1)) := Real.exp_pos _
    dsimp [A]
    apply div_pos
    · linarith
    · exact sq_pos_of_pos hgamma
  have hA_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ A t := by
    intro t ht
    simpa [A] using scalar_frozen_energy_coefficient_nonneg sys.gamma_pos ht
  -- The remaining comparison is the twice-integrated version of
  -- `scalar_distance_damped_frozen_energy_ineq`; its output will be divided
  -- by the eventually positive coefficient `A` above.
  have henergyEq : energyLimit = sInf (Set.range Phi) := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < energyLimit - sInf (Set.range Phi) := by
        have hle := henergyLowerLimit
        linarith
      let delta : ℝ := (energyLimit - sInf (Set.range Phi)) / 4
      have hdelta : 0 < delta := by dsimp [delta]; linarith
      rcases exists_lt_of_csInf_lt (b := sInf (Set.range Phi) + delta)
        (Set.range_nonempty Phi) (by
          linarith) with ⟨_, ⟨x, rfl⟩, hylt⟩
      have hcx : ∀ᶠ T in atTop,
          Phi x - energy T ≤ -(2 * delta) := by
        have hev := (tendsto_order.1 henergy).1 (sInf (Set.range Phi) + 3 * delta) (by
          dsimp [delta]
          linarith)
        filter_upwards [hev] with T hT
        have : Phi x ≤ sInf (Set.range Phi) + delta := hylt.le
        linarith
      have hinit : ∀ᶠ s in atTop,
          Real.exp (-gamma * (s - 1)) * deriv
            (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
              delta * Real.exp (-gamma) := by
        have he : Tendsto (fun s : ℝ => Real.exp (-gamma * (s - 1))) atTop
            (nhds 0) := by
          have harg : Tendsto (fun s : ℝ => -gamma * (s - 1)) atTop atBot := by
            have hlin : Tendsto (fun s : ℝ => -gamma * s) atTop atBot := by
              simpa [mul_comm] using
                (tendsto_id.atTop_mul_const_of_neg (neg_lt_zero.mpr sys.gamma_pos))
            simpa [sub_eq_add_neg, mul_add] using
              (Filter.tendsto_atBot_add_const_right atTop gamma hlin)
          exact (Real.tendsto_exp_atBot).comp harg
        have hmul := he.mul_const
          (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1)
        have htarget : 0 * deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 <
            delta * Real.exp (-gamma) := by
          simp
          positivity
        have hev := (tendsto_order.1 hmul).2 (delta * Real.exp (-gamma)) htarget
        filter_upwards [hev] with s hs
        linarith
      have hRint : IntegrableOn (fun theta : ℝ =>
          ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s)
          (Set.Ici 0) := by
        simpa [q] using scalar_causal_exp_convolution_integrable q gamma
          sys.gamma_pos hvelIci
      let R : ℝ → ℝ := fun theta : ℝ =>
        ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s
      have hRnonneg : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
          0 ≤ ∫ s in a..b, Real.exp (-gamma * (b - s)) * q s := by
        intro a b ha hab
        apply intervalIntegral.integral_nonneg hab
        intro s hs
        positivity
      have htail : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T in atTop, error T ≤ M := by
        refine ⟨|errorLimit| + 1, by positivity, ?_⟩
        have hev := herror.eventually (Metric.ball_mem_nhds errorLimit (ε := (1 : ℝ)) (by norm_num))
        filter_upwards [hev] with T hT
        have habs : |error T - errorLimit| < 1 := by
          simpa [Real.dist_eq, abs_sub_comm] using hT
        linarith [(abs_lt.mp habs).2, le_abs_self (errorLimit)]
      rcases htail with ⟨M, hMpos, hM⟩
      obtain ⟨a, ha_ge, ha_init, ha_energy, ha_err⟩ :=
        ((eventually_ge_atTop (2 : ℝ)).and (hinit.and (hcx.and hM))).exists
      have ha2 : (2 : ℝ) ≤ a := by
        exact le_trans (by norm_num) ha_ge
      have hTex : ∃ T : ℝ,
          ((a ≤ T ∧
            Real.exp (-gamma * (T - 1)) * deriv
              (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
                delta * Real.exp (-gamma) ∧
            Phi x - energy T ≤ -(2 * delta) ∧ error T ≤ M) ∧
            a + 1 < T) ∧
            a + 2 * (M + p x a + 1) / (delta * Real.exp (-gamma)) < T := by
        have hev := (eventually_ge_atTop a).and (hinit.and (hcx.and hM))
        have hev' := hev.and (eventually_gt_atTop (a + 1))
        have hev'' := hev'.and (eventually_gt_atTop
          (a + 2 * (M + p x a + 1) / (delta * Real.exp (-gamma))))
        simpa only [and_assoc] using hev''.exists
      rcases hTex with ⟨T, ⟨⟨hT_ge, hT_init, hT_energy, hT_err⟩, hTafter⟩, hTlarge⟩
      have hTa : a ≤ T := hT_ge
      have hTa_lt : a < T := lt_trans (by linarith) hTafter
      have hpoint : ∀ s ∈ Set.Ioo a T,
          deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) s ≤
            Real.exp (-gamma * (s - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
              (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R s := by
        intro s hs
        have hs1 : 1 ≤ s := le_trans (by linarith [ha2]) (le_of_lt hs.1)
        have hsT : s ≤ T := hs.2.le
        have hbase := scalar_frozen_energy_first_integral hPhi sys
          (x := x) (theta := s) (t := T) hs1 hsT
        have hkcont : ContinuousOn (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) (Set.Icc 0 s) := by
          exact (Real.continuous_exp.comp
            (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
        have hkint0 : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r)) * q r) volume 0 1 := by
          have hi0 := (hvelIci.mono_set (Set.Icc_subset_Ici_self)).mul_continuousOn
            hkcont isCompact_Icc
          have hi : IntegrableOn (fun r : ℝ => q r * Real.exp (-gamma * (s - r)))
              (Set.Icc 0 1) volume := hi0.mono_set (by
                intro r hr
                change 0 ≤ r ∧ r ≤ s
                exact ⟨hr.1, le_trans hr.2 hs1⟩)
          simpa [q, mul_comm] using
            ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hi)
        have hkint1 : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r)) * q r) volume 1 s := by
          have hi0 := (hvelIci.mono_set (Set.Icc_subset_Ici_self)).mul_continuousOn
            hkcont isCompact_Icc
          have hi : IntegrableOn (fun r : ℝ => q r * Real.exp (-gamma * (s - r)))
              (Set.Icc 1 s) volume := hi0.mono_set (by
                intro r hr
                change 0 ≤ r ∧ r ≤ s
                exact ⟨le_trans (by norm_num) hr.1, hr.2⟩)
          simpa [q, mul_comm] using
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hs1).mpr hi)
        have hkintseg : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume (s - 1) s := by
          apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hs1])
          exact hkcont.mono (by
            intro r hr
            change 0 ≤ r ∧ r ≤ s
            exact ⟨by linarith [hs1, hr.1], hr.2⟩)
        have hkintpre : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume 1 (s - 1) := by
          apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [ha2, hs.1])
          exact hkcont.mono (by
            intro r hr
            change 0 ≤ r ∧ r ≤ s
            exact ⟨by linarith [hr.1], le_trans hr.2 (by linarith [ha2, hs.1])⟩)
        have hkintall : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume 1 s :=
          by
            have hkcont1 : ContinuousOn (fun r : ℝ => Real.exp (-gamma * (s - r)))
                (Set.Icc 1 s) := hkcont.mono (by
              intro r hr
              change 0 ≤ r ∧ r ≤ s
              exact ⟨by linarith [hr.1], hr.2⟩)
            exact hkcont1.intervalIntegrable_of_Icc hs1
        have hseg := intervalIntegral.integral_mono_on (by linarith : s - 1 ≤ s)
          (intervalIntegrable_const : IntervalIntegrable
            (fun _ : ℝ => Real.exp (-gamma)) volume (s - 1) s) hkintseg (by
            intro r hr
            have hr0 : 0 ≤ s - r := by linarith [hr.2]
            have hr1 : s - r ≤ 1 := by linarith [hr.1]
            exact Real.exp_le_exp.mpr (by nlinarith [sys.gamma_pos, hr0, hr1]))
        rw [intervalIntegral.integral_const] at hseg
        have hadd := intervalIntegral.integral_add_adjacent_intervals hkintpre hkintseg
        have hpre : 0 ≤ ∫ r in 1..(s - 1), Real.exp (-gamma * (s - r)) :=
          intervalIntegral.integral_nonneg (by linarith [ha2, hs.1])
            (by intro r hr; exact (Real.exp_pos _).le)
        have hK : Real.exp (-gamma) ≤ ∫ r in 1..s,
            Real.exp (-gamma * (s - r)) := by
          have hseg' : Real.exp (-gamma) ≤ ∫ r in (s - 1)..s,
              Real.exp (-gamma * (s - r)) := by
            simpa [smul_eq_mul] using hseg
          linarith
        have hqadd := intervalIntegral.integral_add_adjacent_intervals hkint0 hkint1
        have hqpre : 0 ≤ ∫ r in 0..1,
            Real.exp (-gamma * (s - r)) * q r :=
          intervalIntegral.integral_nonneg (by norm_num)
            (by intro r hr; positivity)
        have hqle : (∫ r in 1..s, Real.exp (-gamma * (s - r)) * q r) ≤ R s := by
          dsimp [R]
          linarith
        have hsplit : (∫ r in 1..s, Real.exp (-gamma * (s - r)) *
            (Phi x - energy T + (3 / 2 : ℝ) * q r)) =
            (Phi x - energy T) * (∫ r in 1..s, Real.exp (-gamma * (s - r))) +
              (3 / 2 : ℝ) * (∫ r in 1..s, Real.exp (-gamma * (s - r)) * q r) := by
          rw [show (fun r : ℝ => Real.exp (-gamma * (s - r)) *
              (Phi x - energy T + (3 / 2 : ℝ) * q r)) =
              (fun r => (Phi x - energy T) * Real.exp (-gamma * (s - r)) +
                (3 / 2 : ℝ) * (Real.exp (-gamma * (s - r)) * q r)) by
              funext r; ring]
          rw [intervalIntegral.integral_add
            ((intervalIntegrable_const : IntervalIntegrable
              (fun _ : ℝ => Phi x - energy T) volume 1 s).mul_continuousOn
                (by
                  simpa [Set.uIcc_of_le hs1] using
                    (hkcont.mono (by
                      intro r hr
                      change 0 ≤ r ∧ r ≤ s
                      exact ⟨by linarith [hr.1], hr.2⟩))))
            (hkint1.const_mul (3 / 2 : ℝ)),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hc : Phi x - energy T ≤ -(2 * delta) := hT_energy
        have hck := mul_le_mul_of_nonpos_left hK (by linarith : Phi x - energy T ≤ 0)
        rw [hsplit] at hbase
        have hqscaled := mul_le_mul_of_nonneg_left hqle
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        have hsum := add_le_add hck hqscaled
        have hconst := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-gamma)).le
        linarith
      have hpcont : ContDiffOn ℝ 2 (fun r : ℝ =>
          (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) (Set.Icc a T) := by
        have hu : ContDiffOn ℝ 2 sys.u (Set.Icc a T) :=
          sys.contDiff.mono (fun r hr => le_trans (by linarith [ha2]) hr.1)
        exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
      have hpint : IntervalIntegrable (deriv (fun r : ℝ =>
          (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2)) volume a T := by
        have hd := (hpcont.derivWithin (m := 0) (uniqueDiffOn_Icc hTa_lt) (by norm_num)).continuousOn
        apply (hd.intervalIntegrable_of_Icc hTa).congr_ae
        simp only [Set.uIoc_of_le hTa]
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
      have hRintAT : IntervalIntegrable R volume a T := by
        apply (intervalIntegrable_iff_integrableOn_Icc_of_le hTa).mpr
        exact hRint.mono_set (by
          intro r hr
          change 0 ≤ r
          linarith [ha_ge, hr.1])
      have hmajint : IntervalIntegrable (fun s : ℝ =>
          Real.exp (-gamma * (s - 1)) *
            deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
          (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R s) volume a T := by
        apply IntervalIntegrable.add
        · have hexpcont : ContinuousOn (fun s : ℝ => Real.exp (-gamma * (s - 1)))
              (Set.Icc a T) :=
            (Real.continuous_exp.comp (continuous_const.mul
              (continuous_id.sub continuous_const))).continuousOn
          have hexpint : IntervalIntegrable (fun s : ℝ => Real.exp (-gamma * (s - 1)))
              volume a T := hexpcont.intervalIntegrable_of_Icc hTa
          have hfirst : IntervalIntegrable (fun s : ℝ =>
              Real.exp (-gamma * (s - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T :=
            hexpint.mul_continuousOn
              (continuousOn_const : ContinuousOn (fun _ : ℝ =>
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
          exact hfirst.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ =>
              (-(2 * delta)) * Real.exp (-gamma)) volume a T)
        · exact hRintAT.const_mul (3 / 2 : ℝ)
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hTa hpint hmajint hpoint
      have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc (hpcont.of_le (by norm_num)) hTa
      have hmono' := hmono
      rw [hFTC] at hmono'
      have hRle : (∫ s in a..T, R s) ≤ ∫ s in 1..T, R s := by
        have hRint1 : IntervalIntegrable R volume 1 a := by
          have h1a : (1 : ℝ) ≤ a := by linarith [ha2]
          apply (intervalIntegrable_iff_integrableOn_Icc_of_le h1a).mpr
          exact hRint.mono_set (by
            intro r hr
            change 0 ≤ r
            exact le_trans (by norm_num) hr.1)
        have haddR := intervalIntegral.integral_add_adjacent_intervals hRint1 hRintAT
        have hR01 : 0 ≤ ∫ s in 1..a, R s := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro s hs
          exact hRnonneg (a := 0) (b := s) (by norm_num) (by linarith [hs.1, ha2])
        linarith
      have hbound : (3 / 2 : ℝ) * (∫ s in 1..T, R s) ≤ M := by
        simpa [error, R, q] using hT_err
      have hlen : 0 ≤ T - a := by linarith
      have hinitInt :
          ∫ u in a..T,
            Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1
            ≤ delta * Real.exp (-gamma) * (T - a) := by
        have hexpcont : ContinuousOn (fun u : ℝ => Real.exp (-gamma * (u - 1)))
            (Set.Icc a T) :=
          (Real.continuous_exp.comp (continuous_const.mul
            (continuous_id.sub continuous_const))).continuousOn
        have hexpint : IntervalIntegrable
            (fun u : ℝ => Real.exp (-gamma * (u - 1))) volume a T :=
          hexpcont.intervalIntegrable_of_Icc hTa
        have hDint : IntervalIntegrable
            (fun u : ℝ => Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T :=
          hexpint.mul_continuousOn
            (continuousOn_const : ContinuousOn (fun _ : ℝ =>
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
        have hpointInit : ∀ u ∈ Set.Ioo a T,
            Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
              delta * Real.exp (-gamma) := by
          intro u hu
          by_cases hD : deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤ 0
          · have hleft : Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hD
            have hright : 0 ≤ delta * Real.exp (-gamma) :=
              (mul_pos hdelta (Real.exp_pos _)).le
            linarith
          · have hDpos : 0 < deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 :=
              lt_of_not_ge hD
            have hexple : Real.exp (-gamma * (u - 1)) ≤
                Real.exp (-gamma * (a - 1)) := by
              apply Real.exp_le_exp.mpr
              nlinarith [sys.gamma_pos, hu.1.le]
            have hmul := mul_le_mul_of_nonneg_right hexple hDpos.le
            have ha' := ha_init
            have hinit_le := mul_le_mul_of_nonneg_right ha' (by positivity : (0 : ℝ) ≤ 1)
            nlinarith
        have hinitInt0 :=
          intervalIntegral.integral_mono_on_of_le_Ioo
            hTa hDint
            (intervalIntegrable_const :
              IntervalIntegrable (fun _ : ℝ => delta * Real.exp (-gamma)) volume a T)
            hpointInit
        rw [intervalIntegral.integral_const] at hinitInt0
        simpa [smul_eq_mul, mul_comm] using hinitInt0
      have hneg : delta * Real.exp (-gamma) / 2 * (T - a) >
          p x a + M + 1 := by
        have hTlarge' := hTlarge
        have hexp : 0 < Real.exp (-gamma) := Real.exp_pos _
        dsimp [p] at hTlarge'
        have hden : 0 < delta * Real.exp (-gamma) := mul_pos hdelta hexp
        have hratio : 2 * (M + p x a + 1) / (delta * Real.exp (-gamma)) < T - a := by
          linarith [hTlarge']
        have hprod := (div_lt_iff₀ hden).mp hratio
        nlinarith [hprod]
      have hpa : 0 ≤ (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 := by positivity
      have hpt : 0 ≤ (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 := by positivity
      have hsplitRhs :
          (∫ u in a..T,
            (Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
              (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R u)) =
            (∫ u in a..T,
              Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) +
              (-(2 * delta)) * Real.exp (-gamma) * (T - a) +
              (3 / 2 : ℝ) * (∫ u in a..T, R u) := by
        have hfirstInt : IntervalIntegrable (fun u : ℝ =>
            Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T := by
          have hexpcont : ContinuousOn (fun u : ℝ => Real.exp (-gamma * (u - 1)))
              (Set.Icc a T) :=
            (Real.continuous_exp.comp (continuous_const.mul
              (continuous_id.sub continuous_const))).continuousOn
          have hexpint : IntervalIntegrable
              (fun u : ℝ => Real.exp (-gamma * (u - 1))) volume a T :=
            hexpcont.intervalIntegrable_of_Icc hTa
          exact hexpint.mul_continuousOn
            (continuousOn_const : ContinuousOn (fun _ : ℝ =>
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
        have hconstInt : IntervalIntegrable (fun _ : ℝ =>
            (-(2 * delta)) * Real.exp (-gamma)) volume a T :=
          intervalIntegrable_const
        have hRscaled : IntervalIntegrable (fun u : ℝ => (3 / 2 : ℝ) * R u) volume a T :=
          hRintAT.const_mul (3 / 2 : ℝ)
        rw [intervalIntegral.integral_add (hfirstInt.add hconstInt) hRscaled,
          intervalIntegral.integral_add hfirstInt hconstInt,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        ring
      rw [hsplitRhs] at hmono'
      have hRscaled : (3 / 2 : ℝ) * (∫ s in a..T, R s) ≤
          (3 / 2 : ℝ) * (∫ s in 1..T, R s) :=
        mul_le_mul_of_nonneg_left hRle (by norm_num)
      dsimp [p] at hneg
      have hstep :
          (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 ≤
            -(delta * Real.exp (-gamma)) * (T - a) + M := by
        nlinarith [hmono', hinitInt, hRscaled, hbound]
      have hneg2 : delta * Real.exp (-gamma) * (T - a) >
          2 * ((1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 + M + 1) := by
        nlinarith [hneg]
      have hpt_bound : (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 -
            delta * Real.exp (-gamma) * (T - a) + M := by
        linarith [hstep]
      have hneg3 : (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 -
          delta * Real.exp (-gamma) * (T - a) + M < 0 := by
        have hneg2' := hneg2
        ring_nf at hneg2' ⊢
        nlinarith [hneg2', hMpos, sq_nonneg ‖sys.u a - x‖]
      linarith [hpt_bound, hneg3, hpt]
    · exact henergyLowerLimit
  have hpotential : Tendsto (fun t => Phi (sys.u t)) atTop
      (nhds (sInf (Set.range Phi))) := by
    have henergy' : Tendsto energy atTop (nhds (sInf (Set.range Phi))) := by
      simpa [henergyEq] using henergy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => sInf (Set.range Phi)) atTop
        (nhds (sInf (Set.range Phi)))) henergy'
    · intro t
      exact potential_sInf_le hPhi (sys.u t)
    · intro t
      exact hpotential_le_energy t
  have hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) := by
    apply scalar_velocity_tendsto_zero_of_energy_potential_tendsto sys henergy
    simpa [henergyEq] using hpotential
  have hargmin : ∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
      ∃ l : ℝ, Tendsto (fun t => ‖sys.u t - z‖) atTop (nhds l) := by
    intro z hz
    exact scalar_distance_to_minimizer_converges hPhi sys hvelIci z hz
  refine ⟨hvel0, hpotential, ?_⟩
  intro hne
  have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (sys.u (u n))) atTop
        (nhds (f z))) → z ∈ argmin Phi (potential_range_bddBelow hPhi) := by
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
      obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
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
    simpa [argmin] using hzmin
  obtain ⟨uhat, hUhat, hUweak⟩ := opial_lemma_continuous_weak sys.u
    (argmin Phi (potential_range_bddBelow hPhi)) hne hargmin hcluster
  refine ⟨uhat, hUhat, ?_⟩
  apply (weakConvergence_iff_forall_tendsto_inner_right sys.u uhat).2
  intro y
  let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) y
  have hf := hUweak f
  dsimp [f] at hf
  simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf

end Alvarez2000
