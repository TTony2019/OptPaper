import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.thm_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_6
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_thm_2

namespace Alvarez2000

open Filter
open MeasureTheory
open scoped InnerProductSpace Topology

/-- An interior point of the minimizer set contains a positive closed minimizer ball. -/
private theorem interior_argmin_closedBall {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Phi : H → ℝ} (hPhi : HasPotentialAssumption Phi)
    (hInterior : (interior (argmin Phi (potential_range_bddBelow hPhi))).Nonempty) :
    ∃ z0 : H, ∃ rho : ℝ, 0 < rho ∧
      Metric.closedBall z0 rho ⊆ argmin Phi (potential_range_bddBelow hPhi) := by
  rcases hInterior with ⟨z0, hz0⟩
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz0) with ⟨r, hr, hball⟩
  refine ⟨z0, r / 2, half_pos hr, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hball

/-- A differentiable gradient representative vanishes at every global minimizer. -/
private theorem gradient_eq_zero_of_mem_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Phi : H → ℝ} {gradPhi : H → H}
    (hPhi : HasPotentialAssumption Phi) (hGrad : ∀ x, HasGradientAt Phi (gradPhi x) x)
    {z : H} (hz : z ∈ argmin Phi (potential_range_bddBelow hPhi)) : gradPhi z = 0 := by
  have hmin : IsMinOn Phi Set.univ z := by
    intro y hy
    rw [show Phi z = sInf (Set.range Phi) from hz]
    exact potential_sInf_le hPhi y
  have hfderiv : fderiv ℝ Phi z = 0 :=
    (hmin.isLocalMin (by simp : Set.univ ∈ nhds z)).fderiv_eq_zero
  have hinner : ⟪gradPhi z, gradPhi z⟫_ℝ = 0 := by
    rw [← (hGrad z).fderiv_apply, hfderiv]
    simp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa only [real_inner_self_eq_norm_sq] using hinner))

/-- A minimizer ball gives a radial lower bound for the gradient. -/
private theorem gradient_radial_lower_bound_of_argmin_closedBall {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Phi : H → ℝ} {gradPhi : H → H} (hPhi : HasPotentialAssumption Phi)
    (hGrad : ∀ x, HasGradientAt Phi (gradPhi x) x) {z0 : H} {rho : ℝ}
    (hrho : 0 < rho)
    (hball : Metric.closedBall z0 rho ⊆ argmin Phi (potential_range_bddBelow hPhi))
    (x : H) : rho * ‖gradPhi x‖ ≤ ⟪gradPhi x, x - z0⟫_ℝ := by
  by_cases hg : gradPhi x = 0
  · rw [hg]
    simp
  · let g : H := gradPhi x
    let z : H := z0 + (rho / ‖g‖) • g
    have hgnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa [g] using hg)
    have hzsub : z - z0 = (rho / ‖g‖) • g := by
      dsimp [z]
      module
    have hznorm : ‖z - z0‖ = rho := by
      rw [hzsub, norm_smul,
        Real.norm_of_nonneg (div_nonneg (le_of_lt hrho) (norm_nonneg _))]
      field_simp
    have hzball : z ∈ Metric.closedBall z0 rho := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm, norm_sub_rev] using hznorm.le
    have hzmin : z ∈ argmin Phi (potential_range_bddBelow hPhi) := hball hzball
    have hzle : Phi z ≤ Phi x := by
      rw [show Phi z = sInf (Set.range Phi) from hzmin]
      exact potential_sInf_le hPhi x
    have hsupport := Alvarez2000.scalar_convex_gradient_support hPhi.convex hGrad x z
    have hnonneg : 0 ≤ ⟪g, x - z⟫_ℝ := by
      have hsign : ⟪gradPhi x, z - x⟫_ℝ = -⟪gradPhi x, x - z⟫_ℝ := by
        rw [show z - x = -(x - z) by module, inner_neg_right]
      rw [hsign] at hsupport
      dsimp [g]
      linarith
    have hxz : x - z = (x - z0) - (rho / ‖g‖) • g := by
      dsimp [z]
      module
    rw [hxz, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hnonneg
    have hscale : (rho / ‖g‖) * ‖g‖ ^ 2 = rho * ‖g‖ := by
      field_simp
    rw [hscale] at hnonneg
    simpa [g] using hnonneg

/-- The squared distance to a fixed point has the expected first derivative. -/
private theorem scalar_damped_distance_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 z0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)
      ⟪sys.u t - z0, fderiv ℝ sys.u t 1⟫_ℝ t := by
  have hu : HasDerivAt (fun s => sys.u s - z0) (fderiv ℝ sys.u t 1) t := by
    simpa using ((dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt.sub_const z0)
  convert (hasDerivAt_const t (1 / 2 : ℝ)).mul hu.norm_sq using 1
  all_goals ring

/-- The squared distance to an arbitrary point satisfies the damped differential
inequality used for the interior-minimizer case. -/
private theorem scalar_distance_damped_ineq_local {H : Type*} [NormedAddCommGroup H]
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
    convert hsq using 1
    all_goals simp [real_inner_comm]
  have hfirst : ∀ᶠ s in nhds t,
      deriv phi s = ⟪v s, sys.u s - x⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hus : HasDerivAt sys.u (v s) s := by
      simpa only [v] using (dissipativeSystem_differentiableAt_pos sys hs).hasDerivAt
    have hsubs : HasDerivAt (fun r => sys.u r - x) (v s) s := by
      simpa only using hus.sub_const x
    have hsqs := (hasDerivAt_const s (1 / 2 : ℝ)).mul hsubs.norm_sq
    have : HasDerivAt phi ⟪v s, sys.u s - x⟫_ℝ s := by
      convert hsqs using 1
      all_goals simp [real_inner_comm]
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
  simp only [inner_zero_left] at hinnerEq
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

/-- The minimizer-ball estimate controls the damped acceleration through the
squared distance to the centre of the ball. -/
private theorem radial_distance_acceleration_ineq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 z0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {rho : ℝ}
    (hradial : ∀ x : H, rho * ‖gradPhi x‖ ≤ ⟪gradPhi x, x - z0⟫_ℝ)
    {t : ℝ} (ht : 0 < t) :
    rho * ‖fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 +
        gamma • fderiv ℝ sys.u t 1‖ ≤
      - deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
        ‖fderiv ℝ sys.u t 1‖ ^ 2 -
          gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t := by
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : H := fderiv ℝ v t 1
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2
  have hu : HasDerivAt sys.u (v t) t := by
    simpa only [v] using (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
  have hv : HasDerivAt v a t := by
    simpa only [v, a] using dissipativeSystem_velocity_hasDerivAt_pos sys ht
  have hphi : HasDerivAt phi ⟪v t, sys.u t - z0⟫_ℝ t := by
    have hsub : HasDerivAt (fun s => sys.u s - z0) (v t) t := by
      simpa only using hu.sub_const z0
    convert (hasDerivAt_const t (1 / 2 : ℝ)).mul hsub.norm_sq using 1
    all_goals simp [real_inner_comm]
  have hfirst : ∀ᶠ s in nhds t,
      deriv phi s = ⟪v s, sys.u s - z0⟫_ℝ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hus : HasDerivAt sys.u (v s) s := by
      simpa only [v] using (dissipativeSystem_differentiableAt_pos sys hs).hasDerivAt
    have hsub : HasDerivAt (fun r => sys.u r - z0) (v s) s := by
      simpa only using hus.sub_const z0
    have hsquare := (hasDerivAt_const s (1 / 2 : ℝ)).mul hsub.norm_sq
    have h : HasDerivAt phi ⟪v s, sys.u s - z0⟫_ℝ s := by
      convert hsquare using 1
      all_goals simp [real_inner_comm]
    exact h.deriv
  have hinner : HasDerivAt (fun s => ⟪v s, sys.u s - z0⟫_ℝ)
      (⟪a, sys.u t - z0⟫_ℝ + ⟪v t, v t⟫_ℝ) t := by
    simpa only [add_comm] using hv.inner ℝ (hu.sub_const z0)
  have hsecond : deriv (deriv phi) t =
      ⟪a, sys.u t - z0⟫_ℝ + ‖v t‖ ^ 2 := by
    rw [show deriv (deriv phi) t = deriv (fun s => ⟪v s, sys.u s - z0⟫_ℝ) t by
      exact Filter.EventuallyEq.deriv_eq hfirst]
    simpa only [real_inner_self_eq_norm_sq] using hinner.deriv
  have heq := sys.equation t (le_of_lt ht)
  have hrad := hradial (sys.u t)
  have hgrad : gradPhi (sys.u t) = -(a + gamma • v t) := by
    simpa only [v, a] using eq_neg_of_add_eq_zero_right heq
  change rho * ‖a + gamma • v t‖ ≤
    -deriv (deriv phi) t + ‖v t‖ ^ 2 - gamma * deriv phi t
  rw [hsecond, hphi.deriv]
  rw [hgrad] at hrad
  simp only [norm_neg] at hrad
  calc
    rho * ‖a + gamma • v t‖ ≤ ⟪-(a + gamma • v t), sys.u t - z0⟫_ℝ := hrad
    _ = -⟪a, sys.u t - z0⟫_ℝ - gamma * ⟪v t, sys.u t - z0⟫_ℝ := by
      rw [inner_neg_left, inner_add_left, real_inner_smul_left]
      ring
    _ = -(⟪a, sys.u t - z0⟫_ℝ + ‖v t‖ ^ 2) + ‖v t‖ ^ 2 -
        gamma * ⟪v t, sys.u t - z0⟫_ℝ := by ring

/-- The shifted squared distance has a finite limit.  The translation by one
keeps all derivative calculations in the open positive-time domain. -/
private theorem shifted_distance_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 z0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel2 : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0))
    (hdistance : ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
        gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t ≤
          ‖fderiv ℝ sys.u t 1‖ ^ 2) :
    ∃ L : ℝ, Tendsto (fun s => (1 / 2 : ℝ) * ‖sys.u (s + 1) - z0‖ ^ 2)
      atTop (nhds L) := by
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2
  let phiTail : ℝ → ℝ := fun s => phi (s + 1)
  have hphi : ContDiffOn ℝ 2 phi (Set.Ioi 0) := by
    have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
      sys.contDiff.mono Set.Ioi_subset_Ici_self
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hphiTail : ContDiffOn ℝ 2 phiTail (Set.Ici 0) := by
    have hu : ContDiffOn ℝ 2 (fun s : ℝ => sys.u (s + 1)) (Set.Ici 0) := by
      exact sys.contDiff.comp ((contDiff_id.add contDiff_const).contDiffOn)
        (fun s hs => by
          change 0 ≤ s at hs
          exact add_nonneg hs (by norm_num))
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have htail_deriv : ∀ s : ℝ, -1 < s →
      deriv phiTail s = deriv phi (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by
      linarith
    have hphiDiff : DifferentiableAt ℝ phi (s + 1) :=
      (hphi.contDiffAt (Ioi_mem_nhds hspos)).differentiableAt (by norm_num)
    change deriv (phi ∘ fun r : ℝ => r + 1) s = deriv phi (s + 1)
    convert deriv_comp s hphiDiff (differentiableAt_id.add_const 1) using 1
    all_goals simp
  have htail_second : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv phiTail) s = deriv (deriv phi) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by
      change 0 ≤ s at hs
      linarith
    have hderivDiff : DifferentiableAt ℝ (deriv phi) (s + 1) := by
      have hcd := hphi.contDiffAt (Ioi_mem_nhds hspos)
      exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hevent : deriv phiTail =ᶠ[nhds s] fun r => deriv phi (r + 1) := by
      filter_upwards [Ioi_mem_nhds (by linarith : -1 < s)] with r hr
      exact htail_deriv r hr
    rw [Filter.EventuallyEq.deriv_eq hevent]
    convert deriv_comp s hderivDiff (differentiableAt_id.add_const 1) using 1
    all_goals simp
  have hforce : IntegrableOn (fun s : ℝ => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) (Set.Ici 0) := by
    have heq := (measurePreserving_add_right volume (1 : ℝ)).integrableOn_comp_preimage
      (Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding
        (f := fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) (s := Set.Ici 0)
    rw [Set.preimage_add_const_Ici] at heq
    have hfull : IntegrableOn ((fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) ∘
        fun s : ℝ => s + 1) (Set.Ici (0 - 1)) := heq.mpr hvel2
    exact hfull.mono_set (Set.Ici_subset_Ici.mpr (by norm_num : (0 - 1 : ℝ) ≤ 0))
  have hineq : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv phiTail) s + gamma * deriv phiTail s ≤
        ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    rw [htail_second s hs, htail_deriv s (by
      change 0 ≤ s at hs
      linarith)]
    exact hdistance (by
      change 0 ≤ s at hs
      linarith)
  have hpositive : IntegrableOn (fun s => max (deriv phiTail s) 0) (Set.Ici 0) :=
    positive_part_integrable_of_damped_inequality (fun s => deriv phiTail s)
      (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) gamma
      (by
        have hwithin : ContDiffOn ℝ 1 (derivWithin phiTail (Set.Ici 0)) (Set.Ici 0) :=
          hphiTail.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
        exact hwithin.congr fun s hs => by
          have hspos : 0 < s + 1 := by
            change 0 ≤ s at hs
            linarith
          have hdiff : DifferentiableAt ℝ phiTail s := by
            rw [show phiTail = phi ∘ fun r : ℝ => r + 1 by rfl]
            exact ((hphi.contDiffAt (Ioi_mem_nhds hspos)).differentiableAt
              (by norm_num)).comp s (differentiableAt_id.add_const 1)
          rw [deriv, derivWithin,
            fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) s hs)
              hdiff])
      sys.gamma_pos hineq hforce
  apply converges_of_integrable_positive_derivative phiTail
    (hphiTail.of_le (by norm_num))
  · refine ⟨0, ?_⟩
    intro s hs
    dsimp [phiTail, phi]
    positivity
  · exact hpositive

/-- Integrating the radial estimate on a compact positive-time interval. -/
private theorem radial_acceleration_interval_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 z0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0) {rho T : ℝ}
    (haccel : ∀ ⦃t : ℝ⦄, 0 < t →
      rho * ‖fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 + gamma • fderiv ℝ sys.u t 1‖ ≤
        -deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
          ‖fderiv ℝ sys.u t 1‖ ^ 2 -
            gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t)
    (hT : 1 ≤ T) :
    rho * (∫ t in 1..T,
      ‖fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 + gamma • fderiv ℝ sys.u t 1‖) ≤
      deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) 1 -
        deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) T +
          (∫ t in 1..T, ‖fderiv ℝ sys.u t 1‖ ^ 2) +
            gamma * ((1 / 2 : ℝ) * ‖sys.u 1 - z0‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u T - z0‖ ^ 2) := by
  rcases hT.eq_or_lt with rfl | hT
  · simp
  let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2
  let v : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let a : ℝ → H := fun s => fderiv ℝ v s 1
  let q : ℝ → ℝ := fun s => ‖a s + gamma • v s‖
  have hu : ContDiffOn ℝ 2 sys.u (Set.Icc 1 T) :=
    sys.contDiff.mono (fun s hs => le_trans (by norm_num) hs.1)
  have hv : ContDiffOn ℝ 1 v (Set.Icc 1 T) := by
    intro s hs
    have hlocal := sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
    exact ((hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
  have hphi : ContDiffOn ℝ 2 phi (Set.Icc 1 T) :=
    contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
  have hphi' : ContDiffOn ℝ 1 (deriv phi) (Set.Icc 1 T) := by
    apply (hv.inner ℝ ((hu.sub contDiffOn_const).of_le (by norm_num))).congr
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
    simpa only [phi, real_inner_comm] using
      (scalar_damped_distance_hasDerivAt (z0 := z0) sys hspos).deriv
  have ha : ContinuousOn a (Set.Icc 1 T) := by
    intro s hs
    have hlocal := sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
    have hvlocal := (hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))
    simpa only [a] using
      ((hvlocal.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).clm_apply
        (contDiffAt_const (c := (1 : ℝ)))).continuousAt.continuousWithinAt
  have hq : ContinuousOn q (Set.Icc 1 T) :=
    ((ha.add (continuousOn_const.smul hv.continuousOn)).norm)
  have hleft : IntervalIntegrable (fun s => rho * q s) volume 1 T :=
    (continuousOn_const.mul hq).intervalIntegrable_of_Icc hT.le
  have hsecondInt : IntervalIntegrable (deriv (deriv phi)) volume 1 T := by
    have hcont := (hphi'.derivWithin (m := 0) (uniqueDiffOn_Icc hT) (by norm_num)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hT.le).congr_ae
    simp only [hT.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  have hvelsq : IntervalIntegrable (fun s => ‖v s‖ ^ 2) volume 1 T :=
    (hv.continuousOn.norm.pow 2).intervalIntegrable_of_Icc hT.le
  have hgamphi : IntervalIntegrable (fun s => gamma * deriv phi s) volume 1 T :=
    (continuousOn_const.mul hphi'.continuousOn).intervalIntegrable_of_Icc hT.le
  have hright : IntervalIntegrable
      (fun s => -deriv (deriv phi) s + ‖v s‖ ^ 2 - gamma * deriv phi s) volume 1 T := by
    exact (hsecondInt.neg.add hvelsq).sub hgamphi
  have hmono : (∫ s in 1..T, rho * q s) ≤
      ∫ s in 1..T, -deriv (deriv phi) s + ‖v s‖ ^ 2 - gamma * deriv phi s := by
    apply intervalIntegral.integral_mono_on hT.le hleft hright
    intro s hs
    simpa only [phi, v, a, q] using haccel (lt_of_lt_of_le (by norm_num) hs.1)
  have hFTC1 : ∫ s in 1..T, deriv (deriv phi) s = deriv phi T - deriv phi 1 := by
    simpa using intervalIntegral.integral_deriv_of_contDiffOn_Icc hphi' hT.le
  have hFTC2 : ∫ s in 1..T, deriv phi s = phi T - phi 1 := by
    simpa using intervalIntegral.integral_deriv_of_contDiffOn_Icc (hphi.of_le (by norm_num)) hT.le
  have hRHS : (∫ s in 1..T,
      -deriv (deriv phi) s + ‖v s‖ ^ 2 - gamma * deriv phi s) =
      deriv phi 1 - deriv phi T + (∫ s in 1..T, ‖v s‖ ^ 2) +
        gamma * (phi 1 - phi T) := by
    change (∫ s in 1..T,
      ((-deriv (deriv phi)) s + (fun r => ‖v r‖ ^ 2) s) -
        (fun r => gamma * deriv phi r) s) = _
    have hneg : (∫ s in 1..T, (-deriv (deriv phi)) s) =
        -(deriv phi T - deriv phi 1) := by
      change (∫ s in 1..T, -(deriv (deriv phi) s)) = _
      rw [intervalIntegral.integral_neg, hFTC1]
    have hgamma : (∫ s in 1..T, gamma * deriv phi s) = gamma * (phi T - phi 1) := by
      rw [intervalIntegral.integral_const_mul, hFTC2]
    rw [intervalIntegral.integral_sub (hsecondInt.neg.add hvelsq) hgamphi,
      intervalIntegral.integral_add hsecondInt.neg hvelsq, hneg, hgamma]
    ring
  rw [intervalIntegral.integral_const_mul, hRHS] at hmono
  change rho * (∫ s in 1..T, q s) ≤ _
  dsimp [q, v, a, phi] at hmono ⊢
  linarith

/-- Theorem 2.4: even potentials or minimizer sets with nonempty interior give strong convergence. -/
theorem scalar_damped_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hcase : ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty ∧ IsEvenFunction Phi) ∨
      (interior (argmin Phi (potential_range_bddBelow hPhi))).Nonempty) :
    ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi), Tendsto sys.u atTop (nhds uhat) := by
  rcases hcase with hEven | hInterior
  · rcases hEven with ⟨hMin, hPhiEven⟩
    simpa only [proof_irrel_heq] using
      (scalar_damped_even_strong_convergence_result hPhi.contDiff hPhi.convex hPhi.bounded_below
        sys hMin hPhiEven)
  · obtain ⟨z0, rho, hrho, hball⟩ := interior_argmin_closedBall hPhi hInterior
    have hradial : ∀ x : H, rho * ‖gradPhi x‖ ≤ ⟪gradPhi x, x - z0⟫_ℝ :=
      fun x => gradient_radial_lower_bound_of_argmin_closedBall hPhi sys.is_gradient hrho hball x
    obtain ⟨hvel2, hvel0, hPhi0, hweak⟩ := scalar_damped_minimizing_property hPhi sys
    have hz0min : z0 ∈ argmin Phi (potential_range_bddBelow hPhi) :=
      hball (Metric.mem_closedBall_self (le_of_lt hrho))
    have hz0value : Phi z0 = sInf (Set.range Phi) := hz0min
    have hdistance_ineq : ∀ ⦃t : ℝ⦄, 0 < t →
        deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
            gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t ≤
          ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      intro t ht
      have h := scalar_distance_damped_ineq_local hPhi sys z0 ht
      have hgap : Phi z0 - Phi (sys.u t) ≤ 0 := by
        rw [hz0value]
        linarith [potential_sInf_le hPhi (sys.u t)]
      linarith
    have hphiLimit : ∃ L : ℝ, Tendsto
        (fun s => (1 / 2 : ℝ) * ‖sys.u (s + 1) - z0‖ ^ 2) atTop (nhds L) :=
      shifted_distance_converges sys hvel2 hdistance_ineq
    have haccelIneq : ∀ ⦃t : ℝ⦄, 0 < t →
        rho * ‖fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 +
            gamma • fderiv ℝ sys.u t 1‖ ≤
          -deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
            ‖fderiv ℝ sys.u t 1‖ ^ 2 -
              gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t :=
      fun _ ht => radial_distance_acceleration_ineq sys hradial ht
    let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2
    rcases hphiLimit with ⟨L, hphiTail⟩
    have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
    have hphi : Tendsto phi atTop (nhds L) := by
      convert hphiTail.comp hshift using 1
      ext t
      simp [phi]
    have hdist : Tendsto (fun t => ‖sys.u t - z0‖) atTop
        (nhds (Real.sqrt (2 * L))) := by
      have htwo : Tendsto (fun t => 2 * phi t) atTop (nhds (2 * L)) :=
        tendsto_const_nhds.mul hphi
      have hsqrt := (Real.continuous_sqrt.tendsto (2 * L)).comp htwo
      convert hsqrt using 1
      ext t
      simp only [Function.comp_apply, phi]
      rw [show 2 * (1 / 2 * ‖sys.u t - z0‖ ^ 2) = ‖sys.u t - z0‖ ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hderiv0 : Tendsto (fun t => deriv phi t) atTop (nhds 0) := by
      have hprod : Tendsto (fun t => ‖sys.u t - z0‖ * ‖fderiv ℝ sys.u t 1‖)
          atTop (nhds 0) := by
        simpa using hdist.mul hvel0.norm
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_ hprod
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
      rw [show deriv phi t = ⟪sys.u t - z0, fderiv ℝ sys.u t 1⟫_ℝ by
        simpa only [phi] using (scalar_damped_distance_hasDerivAt (z0 := z0) sys ht).deriv]
      exact abs_real_inner_le_norm _ _
    let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
    let r : ℝ → H := fun t => fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 +
      gamma • fderiv ℝ sys.u t 1
    let V : ℝ := ∫ t in Set.Ici 0, q t
    have hq_nonneg : ∀ t : ℝ, 0 ≤ q t := fun t => sq_nonneg _
    have hqint : IntegrableOn q (Set.Ici 0) := by simpa only [q] using hvel2
    have hq_bound : ∀ n : ℕ, (∫ t in 1..(n + 1 : ℝ), q t) ≤ V := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      rw [intervalIntegral.integral_of_le hn]
      exact setIntegral_mono_set hqint
        (Filter.Eventually.of_forall fun t => hq_nonneg t)
        (Filter.Eventually.of_forall fun t ht =>
          show t ∈ Set.Ici 0 from
            le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt ht.1))
    have hlocal : ∀ n : ℕ, IntegrableOn r (Set.Ioc 1 (n + 1 : ℝ)) := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hu : ContDiffOn ℝ 2 sys.u (Set.Icc 1 (n + 1 : ℝ)) :=
        sys.contDiff.mono (fun s hs => le_trans (by norm_num) hs.1)
      have hv : ContDiffOn ℝ 1 (fun s => fderiv ℝ sys.u s 1) (Set.Icc 1 (n + 1 : ℝ)) := by
        intro s hs
        have hlocal := sys.contDiff.contDiffAt
          (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
        exact ((hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
      have ha : ContinuousOn (fun s => fderiv ℝ (fun t => fderiv ℝ sys.u t 1) s 1)
          (Set.Icc 1 (n + 1 : ℝ)) := by
        intro s hs
        have hlocal := sys.contDiff.contDiffAt
          (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
        have hvlocal := (hlocal.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
            (contDiffAt_const (c := (1 : ℝ)))
        exact ((hvlocal.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))).continuousAt.continuousWithinAt
      exact (ha.add (continuousOn_const.smul hv.continuousOn)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hbound : ∀ᶠ n : ℕ in atTop, (∫ t in 1..(n + 1 : ℝ), ‖r t‖) ≤
        (deriv phi 1 + 1 + V + gamma * phi 1) / rho := by
      have hTendsto' : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have hdshift := hderiv0.comp hTendsto'
      rcases (Metric.tendsto_atTop.mp hdshift 1 zero_lt_one) with ⟨N, hN⟩
      filter_upwards [Ioi_mem_atTop N] with n hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnat : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hsmall : |deriv phi ((n : ℝ) + 1)| ≤ 1 := by
        have := hN n (le_of_lt hn)
        simpa [Real.dist_eq] using this.le
      have hrad := radial_acceleration_interval_bound sys haccelIneq hnat
      have hphiT : 0 ≤ phi ((n : ℝ) + 1) := by
        dsimp [phi]
        positivity
      have hvel := hq_bound n
      apply (le_div_iff₀ hrho).2
      rw [mul_comm]
      change rho * (∫ t in 1..(n + 1 : ℝ), ‖r t‖) ≤
        deriv phi 1 + 1 + V + gamma * phi 1
      have hneg : -deriv phi ((n : ℝ) + 1) ≤ 1 := by
        linarith [neg_le_of_abs_le hsmall]
      have hgamma : 0 < gamma := sys.gamma_pos
      simpa only [r, q, phi] using (le_trans hrad (by nlinarith))
    have hTendsto : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hrint : IntegrableOn r (Set.Ioi 1) :=
      integrableOn_Ioi_of_intervalIntegral_norm_bounded _ 1 hlocal hTendsto hbound
    have hw : Tendsto (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t) atTop
        (nhds (limUnder atTop (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t))) := by
      apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (f' := r) ?_ hrint
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
        (dissipativeSystem_differentiableAt_pos sys ht0).hasDerivAt
      convert (dissipativeSystem_velocity_hasDerivAt_pos sys ht0).add
        ((hasDerivAt_const t gamma).smul hu) using 1
      all_goals simp [r]
    let wLim : H := limUnder atTop (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t)
    have huLim : Tendsto sys.u atTop (nhds (gamma⁻¹ • wLim)) := by
      have hsub := hw.sub hvel0
      have hscaled :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (gamma⁻¹ : ℝ)) atTop
          (nhds (gamma⁻¹ : ℝ))).smul hsub
      simpa only [wLim, sub_zero, smul_sub, smul_add, smul_smul,
        inv_mul_cancel₀ (ne_of_gt sys.gamma_pos), one_smul, add_sub_cancel_left] using hscaled
    have hMin : (argmin Phi (potential_range_bddBelow hPhi)).Nonempty := ⟨z0, hz0min⟩
    rcases hweak hMin with ⟨uhat, huhat, hweakU⟩
    have huWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
        (nhds (toWeakSpace ℝ H (gamma⁻¹ • wLim))) :=
      (toWeakSpaceCLM ℝ H).continuous.tendsto _ |>.comp huLim
    have heq : gamma⁻¹ • wLim = uhat :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique huWeak hweakU)
    exact ⟨uhat, huhat, heq ▸ huLim⟩

end Alvarez2000
