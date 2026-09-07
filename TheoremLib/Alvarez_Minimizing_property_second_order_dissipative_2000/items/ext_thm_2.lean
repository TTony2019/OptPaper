import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.def_1
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_2
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_6
import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.thm_1

/- The source cites Bruck's first-order steepest-descent result only as a
   methodological precedent.  This file formalizes the adjacent, fully stated
   even-potential branch of Alvarez Theorem 2.4(i). -/
namespace Alvarez2000

open Filter
open MeasureTheory
open scoped InnerProductSpace Topology

/-- The even-potential branch of the scalar-damped strong-convergence result.

This is the result proved as Theorem 2.4(i) in Alvarez's paper.  The cited
Bruck result concerns first-order steepest descent, whose hypotheses are not
reproduced in the source. -/
private theorem even_convex_zero_mem_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Phi : H → ℝ} (hconv : ConvexOn ℝ Set.univ Phi)
    (heven : IsEvenFunction Phi) (hBdd : BddBelow (Set.range Phi)) :
    (0 : H) ∈ argmin Phi hBdd := by
  rw [argmin]
  apply le_antisymm
  · refine le_csInf ⟨Phi 0, ⟨0, rfl⟩⟩ ?_
    rintro _ ⟨x, rfl⟩
    have hmid := hconv.2 (Set.mem_univ x) (Set.mem_univ (-x))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hzero : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by module
    rw [hzero] at hmid
    rw [heven x] at hmid
    norm_num at hmid
    linarith
  · exact csInf_le hBdd ⟨0, rfl⟩

/-- The first-order support inequality for a differentiable convex potential. -/
private theorem convex_gradient_support {H : Type*} [NormedAddCommGroup H]
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

/-- The squared distance to a fixed point satisfies the scalar damped
inequality on the positive-time interior.  This is kept here because the
corresponding calculation in `thm_1` is deliberately private. -/
private theorem even_distance_damped_ineq {H : Type*} [NormedAddCommGroup H]
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
    have h : HasDerivAt phi ⟪v s, sys.u s - x⟫_ℝ s := by
      convert hsqs using 1 <;> simp [phi, real_inner_comm] <;> ring
    exact h.deriv
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
  have hsupp := convex_gradient_support hPhi.convex sys.is_gradient (sys.u t) x
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

/-- The causal exponential convolution of an integrable scalar forcing is
integrable on the positive half-line.  This is the analytic tail estimate
needed in the even-potential argument. -/
private theorem causal_exp_convolution_integrable_local (g : ℝ → ℝ) (gamma : ℝ)
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

/-- The nested causal error occurring in the moving-endpoint estimate has a
finite limit. -/
private theorem even_causal_error_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hvel2 : IntegrableOn (fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2) (Set.Ici 0)) :
    ∃ Herr : ℝ, Tendsto (fun r => (3 / 2 : ℝ) *
      ∫ theta in 1..r, ∫ s in 0..theta,
        Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2)
      atTop (nhds Herr) := by
  let v2 : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u s 1‖ ^ 2
  have hv2abs : ∀ s, |v2 s| = v2 s := by
    intro s
    exact abs_of_nonneg (sq_nonneg _)
  have hq : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * v2 s) (Set.Ici 0) := by
    have h := causal_exp_convolution_integrable_local v2 gamma sys.gamma_pos hvel2
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    simp only [hv2abs]
  have hqIoi : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * v2 s) (Set.Ioi 1) := by
    exact hq.mono_set (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr (by norm_num)))
  let L : ℝ := ∫ theta in Set.Ioi 1,
    ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * v2 s
  have hL : Tendsto (fun r : ℝ => ∫ theta in 1..r,
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * v2 s)
      atTop (nhds L) := by
    simpa [L] using intervalIntegral_tendsto_integral_Ioi 1 hqIoi tendsto_id
  refine ⟨(3 / 2 : ℝ) * L, ?_⟩
  have hconst := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 / 2 : ℝ)) atTop
    (nhds (3 / 2))).mul hL
  simpa [v2, mul_assoc] using hconst

/-- The moving-endpoint quadratic from the even-potential argument satisfies
the frozen-energy differential inequality. -/
private theorem even_moving_endpoint_damped_ineq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (hEven : IsEvenFunction Phi)
    {T s : ℝ} (hT : 1 ≤ T) (hs : s ∈ Set.Ioc 1 T) :
    deriv (deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2)) s +
        gamma * deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) s ≤
      (3 / 2 : ℝ) * ‖fderiv ℝ sys.u s 1‖ ^ 2 := by
  let phi : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r - (-sys.u T)‖ ^ 2
  let g : ℝ → ℝ := fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
    (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2
  have hquad : ∀ r : ℝ, g r = phi r - 2 * ‖sys.u T‖ ^ 2 := by
    intro r
    dsimp [g, phi]
    rw [show sys.u r - -sys.u T = sys.u r + sys.u T by abel]
    rw [norm_sub_sq_real, norm_add_sq_real]
    ring
  have hderiv : deriv g s = deriv phi s := by
    rw [show g = fun r => phi r - 2 * ‖sys.u T‖ ^ 2 from funext hquad]
    simp
  have hsecond : deriv (deriv g) s = deriv (deriv phi) s := by
    have hevent : deriv g =ᶠ[nhds s] deriv phi := by
      filter_upwards with r
      rw [show g = fun q => phi q - 2 * ‖sys.u T‖ ^ 2 from funext hquad]
      simp
    exact Filter.EventuallyEq.deriv_eq hevent
  have hbase := scalar_distance_damped_frozen_energy_ineq hPhi sys
    (x := -sys.u T) (a := 1) (t := T) (s := s) (by norm_num) hT hs
  have heven : Phi (-sys.u T) = Phi (sys.u T) := by
    simpa using hEven (sys.u T)
  rw [show (fun r => (1 / 2 : ℝ) * ‖sys.u r - -sys.u T‖ ^ 2) = phi by rfl] at hbase
  rw [hsecond, hderiv]
  rw [heven] at hbase
  have hnonneg : 0 ≤ ‖fderiv ℝ sys.u T 1‖ ^ 2 := sq_nonneg _
  linarith

/-- The endpoint-sensitive initial derivative in the two-time estimate. -/
private theorem even_moving_endpoint_deriv_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (T : ℝ) :
    deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
      (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1 =
      ⟪fderiv ℝ sys.u 1 1, sys.u 1 + sys.u T⟫_ℝ := by
  have hu : HasDerivAt sys.u (fderiv ℝ sys.u 1 1) 1 :=
    (dissipativeSystem_differentiableAt_pos sys (by norm_num)).hasDerivAt
  let g : ℝ → ℝ := fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
    (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2
  let q : ℝ → ℝ := fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2 -
    (3 / 2 : ℝ) * ‖sys.u T‖ ^ 2 + ⟪sys.u r, sys.u T⟫_ℝ
  have hgq : g = q := by
    funext r
    dsimp [g, q]
    rw [norm_sub_sq_real]
    ring
  have hq : HasDerivAt q ⟪fderiv ℝ sys.u 1 1, sys.u 1 + sys.u T⟫_ℝ 1 := by
    have hnorm : HasDerivAt (fun r => ‖sys.u r‖ ^ 2)
        (2 * ⟪fderiv ℝ sys.u 1 1, sys.u 1⟫_ℝ) 1 := by
      simpa [two_mul, real_inner_comm] using hu.norm_sq
    have hinner : HasDerivAt (fun r => ⟪sys.u r, sys.u T⟫_ℝ)
        ⟪fderiv ℝ sys.u 1 1, sys.u T⟫_ℝ 1 := by
      simpa using hu.inner ℝ (hasDerivAt_const 1 (sys.u T))
    convert ((hasDerivAt_const 1 (1 / 2 : ℝ)).mul hnorm).sub_const
      ((3 / 2 : ℝ) * ‖sys.u T‖ ^ 2) |>.add hinner using 1 <;>
      dsimp [q] <;> simp [inner_add_right] <;> ring
  rw [show (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
      (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) = g by rfl, hgq]
  exact hq.deriv

/-- Integrating-factor estimate on a compact interval with an arbitrary lower
endpoint.  This is the scalar FTC component of the moving-endpoint argument. -/
private theorem damped_one_time_exp_bound (omega q : ℝ → ℝ) (gamma a t : ℝ)
    (hDiff : ContDiffOn ℝ 1 omega (Set.Ici a))
    (hq : ContinuousOn q (Set.Icc a t))
    (hineq : ∀ s ∈ Set.Ioo a t, deriv omega s + gamma * omega s ≤ q s)
    (hat : a ≤ t) :
    omega t ≤ Real.exp (-gamma * (t - a)) * omega a +
      ∫ s in a..t, Real.exp (-gamma * (t - s)) * q s := by
  rcases hat.eq_or_lt with rfl | hat
  · simp
  let F : ℝ → ℝ := fun x => Real.exp (gamma * (x - a)) * omega x
  have hqOn : IntegrableOn q (Set.Icc a t) := hq.integrableOn_Icc
  have hExpCont : Continuous (fun s : ℝ => Real.exp (gamma * (s - a))) := by
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hweighted : IntegrableOn (fun s : ℝ =>
      Real.exp (gamma * (s - a)) * q s) (Set.Icc a t) :=
    IntegrableOn.continuousOn_mul
      hExpCont.continuousOn
      hqOn isCompact_Icc
  have hweighted_interval : IntervalIntegrable (fun s : ℝ =>
      Real.exp (gamma * (s - a)) * q s) volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hat.le).mpr hweighted
  have hF : ContDiffOn ℝ 1 F (Set.Icc a t) := by
    dsimp [F]
    have hExp : ContDiff ℝ 1 (fun x : ℝ => Real.exp (gamma * (x - a))) :=
      Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    exact hExp.contDiffOn.mul (hDiff.mono Set.Icc_subset_Ici_self)
  have hderivInt : IntervalIntegrable (deriv F) volume a t := by
    have hcont :=
      (hF.derivWithin (m := 0) (uniqueDiffOn_Icc hat) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc hat.le).congr_ae
    simp only [hat.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have hderiv : ∀ x ∈ Set.Ioo a t,
      deriv F x ≤ Real.exp (gamma * (x - a)) * q x := by
    intro x hx
    have hinner : HasDerivAt (fun y : ℝ => gamma * (y - a)) gamma x := by
      convert ((hasDerivAt_const (c := gamma) (x := x)).mul
        ((hasDerivAt_id x).sub_const a)) using 1 <;> ring
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (gamma * (y - a)))
        (gamma * Real.exp (gamma * (x - a))) x := by
      convert (Real.hasDerivAt_exp (gamma * (x - a))).comp x hinner using 1 <;> ring
    have homega : HasDerivAt omega (deriv omega x) x :=
      (hDiff.contDiffAt (Ici_mem_nhds hx.1)).differentiableAt
        (by norm_num) |>.hasDerivAt
    have hFderiv : deriv F x = Real.exp (gamma * (x - a)) *
        (deriv omega x + gamma * omega x) := by
      convert (hexp.mul homega).deriv using 1 <;> dsimp [F] <;> ring
    rw [hFderiv]
    exact mul_le_mul_of_nonneg_left (hineq x hx) (le_of_lt (Real.exp_pos _))
  have hFTC : F t - F a = ∫ x in a..t, deriv F x := by
    simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hF hat.le).symm
  have hIntegrated : F t - F a ≤ ∫ x in a..t,
      Real.exp (gamma * (x - a)) * q x := by
    rw [hFTC]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hat.le hderivInt hweighted_interval hderiv
  have hmul := mul_le_mul_of_nonneg_left hIntegrated
    (le_of_lt (Real.exp_pos (-gamma * (t - a))))
  rw [← intervalIntegral.integral_const_mul] at hmul
  have hexp : ∀ s : ℝ, Real.exp (-gamma * (t - a)) *
      Real.exp (gamma * (s - a)) = Real.exp (-gamma * (t - s)) := by
    intro s
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [F] at hmul
  have hcancel : Real.exp (-gamma * (t - a)) * Real.exp (gamma * (t - a)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [mul_sub] at hmul
  rw [← mul_assoc, hcancel] at hmul
  simp only [one_mul] at hmul
  have hkernel_eq : (∫ x in a..t, Real.exp (-gamma * (t - a)) *
      (Real.exp (gamma * (x - a)) * q x)) =
      ∫ x in a..t, Real.exp (-gamma * (t - x)) * q x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [← mul_assoc, hexp x]
  rw [hkernel_eq] at hmul
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hmul
  linarith

/-! A second integration of the preceding estimate.  The nested integral is
kept as an explicit integrability hypothesis; this makes the lemma usable for
the moving endpoint term below without imposing any global regularity on the
trajectory before time `a`. -/
theorem damped_two_time_integral_bound (g q : ℝ → ℝ) (gamma a t T : ℝ)
    (hDiff : ContDiffOn ℝ 1 g (Set.Ici a))
    (hDerivDiff : ContDiffOn ℝ 1 (deriv g) (Set.Ici a))
    (hq : ContinuousOn q (Set.Icc a T))
    (hNestedInt : IntervalIntegrable
      (fun theta => ∫ s in a..theta, Real.exp (-gamma * (theta - s)) * q s)
      volume t T)
    (hgamma : 0 < gamma) (hat : a ≤ t) (htT : t ≤ T)
    (hineq : ∀ s ∈ Set.Ioo a T, deriv (deriv g) s + gamma * deriv g s ≤ q s) :
    g T - g t ≤
      ((Real.exp (-gamma * (t - a)) - Real.exp (-gamma * (T - a))) / gamma) *
          deriv g a +
        ∫ theta in t..T, ∫ s in a..theta,
          Real.exp (-gamma * (theta - s)) * q s := by
  rcases htT.eq_or_lt with rfl | htT
  · simp
  have hpoint : ∀ theta ∈ Set.Icc t T,
      deriv g theta ≤ Real.exp (-gamma * (theta - a)) * deriv g a +
        ∫ s in a..theta, Real.exp (-gamma * (theta - s)) * q s := by
    intro theta htheta
    have hqtheta : ContinuousOn q (Set.Icc a theta) := by
      exact hq.mono (show Set.Icc a theta ⊆ Set.Icc a T from by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 htheta.2⟩)
    apply damped_one_time_exp_bound (omega := deriv g) (q := q) (gamma := gamma)
      (a := a) (t := theta) hDerivDiff
      hqtheta
    · intro s hs
      exact hineq s ⟨hs.1, lt_of_lt_of_le hs.2 htheta.2⟩
    · exact le_trans hat htheta.1
  have hderivInt : IntervalIntegrable (deriv g) volume t T := by
    have hcont : ContinuousOn (deriv g) (Set.Icc t T) :=
      hDerivDiff.continuousOn.mono (by
        intro x hx
        exact hat.trans hx.1)
    exact hcont.intervalIntegrable_of_Icc htT.le
  have hexpCont : ContinuousOn (fun theta : ℝ =>
      Real.exp (-gamma * (theta - a)) * deriv g a) (Set.Icc t T) := by
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).continuousOn.mul continuousOn_const
  have hexpInt : IntervalIntegrable (fun theta : ℝ =>
      Real.exp (-gamma * (theta - a)) * deriv g a) volume t T :=
    hexpCont.intervalIntegrable_of_Icc htT.le
  have hRHSInt : IntervalIntegrable (fun theta : ℝ =>
      Real.exp (-gamma * (theta - a)) * deriv g a +
        ∫ s in a..theta, Real.exp (-gamma * (theta - s)) * q s) volume t T :=
    hexpInt.add hNestedInt
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo htT.le hderivInt hRHSInt
    (fun theta htheta => hpoint theta ⟨le_of_lt htheta.1, le_of_lt htheta.2⟩)
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (hDiff.mono (by
      intro x hx
      exact hat.trans hx.1)) htT.le
  rw [hFTC] at hmono
  have hexp_eval : (∫ theta in t..T, Real.exp (-gamma * (theta - a))) =
      (Real.exp (-gamma * (t - a)) - Real.exp (-gamma * (T - a))) / gamma := by
    let F : ℝ → ℝ := fun theta => -(1 / gamma) * Real.exp (-gamma * (theta - a))
    have hF : ContDiffOn ℝ 1 F (Set.Icc t T) := by
      exact (contDiff_const.mul (Real.contDiff_exp.comp
        (contDiff_const.mul (contDiff_id.sub contDiff_const)))).contDiffOn
    have hFderiv : ∀ x : ℝ, deriv F x = Real.exp (-gamma * (x - a)) := by
      intro x
      have he : HasDerivAt (fun y : ℝ => Real.exp (-gamma * (y - a)))
          (-gamma * Real.exp (-gamma * (x - a))) x := by
        convert (Real.hasDerivAt_exp (-gamma * (x - a))).comp x
          ((hasDerivAt_const (c := -gamma) (x := x)).mul
            ((hasDerivAt_id x).sub_const a)) using 1 <;> ring
      convert (hasDerivAt_const x (-(1 / gamma : ℝ))).mul he |>.deriv using 1
      field_simp [hgamma.ne']
      norm_num
    have hFi := intervalIntegral.integral_deriv_of_contDiffOn_Icc hF htT.le
    have hcongr : (∫ x in t..T, deriv F x) =
        ∫ x in t..T, Real.exp (-gamma * (x - a)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      exact hFderiv x
    rw [← hcongr, hFi]
    dsimp [F]
    field_simp [hgamma.ne']
    ring
  have hscale : (∫ theta in t..T, Real.exp (-gamma * (theta - a)) * deriv g a) =
      (∫ theta in t..T, Real.exp (-gamma * (theta - a))) * deriv g a := by
    rw [show (fun theta : ℝ => Real.exp (-gamma * (theta - a)) * deriv g a) =
      fun theta => deriv g a * Real.exp (-gamma * (theta - a)) by
      funext theta; ring, intervalIntegral.integral_const_mul]
    simpa [mul_comm]
  have hscale' : (∫ u in t..T, Real.exp (-gamma * (u - a)) * deriv g a) =
      (Real.exp (-gamma * (t - a)) - Real.exp (-gamma * (T - a))) / gamma * deriv g a := by
    calc
      (∫ u in t..T, Real.exp (-gamma * (u - a)) * deriv g a) =
          (∫ u in t..T, Real.exp (-gamma * (u - a))) * deriv g a := hscale
      _ = (Real.exp (-gamma * (t - a)) - Real.exp (-gamma * (T - a))) / gamma *
          deriv g a := by rw [hexp_eval]
  have hmono' := hmono
  rw [intervalIntegral.integral_add hexpInt hNestedInt] at hmono'
  calc
    g T - g t ≤
        (∫ u in t..T, Real.exp (-gamma * (u - a)) * deriv g a) +
          (∫ u in t..T, ∫ s in a..u, Real.exp (-gamma * (u - s)) * q s) := hmono'
    _ = ((Real.exp (-gamma * (t - a)) - Real.exp (-gamma * (T - a))) / gamma) *
          deriv g a + ∫ theta in t..T, ∫ s in a..theta,
            Real.exp (-gamma * (theta - s)) * q s := by
      rw [hscale']

/-- A convergent squared-norm tail gives a uniform late bound for the
endpoint derivative occurring in the moving-endpoint calculation. -/
private theorem eventually_bounded_even_endpoint_deriv {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    {L : ℝ} (hNormSq : Tendsto (fun T : ℝ => ‖sys.u T‖ ^ 2) atTop (nhds L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T in atTop,
      |deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1| ≤ C := by
  rcases (Metric.tendsto_atTop.1 hNormSq) 1 (by norm_num) with ⟨N, hN⟩
  let B : ℝ := |L| + 2
  let C : ℝ := ‖fderiv ℝ sys.u 1 1‖ * (‖sys.u 1‖ + B)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop N] with T hT
  have hdist : dist (‖sys.u T‖ ^ 2) L < 1 := hN T hT
  have hsq : ‖sys.u T‖ ^ 2 ≤ |L| + 1 := by
    rw [Real.dist_eq] at hdist
    have : ‖sys.u T‖ ^ 2 < L + 1 := by linarith [abs_lt.mp hdist |>.2]
    exact this.le.trans (by gcongr; exact le_abs_self L)
  have hnorm : ‖sys.u T‖ ≤ B := by
    have hnonneg : 0 ≤ ‖sys.u T‖ := norm_nonneg _
    dsimp [B]
    nlinarith
  rw [even_moving_endpoint_deriv_one sys T]
  calc
    |⟪fderiv ℝ sys.u 1 1, sys.u 1 + sys.u T⟫_ℝ| ≤
        ‖fderiv ℝ sys.u 1 1‖ * ‖sys.u 1 + sys.u T‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖fderiv ℝ sys.u 1 1‖ * (‖sys.u 1‖ + ‖sys.u T‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ C := by
      dsimp [C]
      gcongr

theorem scalar_damped_even_strong_convergence_result {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhiDiff : ContDiff ℝ 1 Phi)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (hPhiBoundedBelow : ∃ m : ℝ, ∀ x : H, m ≤ Phi x)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hMin : (argmin Phi (by
      rcases hPhiBoundedBelow with ⟨m, hm⟩
      exact ⟨m, by rintro _ ⟨x, rfl⟩; exact hm x⟩)).Nonempty)
    (hEven : IsEvenFunction Phi) :
    ∃ uhat ∈ argmin Phi (by
      rcases hPhiBoundedBelow with ⟨m, hm⟩
      exact ⟨m, by rintro _ ⟨x, rfl⟩; exact hm x⟩), Tendsto sys.u atTop (nhds uhat) := by
  rcases hPhiBoundedBelow with ⟨m, hm⟩
  let hBdd : BddBelow (Set.range Phi) := ⟨m, by
    rintro _ ⟨x, rfl⟩
    exact hm x⟩
  have hZeroMin : (0 : H) ∈ argmin Phi hBdd :=
    even_convex_zero_mem_argmin hPhiConvex hEven hBdd
  have hMin' : (argmin Phi hBdd).Nonempty := by
    simpa only [proof_irrel_heq] using hMin
  let hPhi : HasPotentialAssumption Phi :=
    ⟨hPhiDiff, hPhiConvex, ⟨m, hm⟩⟩
  have hBdd' : potential_range_bddBelow hPhi = hBdd := by
    apply Subsingleton.elim
  have hMin'' : (argmin Phi (potential_range_bddBelow hPhi)).Nonempty := by
    simpa only [hBdd'] using hMin'
  obtain ⟨hvel2, hvel0, hPhi0, hweak⟩ :=
    scalar_damped_minimizing_property hPhi sys
  obtain ⟨uhat, hUhatMin, hUhatWeak⟩ := hweak hMin''
  have hUhatValue : Phi uhat = sInf (Set.range Phi) := hUhatMin
  have hDistanceIneq : ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - uhat‖ ^ 2)) t +
          gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - uhat‖ ^ 2) t ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    have h := even_distance_damped_ineq hPhi sys uhat ht
    have hgap : Phi uhat - Phi (sys.u t) ≤ 0 := by
      rw [hUhatValue]
      linarith [potential_sInf_le hPhi (sys.u t)]
    linarith
  have hZeroValue : Phi (0 : H) = sInf (Set.range Phi) := hZeroMin
  have hZeroDistanceIneq : ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s‖ ^ 2)) t +
          gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s‖ ^ 2) t ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    have h := even_distance_damped_ineq hPhi sys (0 : H) ht
    have hgap : Phi (0 : H) - Phi (sys.u t) ≤ 0 := by
      rw [hZeroValue]
      linarith [potential_sInf_le hPhi (sys.u t)]
    simpa using (h.trans (by linarith :
      Phi (0 : H) - Phi (sys.u t) + ‖fderiv ℝ sys.u t 1‖ ^ 2 ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2))
  -- Work on the positive-time tail.  Shifting by one lets the two scalar
  -- convergence lemmas be applied without ever differentiating at the
  -- one-sided endpoint `0` of the trajectory.
  let theta : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u (t + 1)‖ ^ 2
  have htheta : ContDiffOn ℝ 2 theta (Set.Ici 0) := by
    have hu : ContDiffOn ℝ 2 (fun t : ℝ => sys.u (t + 1)) (Set.Ici 0) := by
      exact sys.contDiff.comp
        ((contDiff_id.add contDiff_const).contDiffOn)
        (fun t ht => by
          change 0 ≤ t at ht
          simpa only [Set.mem_Ici] using add_nonneg ht (by norm_num))
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu)
  have hthetaDiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ theta t := by
    intro t ht
    change 0 ≤ t at ht
    have hu : DifferentiableAt ℝ (fun s : ℝ => sys.u (s + 1)) t :=
      (dissipativeSystem_differentiableAt_pos sys (by nlinarith : 0 < t + 1)).comp t
        (differentiableAt_id.add_const 1)
    simpa [theta] using (differentiableAt_const (c := (1 / 2 : ℝ))).mul (hu.norm_sq ℝ)
  have homega : ContDiffOn ℝ 1 (fun t => deriv theta t) (Set.Ici 0) := by
    have hwithin : ContDiffOn ℝ 1 (derivWithin theta (Set.Ici 0)) (Set.Ici 0) :=
      htheta.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact hwithin.congr fun t ht => by
      rw [deriv, derivWithin,
        fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) (hthetaDiff t ht)]
  have hthetaDeriv : ∀ s : ℝ, -1 < s →
      deriv theta s = deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by linarith
    have hphiDiff : DifferentiableAt ℝ (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
      have hu := dissipativeSystem_differentiableAt_pos sys hspos
      simpa using (differentiableAt_const (c := (1 / 2 : ℝ))).mul (hu.norm_sq ℝ)
    change deriv ((fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) ∘ fun r : ℝ => r + 1) s = _
    convert deriv_comp s hphiDiff (differentiableAt_id.add_const 1) using 1 <;> simp
  have hthetaSecond : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s =
        deriv (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2)) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by
      change 0 ≤ s at hs
      linarith
    have hderivDiff : DifferentiableAt ℝ
        (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2)) (s + 1) := by
      have hcd : ContDiffAt ℝ 2 (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
        have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
          sys.contDiff.mono Set.Ioi_subset_Ici_self
        exact (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu)).contDiffAt
          (Ioi_mem_nhds hspos)
      exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hevent : deriv theta =ᶠ[nhds s] fun r =>
        deriv (fun q => (1 / 2 : ℝ) * ‖sys.u q‖ ^ 2) (r + 1) := by
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
        fun s : ℝ => s + 1) (Set.Ici (0 - 1)) := heq.mpr hvel2
    exact hfull.mono_set (Set.Ici_subset_Ici.mpr (by norm_num : (0 - 1 : ℝ) ≤ 0))
  have hineq : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s + gamma * deriv theta s ≤
        ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    rw [hthetaSecond s hs, hthetaDeriv s (by
      change 0 ≤ s at hs
      linarith)]
    exact hZeroDistanceIneq (by
      change 0 ≤ s at hs
      linarith)
  have hpositive : IntegrableOn (fun s => max (deriv theta s) 0) (Set.Ici 0) :=
    positive_part_integrable_of_damped_inequality (fun s => deriv theta s)
      (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) gamma homega sys.gamma_pos hineq hforce
  obtain ⟨normTailLimit, hNormSqTail⟩ :=
    converges_of_integrable_positive_derivative theta (htheta.of_le (by norm_num))
      (by
        refine ⟨0, ?_⟩
        intro s hs
        dsimp [theta]
        positivity) hpositive
  have hNormSqShift : Tendsto (fun s : ℝ => ‖sys.u (s + 1)‖ ^ 2) atTop
      (nhds (2 * normTailLimit)) := by
    have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul
      hNormSqTail
    simpa [theta] using hscaled
  have hNormSq : Tendsto (fun t : ℝ => ‖sys.u t‖ ^ 2) atTop
      (nhds (2 * normTailLimit)) := by
    have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    convert hNormSqShift.comp hshift using 1
    ext t
    congr 2
    ring
  -- The causal error term from the paper is now available as a genuine
  -- convergent primitive.  The remaining task is to connect it to the
  -- moving-endpoint differential estimate (2.9).
  obtain ⟨Herr, hCausalError⟩ := even_causal_error_converges sys hvel2
  let Herror : ℝ → ℝ := fun r => (3 / 2 : ℝ) *
    ∫ theta in 1..r, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2
  have hHerror : Tendsto Herror atTop (nhds Herr) := by
    simpa [Herror] using hCausalError
  -- The coefficient of the initial derivative in the two-time integrating
  -- factor estimate is nonnegative.  Together with the uniform endpoint
  -- bound above, this is the tail estimate needed after that estimate is
  -- integrated.
  obtain ⟨C, hCnonneg, hCtail⟩ :=
    eventually_bounded_even_endpoint_deriv sys hNormSq
  have hEndpointTerm : ∀ ⦃t T : ℝ⦄, 1 ≤ t → t ≤ T →
      (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma ≥ 0 ∧
      ∀ᶠ T in atTop,
        ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) *
          deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
            (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1 ≤
          ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) * C := by
    intro t T ht hle
    have hneg : -gamma * (T - 1) ≤ -gamma * (t - 1) := by
      nlinarith [sys.gamma_pos]
    have hexp : Real.exp (-gamma * (T - 1)) ≤ Real.exp (-gamma * (t - 1)) :=
      Real.exp_le_exp.mpr hneg
    have hcoef : 0 ≤
        (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma := by
      exact div_nonneg (sub_nonneg.mpr hexp) (le_of_lt sys.gamma_pos)
    refine ⟨hcoef, ?_⟩
    filter_upwards [hCtail, eventually_ge_atTop T] with S hS hTS
    have hnegS : -gamma * (S - 1) ≤ -gamma * (t - 1) := by
      nlinarith [sys.gamma_pos]
    have hcoefS : 0 ≤
        (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (S - 1))) / gamma := by
      exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hnegS))
        (le_of_lt sys.gamma_pos)
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hS) hcoefS
  let vfun : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let qfun : ℝ → ℝ := fun s => (3 / 2 : ℝ) * ‖vfun s‖ ^ 2
  have hvOn : ContinuousOn vfun (Set.Ici (1 : ℝ)) := by
    intro s hs
    have hlocal : ContDiffAt ℝ 2 sys.u s :=
      sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs))
    have hv : ContDiffAt ℝ 1 vfun s := by
      simpa [vfun] using
        (hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))
    exact hv.continuousAt.continuousWithinAt
  have hqOn : ContinuousOn qfun (Set.Ici (1 : ℝ)) := by
    have hn : ContinuousOn (fun s : ℝ => ‖vfun s‖) (Set.Ici (1 : ℝ)) :=
      continuous_norm.continuousOn.comp hvOn (fun _ _ => Set.mem_univ _)
    simpa [qfun] using continuousOn_const.mul (hn.pow 2)
  let vext : ℝ → H := fun s => vfun (max s 1)
  let qext : ℝ → ℝ := fun s => qfun (max s 1)
  have hvext : Continuous vext := by
    apply ContinuousOn.comp_continuous hvOn (continuous_id.max continuous_const)
    intro s
    exact show 1 ≤ max s 1 from le_max_right _ _
  have hqext : Continuous qext := by
    apply ContinuousOn.comp_continuous hqOn (continuous_id.max continuous_const)
    intro s
    exact show 1 ≤ max s 1 from le_max_right _ _
  have hq_eq : ∀ s : ℝ, 1 ≤ s → qext s = qfun s := by
    intro s hs
    simp [qext, qfun, max_eq_left hs]
  have hNestedInt : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      IntervalIntegrable (fun theta => ∫ s in (1 : ℝ)..theta,
        Real.exp (-gamma * (theta - s)) * qfun s) volume t T := by
    intro t T ht hT
    let F : ℝ → ℝ → ℝ := fun theta s =>
      Real.exp (-gamma * (theta - s)) * qext s
    have hFcont : Continuous (Function.uncurry F) := by
      dsimp [F]
      fun_prop
    have hJcont : Continuous (fun theta : ℝ =>
        ∫ s in (1 : ℝ)..theta, F theta s) := by
      simpa [F] using
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (a₀ := (1 : ℝ)) hFcont continuous_id)
    have hJint : IntervalIntegrable (fun theta : ℝ =>
        ∫ s in (1 : ℝ)..theta, F theta s) volume t T :=
      hJcont.continuousOn.intervalIntegrable_of_Icc hT
    refine hJint.congr ?_
    intro theta htheta
    apply intervalIntegral.integral_congr_ae
    simp only [Set.uIoc_of_le hT] at htheta
    have htheta1 : 1 ≤ theta := le_trans ht htheta.1.le
    simp only [Set.uIoc_of_le htheta1] at *
    filter_upwards with s hs
    have hs1 : 1 ≤ s := by
      exact hs.1.le
    simp [F, hq_eq s hs1]
  have hGDiff : ∀ T : ℝ, ContDiffOn ℝ 2
      (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) (Set.Ici (1 : ℝ)) := by
    intro T
    have hu : ContDiffOn ℝ 2 sys.u (Set.Ici (1 : ℝ)) :=
      sys.contDiff.mono (Set.Ici_subset_Ici.mpr (by norm_num))
    have hc : ContDiffOn ℝ 2 (fun _ : ℝ => ‖sys.u T‖ ^ 2) (Set.Ici (1 : ℝ)) :=
      contDiffOn_const
    have hu_sub : ContDiffOn ℝ 2 (fun r : ℝ => sys.u r - sys.u T)
        (Set.Ici (1 : ℝ)) := hu.sub contDiffOn_const
    exact ((ContDiffOn.norm_sq ℝ hu).sub hc).sub
      (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu_sub))
  have hGDerivDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (deriv
      (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2)) (Set.Ici (1 : ℝ)) := by
    intro T
    have hG2 := hGDiff T
    have hwithin := hG2.derivWithin (m := 1) (uniqueDiffOn_Ici 1) (by norm_num)
    refine hwithin.congr ?_
    intro s hs
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 1) s hs)]
    have hu : DifferentiableAt ℝ sys.u s :=
      dissipativeSystem_differentiableAt_pos sys (lt_of_lt_of_le (by norm_num) hs)
    have hGdiff : DifferentiableAt ℝ
        (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) s := by
      have hc : DifferentiableAt ℝ (fun _ : ℝ => ‖sys.u T‖ ^ 2) s :=
        differentiableAt_const (c := ‖sys.u T‖ ^ 2)
      have hsquare : DifferentiableAt ℝ
          (fun r : ℝ => (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) s :=
        (differentiableAt_const (c := (1 / 2 : ℝ))).mul
          ((hu.sub_const (sys.u T)).norm_sq ℝ)
      exact (hu.norm_sq ℝ).sub hc |>.sub hsquare
    exact hGdiff
  have hTwo : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2 ≤
        ‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 +
          ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1 +
          ∫ theta in t..T, ∫ s in 1..theta,
            Real.exp (-gamma * (theta - s)) * qfun s := by
    intro t T ht hT
    have hT1 : 1 ≤ T := ht.trans hT
    have hqcont : ContinuousOn qfun (Set.Icc (1 : ℝ) T) :=
      hqOn.mono (Set.Icc_subset_Ici_self)
    have hbase := damped_two_time_integral_bound
      (g := fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2)
      (q := qfun) gamma 1 t T ((hGDiff T).of_le (by norm_num)) (hGDerivDiff T)
      hqcont (hNestedInt ht hT) sys.gamma_pos ht hT
      (fun s hs => by
        simpa [qfun] using even_moving_endpoint_damped_ineq hPhi sys hEven hT1
          ⟨hs.1, hs.2.le⟩)
    have hG_T : (‖sys.u T‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u T - sys.u T‖ ^ 2) = 0 := by simp
    have hG_t : (‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2) =
        ‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2 := by rfl
    dsimp at hbase
    simp only [sub_self, norm_zero, zero_mul, sub_zero] at hbase
    linarith
  have hJ0int : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2)
      (Set.Ici (0 : ℝ)) := by
    have h := causal_exp_convolution_integrable_local
      (fun s : ℝ => ‖vfun s‖ ^ 2) gamma sys.gamma_pos hvel2
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖vfun s‖ ^ 2)]
  have hJ0intIcc : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      IntervalIntegrable (fun theta : ℝ =>
        ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2)
        volume t T := by
    intro t T ht hT
    have hset : Set.uIcc t T ⊆ Set.Ici (0 : ℝ) := by
      rw [Set.uIcc_of_le hT]
      intro x hx
      exact le_trans (by linarith [ht]) hx.1
    exact (hJ0int.mono_set hset).intervalIntegrable
  have hNestedLe : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (∫ theta in t..T, ∫ s in 1..theta,
        Real.exp (-gamma * (theta - s)) * qfun s) ≤ Herror T - Herror t := by
    intro t T ht hT
    have hT1 : 1 ≤ T := ht.trans hT
    have hpoint : ∀ theta ∈ Set.Icc t T,
        (∫ s in 1..theta, Real.exp (-gamma * (theta - s)) * qfun s) ≤
          (3 / 2 : ℝ) * (∫ s in 0..theta,
            Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) := by
      intro theta htheta
      have htheta1 : 1 ≤ theta := ht.trans htheta.1
      let K : ℝ → ℝ := fun s => Real.exp (-gamma * (theta - s)) *
        ‖vfun s‖ ^ 2
      have hKnonneg : ∀ s : ℝ, 0 ≤ K s := by
        intro s
        exact mul_nonneg (le_of_lt (Real.exp_pos _)) (sq_nonneg _)
      have hKint01 : IntervalIntegrable K volume 0 1 := by
        have hKcont : ContinuousOn
            (fun s : ℝ => Real.exp (-gamma * (theta - s))) (Set.Icc 0 1) := by
          fun_prop
        have hgint : IntegrableOn (fun s : ℝ => ‖vfun s‖ ^ 2) (Set.Icc 0 1) :=
          hvel2.mono_set Set.Icc_subset_Ici_self
        apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
        exact hgint.continuousOn_mul hKcont isCompact_Icc
      have hKint1 : IntervalIntegrable K volume 1 theta := by
        have hcont : ContinuousOn K (Set.Icc 1 theta) := by
          dsimp [K]
          have hvnorm : ContinuousOn (fun s : ℝ => ‖vfun s‖ ^ 2)
              (Set.Icc 1 theta) := by
            simpa only [Function.comp_apply] using
              ((continuous_norm.continuousOn.comp hvOn
                (fun _ _ => Set.mem_univ _)).pow 2).mono
                Set.Icc_subset_Ici_self
          exact (Real.continuous_exp.comp (continuous_const.mul
            (continuous_const.sub continuous_id))).continuousOn.mul hvnorm
        exact hcont.intervalIntegrable_of_Icc htheta1
      have hadd := intervalIntegral.integral_add_adjacent_intervals hKint01 hKint1
      have hnonneg : 0 ≤ ∫ s in 0..1, K s :=
        intervalIntegral.integral_nonneg (by norm_num) (fun s hs => hKnonneg s)
      dsimp [qfun, vfun, K]
      rw [show (fun s : ℝ => Real.exp (-gamma * (theta - s)) *
          ((3 / 2 : ℝ) * ‖vfun s‖ ^ 2)) =
          fun s => (3 / 2 : ℝ) *
            (Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) by
        funext s; ring, intervalIntegral.integral_const_mul]
      rw [← hadd]
      linarith
    have hleft := hNestedInt ht hT
    have hright := (hJ0intIcc ht hT).const_mul (3 / 2 : ℝ)
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hT hleft hright
      (fun theta htheta => hpoint theta ⟨le_of_lt htheta.1, le_of_lt htheta.2⟩)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hJ0intIcc (by norm_num) ht) (hJ0intIcc ht hT)
    dsimp [Herror]
    rw [show (∫ theta in 1..T, ∫ s in 0..theta,
        Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) =
        (∫ theta in 1..t, ∫ s in 0..theta,
          Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) +
          ∫ theta in t..T, ∫ s in 0..theta,
            Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2 by
      exact hsplit.symm]
    linarith

  have hUniform : ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ s t : ℝ,
      N ≤ s → N ≤ t → dist (sys.u s) (sys.u t) < ε := by
    intro ε hε
    let δ : ℝ := ε ^ 2 / 12
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    rcases Metric.tendsto_atTop.1 hNormSq δ hδ with ⟨Nnorm, hNnorm⟩
    rcases Metric.tendsto_atTop.1 hHerror δ hδ with ⟨Nerr, hNerr⟩
    have hexp0 : Tendsto (fun r : ℝ => Real.exp (-gamma * (r - 1))) atTop
        (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hshift : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
      convert (tendsto_id.const_mul_atTop_of_neg
        (by linarith [sys.gamma_pos] : -gamma < 0)).comp hshift using 1 <;> ring
    have hexpC : Tendsto (fun r : ℝ => (C / gamma) *
        Real.exp (-gamma * (r - 1))) atTop (nhds 0) := by
      simpa using hexp0.const_mul (C / gamma)
    rcases Metric.tendsto_atTop.1 hexpC δ hδ with ⟨Nexp, hNexp⟩
    rcases eventually_atTop.1 hCtail with ⟨NC, hNC⟩
    let N : ℝ := max 1 (max Nnorm (max Nerr (max Nexp NC)))
    have hN1 : 1 ≤ N := le_max_left _ _
    have hNnorm_le : Nnorm ≤ N := by
      calc
        Nnorm ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_left _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNerr_le : Nerr ≤ N := by
      calc
        Nerr ≤ max Nerr (max Nexp NC) := le_max_left _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNexp_le : Nexp ≤ N := by
      calc
        Nexp ≤ max Nexp NC := le_max_left _ _
        _ ≤ max Nerr (max Nexp NC) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNC_le : NC ≤ N := by
      calc
        NC ≤ max Nexp NC := le_max_right _ _
        _ ≤ max Nerr (max Nexp NC) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    refine ⟨N, ?_⟩
    have hordered : ∀ {s t : ℝ}, N ≤ s → N ≤ t → s ≤ t →
        dist (sys.u s) (sys.u t) < ε := by
      intro s t hs ht hst
      have h1s : 1 ≤ s := hN1.trans hs
      have h1t : 1 ≤ t := hN1.trans ht
      have hsNnorm : Nnorm ≤ s := hNnorm_le.trans hs
      have htNnorm : Nnorm ≤ t := hNnorm_le.trans ht
      have hsNerr : Nerr ≤ s := hNerr_le.trans hs
      have htNerr : Nerr ≤ t := hNerr_le.trans ht
      have hsNexp : Nexp ≤ s := hNexp_le.trans hs
      have htNC : NC ≤ t := hNC_le.trans ht
      have hnorm_s : |‖sys.u s‖ ^ 2 - 2 * normTailLimit| < δ := by
        simpa [Real.dist_eq] using hNnorm s hsNnorm
      have hnorm_t : |‖sys.u t‖ ^ 2 - 2 * normTailLimit| < δ := by
        simpa [Real.dist_eq] using hNnorm t htNnorm
      have hnorm_tri : |‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2| ≤
          |‖sys.u s‖ ^ 2 - 2 * normTailLimit| +
            |‖sys.u t‖ ^ 2 - 2 * normTailLimit| := by
        simpa [abs_sub_comm] using
          (abs_sub_le (‖sys.u s‖ ^ 2) (2 * normTailLimit) (‖sys.u t‖ ^ 2))
      have hnorm_diff : ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 < 2 * δ := by
        exact lt_of_le_of_lt (le_abs_self _) (by linarith [hnorm_tri, hnorm_s, hnorm_t])
      have herr_s : |Herror s - Herr| < δ := by
        simpa [Real.dist_eq] using hNerr s hsNerr
      have herr_t : |Herror t - Herr| < δ := by
        simpa [Real.dist_eq] using hNerr t htNerr
      have herr_tri : |Herror t - Herror s| ≤
          |Herror t - Herr| + |Herror s - Herr| := by
        have h := abs_sub_le (Herror t) Herr (Herror s)
        rw [abs_sub_comm Herr (Herror s)] at h
        exact h
      have herr_diff : Herror t - Herror s < 2 * δ := by
        exact lt_of_le_of_lt (le_abs_self _) (by linarith [herr_tri, herr_s, herr_t])
      have hcoef_nonneg : 0 ≤
          (Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma := by
        have harg : -gamma * (t - 1) ≤ -gamma * (s - 1) := by
          have hmul : 0 ≤ gamma * (t - s) :=
            mul_nonneg (le_of_lt sys.gamma_pos) (sub_nonneg.mpr hst)
          linarith
        exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr harg))
          (le_of_lt sys.gamma_pos)
      have hderiv_le : deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 ≤ C := by
        exact (le_abs_self _).trans (hNC t htNC)
      have hend0 :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 ≤
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) * C :=
        mul_le_mul_of_nonneg_left hderiv_le hcoef_nonneg
      have hexp_t_nonneg : 0 ≤ Real.exp (-gamma * (t - 1)) :=
        (Real.exp_pos _).le
      have hcoef_le :
          (Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma ≤
            Real.exp (-gamma * (s - 1)) / gamma := by
        exact div_le_div_of_nonneg_right
          (sub_le_self _ hexp_t_nonneg) (le_of_lt sys.gamma_pos)
      have hend1 :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) * C ≤
            (C / gamma) * Real.exp (-gamma * (s - 1)) := by
        calc
          _ ≤ (Real.exp (-gamma * (s - 1)) / gamma) * C :=
            mul_le_mul_of_nonneg_right hcoef_le hCnonneg
          _ = (C / gamma) * Real.exp (-gamma * (s - 1)) := by ring
      have hexp_bound : (C / gamma) * Real.exp (-gamma * (s - 1)) < δ := by
        have hnonneg : 0 ≤ (C / gamma) * Real.exp (-gamma * (s - 1)) :=
          mul_nonneg (div_nonneg hCnonneg (le_of_lt sys.gamma_pos))
            (le_of_lt (Real.exp_pos _))
        have h := hNexp s hsNexp
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h
        exact h
      have hend :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 < δ :=
        lt_of_le_of_lt (hend0.trans hend1) hexp_bound
      have hnest := hNestedLe h1s hst
      have hbound :
          ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 +
              ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
                deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
                  (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 +
            ∫ theta in s..t, ∫ r in 1..theta,
              Real.exp (-gamma * (theta - r)) * qfun r < ε ^ 2 / 2 := by
        have hsum :
            ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 +
                ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
                  deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
                    (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 +
              ∫ theta in s..t, ∫ r in 1..theta,
                Real.exp (-gamma * (theta - r)) * qfun r < 5 * δ := by
          linarith [hnorm_diff, hend, hnest, herr_diff]
        calc
          _ < 5 * δ := hsum
          _ = 5 * (ε ^ 2 / 12) := by rfl
          _ < ε ^ 2 / 2 := by nlinarith [sq_pos_of_pos hε]
      have hsq := hTwo h1s hst
      have hsq' : (1 / 2 : ℝ) * ‖sys.u s - sys.u t‖ ^ 2 < ε ^ 2 / 2 :=
        lt_of_le_of_lt hsq hbound
      have hnorm_lt : ‖sys.u s - sys.u t‖ < ε := by
        have hsqnorm : ‖sys.u s - sys.u t‖ ^ 2 < ε ^ 2 := by
          linarith
        simpa [abs_of_nonneg (norm_nonneg _)] using
          (abs_lt_of_sq_lt_sq hsqnorm (le_of_lt hε))
      simpa [dist_eq_norm] using hnorm_lt
    intro s t hs ht
    rcases le_total s t with hst | hts
    · exact hordered hs ht hst
    · simpa [dist_comm] using hordered ht hs hts

  obtain ⟨w, hstrong⟩ : ∃ w : H, Tendsto sys.u atTop (nhds w) := by
    apply cauchy_map_iff_exists_tendsto.mp
    rw [Metric.cauchy_iff]
    refine ⟨by infer_instance, ?_⟩
    intro ε hε
    rcases hUniform ε hε with ⟨N, hN⟩
    refine ⟨sys.u '' Set.Ici N, Filter.image_mem_map (eventually_ge_atTop N), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simpa [dist_eq_norm] using hN s t hs ht
  have hstrongWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
      (nhds (toWeakSpace ℝ H w)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto w).comp hstrong
  have hw : w = uhat :=
    (toWeakSpace ℝ H).injective (tendsto_nhds_unique hstrongWeak hUhatWeak)
  subst w
  exact ⟨uhat, hUhatMin, hstrong⟩

end Alvarez2000
