import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_3
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_4
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.thm_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_def_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_2

/- The derivative of the auxiliary curve used in the TOGES-VH energy. -/
private theorem togesVH_auxiliary_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (u uDot uDdot : ℝ → H) (t0 : ℝ)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (huDot : ∀ t, t0 ≤ t → HasDerivAt uDot (uDdot t) t) :
    ∀ t, t0 ≤ t → HasDerivAt (fun s => u s + (s / 4) • uDot s)
      ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) t := by
  intro t ht
  have hraw := (hu t ht).add (((hasDerivAt_id t).div_const 4).smul (huDot t ht))
  convert hraw using 1 <;> simp [id] <;> module

/- A global minimizer realizes the infimum of the range. -/
private theorem togesVH_sInf_eq_minimum {H : Type*} (f : H → ℝ) (z : H)
    (hMin : IsMinOn f Set.univ z) : sInf (Set.range f) = f z := by
  have hzGlobal : ∀ x : H, f z ≤ f x := by
    simpa [IsMinOn, IsMinFilter] using hMin
  apply le_antisymm
  · apply csInf_le
    · exact ⟨f z, fun y hy => by
        rcases hy with ⟨x, rfl⟩
        exact hzGlobal x⟩
    · exact ⟨z, rfl⟩
  · apply le_csInf
    · exact ⟨f z, ⟨z, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hzGlobal x

/-- The first-order support inequality supplied by convex differentiability. -/
private theorem togesVH_convex_gradient_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (grad : H → H)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x) (x y : H) :
    f x - f y ≤ inner ℝ (grad x) (x - y) := by
  let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y x
  have hline : HasDerivAt line (x - y) 1 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - y)).add_const y using 1
    all_goals simp
  have hphi : ConvexOn ℝ Set.univ (f ∘ line) := by
    simpa [line] using hConvex.comp_affineMap (AffineMap.lineMap y x)
  have hderiv : HasDerivAt (f ∘ line) (inner ℝ (grad x) (x - y)) 1 := by
    have hgradline : HasFDerivAt f (innerSL ℝ (grad x)) (line 1) := by
      simpa [line] using hGradient x
    simpa [innerSL_apply_apply] using hgradline.comp_hasDerivAt 1 hline
  have hslope := hphi.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
    (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hderiv
  simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using hslope

private theorem togesVH_delta_hasDerivAt (beta t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (togesVDelta beta) (2 * t - 2 * beta) t := by
  have hraw := ((hasDerivAt_pow 2 t).mul
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_const t (2 * beta)).div
      (hasDerivAt_id t) ht)))
  convert hraw using 1 <;> simp [togesVDelta, id] <;> field_simp [ht] <;> ring

private theorem togesVH_w_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u uDot uDdot uDddot : ℝ → H) (grad : H → H)
    (hess : H → H → H) (z : H) (alpha beta t0 tStart t : ℝ)
    (hu : ∀ r, t0 ≤ r → HasDerivAt u (uDot r) r)
    (huDot : ∀ r, t0 ≤ r → HasDerivAt uDot (uDdot r) r)
    (huDdot : ∀ r, t0 ≤ r → HasDerivAt uDdot (uDddot r) r)
    (hGradDeriv : ∀ r, t0 ≤ r → HasDerivAt
      (fun s => grad (u s + (s / 4) • uDot s))
      (hess (u r + (r / 4) • uDot r)
        ((5 / 4 : ℝ) • uDot r + (r / 4) • uDdot r)) r)
    (ht0Start : t0 ≤ tStart) (htStart : tStart ≤ t) (htne : t ≠ 0)
    (hTrajectory : ∀ r, t0 ≤ r →
      uDddot r + ((alpha + 7) / r) • uDdot r +
        (5 * (alpha + 1) / r ^ 2) • uDot r +
        beta • hess (u r + (r / 4) • uDot r)
          ((5 / 4 : ℝ) • uDot r + (r / 4) • uDdot r) +
        grad (u r + (r / 4) • uDot r) = 0) :
    HasDerivAt (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s)
      (-(togesVDelta beta t) • grad (u t + (t / 4) • uDot t)) t := by
  let A : ℝ → H := fun s =>
    uDdot s + beta • grad (u s + (s / 4) • uDot s)
  have htail : t0 ≤ t := le_trans ht0Start htStart
  have hA : HasDerivAt A
      (uDddot t + beta • hess (u t + (t / 4) • uDot t)
        ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) t := by
    simpa [A] using (huDdot t htail).add
      ((hGradDeriv t htail).const_smul beta)
  have hwfun :
      (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s) =
        (fun s => s ^ 2 • A s +
          (((alpha + 5) * s) • uDot s + (4 * alpha) • (u s - z))) := by
    funext s
    simp [A, togesVLyapunovVector, togesVAuxiliary]
    module
  have hfirst : HasDerivAt (fun s => s ^ 2 • A s)
      ((2 * t) • A t + t ^ 2 •
        (uDddot t + beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t))) t := by
    have h := ((hasDerivAt_id t).pow 2).smul hA
    have hfun : (id : ℝ → ℝ) ^ 2 • A = fun s => s ^ 2 • A s := by
      funext s
      simp [id]
    rw [hfun] at h
    simp [id] at h
    convert h using 1 <;> module
  have hsecond : HasDerivAt (fun s => ((alpha + 5) * s) • uDot s)
      ((alpha + 5) • uDot t + ((alpha + 5) * t) • uDdot t) t := by
    have h := ((hasDerivAt_id t).const_mul (alpha + 5)).smul (huDot t htail)
    have hfun : (fun y : ℝ => (alpha + 5) * id y) • uDot =
        fun s => ((alpha + 5) * s) • uDot s := by
      funext s
      simp [id]
    rw [hfun] at h
    simp [id] at h
    convert h using 1 <;> module
  have hthird : HasDerivAt (fun s => (4 * alpha) • (u s - z))
      ((4 * alpha) • uDot t) t := by
    simpa using ((hu t htail).sub_const z).const_smul (4 * alpha)
  have hraw := hfirst.add (hsecond.add hthird)
  have hraw' : HasDerivAt (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s)
      ((2 * t) • A t + t ^ 2 •
        (uDddot t + beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) +
        (((alpha + 5) • uDot t + ((alpha + 5) * t) • uDdot t) +
          (4 * alpha) • uDot t)) t := by
    rw [hwfun]
    exact hraw
  have hscaled := congrArg (fun q : H => t ^ 2 • q) (hTrajectory t htail)
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  have hcoef1 : t ^ 2 * ((alpha + 7) / t) = (alpha + 7) * t := by
    field_simp [htne]
  have hcoef2 : t ^ 2 * (5 * (alpha + 1) / t ^ 2) = 5 * (alpha + 1) := by
    field_simp [htne]
  rw [hcoef1, hcoef2] at hscaled
  have htarget :
      (2 * t) • A t + t ^ 2 •
        (uDddot t + beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) +
        (((alpha + 5) • uDot t + ((alpha + 5) * t) • uDdot t) +
          (4 * alpha) • uDot t) =
        -(togesVDelta beta t) • grad (u t + (t / 4) • uDot t) := by
    dsimp [A]
    rw [show togesVDelta beta t = t ^ 2 - 2 * beta * t by
      simp [togesVDelta]
      field_simp [htne]]
    rw [neg_smul]
    apply (eq_neg_iff_add_eq_zero).2
    rw [← hscaled]
    module
  exact hraw'.congr_deriv htarget

/- The derivative of the TOGES-VH Lyapunov function before applying convexity. -/
private theorem togesVH_energy_hasDerivAt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (u uDot uDdot : ℝ → H) (grad : H → H)
    (z : H) (alpha beta t : ℝ)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hv : HasDerivAt (fun s => u s + (s / 4) • uDot s)
      ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) t)
    (hw : HasDerivAt (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s)
      (-(togesVDelta beta t) • grad (u t + (t / 4) • uDot t)) t)
    (htne : t ≠ 0) :
    HasDerivAt (togesVLyapunov f u uDot uDdot grad z alpha beta)
      (4 * t * togesVDelta beta t *
          inner ℝ (grad (u t + (t / 4) • uDot t))
            ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) +
        4 * (togesVDelta beta t + t * (2 * t - 2 * beta)) *
          (f (u t + (t / 4) • uDot t) - sInf (Set.range f)) +
        inner ℝ (togesVLyapunovVector u uDot uDdot grad z alpha beta t)
          (-(togesVDelta beta t) • grad (u t + (t / 4) • uDot t))) t := by
  have hf : HasDerivAt (fun s => f (u s + (s / 4) • uDot s) - sInf (Set.range f))
      (inner ℝ (grad (u t + (t / 4) • uDot t))
        ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) t := by
    simpa [innerSL_apply_apply] using
      ((hGradient (u t + (t / 4) • uDot t)).comp_hasDerivAt t hv).sub_const
        (sInf (Set.range f))
  have hpref : HasDerivAt (fun s => 4 * s * togesVDelta beta s)
      (4 * (togesVDelta beta t + t * (2 * t - 2 * beta))) t := by
    have h := (((hasDerivAt_const t (4 : ℝ)).mul (hasDerivAt_id t)).mul
      (togesVH_delta_hasDerivAt beta t htne))
    convert h using 1 <;> simp [id] <;> ring
  have hsq := hw.norm_sq.const_mul (1 / 2 : ℝ)
  have hsum := (hpref.mul hf).add hsq
  convert hsum using 1 <;> simp [togesVLyapunov] <;> ring
/-
  have hA := (huDdot t (le_trans ht0Start htStart)).add
    ((hGradDeriv t (le_trans ht0Start htStart)).const_smul beta)
  have hfirst := (((hasDerivAt_id t).pow 2).smul
    ((huDdot t (le_trans ht0Start htStart)).add
      ((hGradDeriv t (le_trans ht0Start htStart)).const_smul beta)))
  have hsecond := (((hasDerivAt_id t).const_mul (alpha + 5 : ℝ)).smul
    (huDot t (le_trans ht0Start htStart)))
  have hthird := ((hu t (le_trans ht0Start htStart)).sub_const z).const_smul (4 * alpha)
  have hraw := hfirst.add (hsecond.add hthird)
  have hscaled := congrArg (fun q : H => t ^ 2 • q)
    (hTrajectory t (le_trans ht0Start htStart))
  simp only [smul_zero, smul_add, smul_smul] at hscaled
  have hcoef1 : t ^ 2 * ((alpha + 7) / t) = (alpha + 7) * t := by
    field_simp [htne]
  have hcoef2 : t ^ 2 * (5 * (alpha + 1) / t ^ 2) = 5 * (alpha + 1) := by
    field_simp [htne]
  rw [hcoef1, hcoef2] at hscaled
  have htarget :
      (2 * t) • (uDdot t + beta • grad (u t + (t / 4) • uDot t)) +
        t ^ 2 • (uDddot t + beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) +
        ((alpha + 5) • uDot t + ((alpha + 5) * t) • uDdot t) +
        (4 * alpha) • uDot t =
        -(togesVDelta beta t) • grad (u t + (t / 4) • uDot t) := by
    rw [show togesVDelta beta t = t ^ 2 - 2 * beta * t by
      simp [togesVDelta]
      field_simp [htne]]
    rw [neg_smul]
    apply (eq_neg_iff_add_eq_zero).2
    rw [← hscaled]
    module
  have hraw' : HasDerivAt (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s)
      ((2 * t) • (uDdot t + beta • grad (u t + (t / 4) • uDot t)) +
        t ^ 2 • (uDddot t + beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) +
        ((alpha + 5) • uDot t + ((alpha + 5) * t) • uDdot t) +
        (4 * alpha) • uDot t) t := by
    convert hraw using 1
    · ext s
      simp only [Pi.add_apply, Pi.smul_apply', Pi.smul_apply, Pi.pow_apply, id_eq]
      simp [togesVLyapunovVector]
      module
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, id_eq]
      module
  exact hraw'.congr_deriv htarget
-/

private theorem togesVH_integrableOn_Ici_of_nonneg_compact_integral_bound
    {a : ℝ} {g : ℝ → ℝ}
    (hcont : ∀ T, a ≤ T → ContinuousOn g (Set.Icc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s) (B : ℝ)
    (hbound : ∀ T, a ≤ T → (∫ s in a..T, g s) ≤ B) :
    MeasureTheory.IntegrableOn g (Set.Ici a) ∧
      (∫ s in Set.Ici a, g s) ≤ B := by
  let S : ℕ → Set ℝ := fun n => Set.Icc a (a + n)
  have hcover : MeasureTheory.AECover (MeasureTheory.volume.restrict (Set.Ici a))
      Filter.atTop S := by
    refine ⟨?_, fun n => (measurableSet_Icc : MeasurableSet (S n))⟩
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun t ht => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
    refine Filter.eventually_atTop.2 ⟨n, fun k hk => ?_⟩
    constructor
    · exact ht
    · dsimp [S]
      have hnk : (n : ℝ) ≤ k := by exact_mod_cast hk
      linarith
  have hfi : ∀ n, MeasureTheory.IntegrableOn g (S n)
      (MeasureTheory.volume.restrict (Set.Ici a)) := by
    intro n
    have hna : a ≤ a + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hc : MeasureTheory.IntegrableOn g (Set.Icc a (a + n)) MeasureTheory.volume :=
      (hcont (a + n) hna).integrableOn_Icc
    apply hc.mono_measure
    exact MeasureTheory.Measure.restrict_le_self
  have hnn : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici a)), 0 ≤ g t := by
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hnonneg
  have hb : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ t in S n, g t ∂(MeasureTheory.volume.restrict (Set.Ici a))) ≤ B := by
    filter_upwards with n
    have hna : a ≤ a + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hS : MeasurableSet (S n) := by
      dsimp [S]
      exact measurableSet_Icc
    rw [MeasureTheory.Measure.restrict_restrict hS,
      Set.inter_eq_left.mpr Set.Icc_subset_Ici_self,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hna]
    exact hbound (a + n) hna
  have hg : MeasureTheory.Integrable g
      (MeasureTheory.volume.restrict (Set.Ici a)) :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae B hfi hnn hb
  refine ⟨hg, ?_⟩
  exact le_of_tendsto (hcover.integral_tendsto_of_countably_generated hg) hb

/- The scalar correction in the approximate-descent estimate. -/
private theorem togesVH_correction_hasDerivAt (C r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => C / (3 * s ^ 3)) (-C / r ^ 4) r := by
  have h := (hasDerivAt_const r (C / 3)).mul
    (hasDerivAt_zpow (-3 : ℤ) r (Or.inl hr))
  have hfun : (fun s : ℝ => C / (3 * s ^ 3)) =
      (fun s => (C / 3) * s ^ (-3 : ℤ)) := by
    funext s
    rw [zpow_neg]
    by_cases hs : s = 0
    · subst s
      norm_num
    · field_simp [hs]
  rw [hfun]
  convert h using 1
  norm_num
  field_simp [hr]

/- The scalar comparison converting the dissipative weight into the t^4 weight. -/
private theorem togesVH_weighted_gradient_compare (alpha beta r q delta : ℝ)
    (hA2 : 0 < alpha - 2) (hBeta : 0 ≤ beta) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hdelta : r ^ 2 / (alpha - 2) ≤ delta) :
    beta * (r ^ 4 * q) ≤ (alpha - 2) * (beta * r ^ 2 * delta * q) := by
  have hfactor : 0 ≤ beta * r ^ 2 * q := by
    exact mul_nonneg (mul_nonneg hBeta (sq_nonneg r)) hq
  have hscaled := mul_le_mul_of_nonneg_left hdelta hfactor
  have hleft :
      (alpha - 2) * ((beta * r ^ 2 * q) * (r ^ 2 / (alpha - 2))) =
        beta * (r ^ 4 * q) := by
    field_simp [ne_of_gt hA2]
  have hright :
      (alpha - 2) * ((beta * r ^ 2 * q) * delta) =
        (alpha - 2) * (beta * r ^ 2 * delta * q) := by
    ring
  rw [← hleft, ← hright]
  exact mul_le_mul_of_nonneg_left hscaled hA2.le

/-- The energy and rate conclusions of Theorem 3.1 for a regular TOGES-VH solution. -/
theorem togesVH_rate_descent_and_integrability {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (hess : H → H → H)
    (z : H) (alpha beta t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (grad x)) x)
    (hGradDeriv : ∀ t, t0 ≤ t → HasDerivAt
      (fun s => grad (u s + (s / 4) • uDot s))
      (hess (u t + (t / 4) • uDot t)
        ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) t)
    (hMin : IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hu : ∀ t, t0 ≤ t → HasDerivAt u (uDot t) t)
    (huDot : ∀ t, t0 ≤ t → HasDerivAt uDot (uDdot t) t)
    (huDdot : ∀ t, t0 ≤ t → HasDerivAt uDdot (uDddot t) t)
    (hTrajectory : ∀ t, t0 ≤ t →
      uDddot t + ((alpha + 7) / t) • uDdot t + (5 * (alpha + 1) / t ^ 2) • uDot t +
        beta • hess (u t + (t / 4) • uDot t)
          ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) +
        grad (u t + (t / 4) • uDot t) = 0) :
    3 < alpha → 0 ≤ beta → let t1 := 2 * beta * (alpha - 2) / (alpha - 3)
      let tStart := max t0 t1
      let E1 := togesVLyapunov f u uDot uDdot grad z alpha beta tStart
      ∀ t ≥ tStart,
        f (u t + (t / 4) • uDot t) - sInf (Set.range f) ≤ (alpha - 2) * E1 / (4 * t ^ 3) ∧
        f (u t) - sInf (Set.range f) ≤
          (tStart ^ 4 * (f (u tStart) - sInf (Set.range f)) - (alpha - 2) * E1 * tStart) / t ^ 4 +
            (alpha - 2) * E1 / t ^ 3 ∧
        AntitoneOn (fun s => f (u s) + (alpha - 2) * E1 / (3 * s ^ 3)) (Set.Ici tStart) ∧
        (0 < beta →
          ∫ s in Set.Ici tStart, s ^ 4 * ‖grad (u s + (s / 4) • uDot s)‖ ^ 2 ≤
            (alpha - 2) * E1 / beta) := by
  intro hAlpha hBeta
  dsimp
  have hsInf := togesVH_sInf_eq_minimum f z hMin
  let t1 : ℝ := 2 * beta * (alpha - 2) / (alpha - 3)
  let tStart : ℝ := max t0 t1
  have ht0Start : t0 ≤ tStart := le_max_left _ _
  have hv : ∀ t, tStart ≤ t → HasDerivAt (fun s => u s + (s / 4) • uDot s)
      ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) t := by
    intro t ht
    exact togesVH_auxiliary_hasDerivAt u uDot uDdot t0 hu huDot t
      (le_trans ht0Start ht)
  have hA3 : 0 < alpha - 3 := by linarith
  have hA2 : 0 < alpha - 2 := by linarith
  have ht1Start : t1 ≤ tStart := le_max_right _ _
  have htailFacts : ∀ t, tStart ≤ t →
      0 < t ∧ t ≠ 0 ∧ 0 ≤ togesVDelta beta t ∧
        0 ≤ (alpha - 3) * t ^ 2 - 2 * beta * t * (alpha - 2) ∧
        0 ≤ f (u t + (t / 4) • uDot t) - f z ∧ 0 ≤ f (u t) - f z := by
    intro t ht
    have ht0t : t0 ≤ t := le_trans ht0Start ht
    have htpos : 0 < t := lt_of_lt_of_le ht0pos ht0t
    have htne : t ≠ 0 := ne_of_gt htpos
    have ht1t : t1 ≤ t := le_trans ht1Start ht
    have hthreshold : 2 * beta * (alpha - 2) ≤ t * (alpha - 3) := by
      dsimp [t1] at ht1t
      exact (div_le_iff₀ hA3).mp ht1t
    have hcoef : 0 ≤ (alpha - 3) * t ^ 2 - 2 * beta * t * (alpha - 2) := by
      have hmul := mul_le_mul_of_nonneg_left hthreshold (le_of_lt htpos)
      nlinarith
    have hdelta : 0 ≤ togesVDelta beta t := by
      rw [show togesVDelta beta t = t ^ 2 - 2 * beta * t by
        simp [togesVDelta]
        field_simp [htne]]
      have hbeta : 0 ≤ beta := hBeta
      nlinarith [hcoef]
    have hmin : ∀ x : H, f z ≤ f x := by
      simpa [IsMinOn, IsMinFilter] using hMin
    exact ⟨htpos, htne, hdelta, hcoef,
      sub_nonneg.mpr (hmin _), sub_nonneg.mpr (hmin _)⟩
  have hw : ∀ t, tStart ≤ t → HasDerivAt
      (fun s => togesVLyapunovVector u uDot uDdot grad z alpha beta s)
      (-(togesVDelta beta t) • grad (u t + (t / 4) • uDot t)) t := by
    intro t ht
    exact togesVH_w_hasDerivAt u uDot uDdot uDddot grad hess z alpha beta t0 tStart t
      hu huDot huDdot hGradDeriv ht0Start ht (htailFacts t ht).2.1
      hTrajectory
  have hDiss : ∀ t, tStart ≤ t →
      deriv (togesVLyapunov f u uDot uDdot grad z alpha beta) t +
          beta * t ^ 2 * togesVDelta beta t *
            ‖grad (u t + (t / 4) • uDot t)‖ ^ 2 +
          4 * ((alpha - 3) * t ^ 2 - 2 * beta * t * (alpha - 2)) *
            (f (u t + (t / 4) • uDot t) - f z) ≤ 0 := by
    intro t ht
    have htail := htailFacts t ht
    have hE := togesVH_energy_hasDerivAt f u uDot uDdot grad z alpha beta t
      hGradient (hv t ht) (hw t ht) htail.2.1
    rw [hE.deriv]
    have hsupp := togesVH_convex_gradient_le f grad hConvex hGradient
      (u t + (t / 4) • uDot t) z
    have hW : togesVLyapunovVector u uDot uDdot grad z alpha beta t =
        ((4 : ℝ) * t) • ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) +
          (t ^ 2 * beta) • grad (u t + (t / 4) • uDot t) +
          ((4 : ℝ) * alpha) • (u t + (t / 4) • uDot t - z) := by
      simp [togesVLyapunovVector, togesVAuxiliary]
      module
    have hinter : inner ℝ (togesVLyapunovVector u uDot uDdot grad z alpha beta t)
        (-(togesVDelta beta t) • grad (u t + (t / 4) • uDot t)) =
        - (4 * t * togesVDelta beta t *
          inner ℝ (grad (u t + (t / 4) • uDot t))
            ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)) -
        beta * t ^ 2 * togesVDelta beta t *
          inner ℝ (grad (u t + (t / 4) • uDot t))
            (grad (u t + (t / 4) • uDot t)) -
        4 * alpha * togesVDelta beta t *
          inner ℝ (grad (u t + (t / 4) • uDot t))
            (u t + (t / 4) • uDot t - z) := by
      rw [hW]
      simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
        inner_neg_right]
      rw [real_inner_comm ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t)
        (grad (u t + (t / 4) • uDot t))]
      rw [real_inner_comm (u t + (t / 4) • uDot t - z)
        (grad (u t + (t / 4) • uDot t))]
      simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hinter]
    rw [real_inner_self_eq_norm_sq]
    rw [← hsInf] at hsupp
    have hscale : 0 ≤ 4 * alpha * togesVDelta beta t := by
      nlinarith [htail.2.2.1]
    have hsupport := mul_le_mul_of_nonneg_left hsupp hscale
    have hdelta : togesVDelta beta t = t ^ 2 - 2 * beta * t := by
      simp [togesVDelta]
      field_simp [htail.2.1]
    rw [hdelta] at hsupport ⊢
    nlinarith
  have hEantitone : AntitoneOn (togesVLyapunov f u uDot uDdot grad z alpha beta)
      (Set.Ici tStart) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici tStart)
    · intro s hs
      exact (togesVH_energy_hasDerivAt f u uDot uDdot grad z alpha beta s hGradient
        (hv s hs) (hw s hs) (htailFacts s hs).2.1).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : tStart ≤ s := Set.mem_Ici.mp (interior_subset hs)
      exact (togesVH_energy_hasDerivAt f u uDot uDdot grad z alpha beta s hGradient
        (hv s hs') (hw s hs') (htailFacts s hs').2.1).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : tStart ≤ s := Set.mem_Ici.mp (interior_subset hs)
      have hd := hDiss s hs'
      have htail := htailFacts s hs'
      have hterm1 : 0 ≤ beta * s ^ 2 * togesVDelta beta s *
          ‖grad (u s + (s / 4) • uDot s)‖ ^ 2 := by
        exact mul_nonneg (mul_nonneg (mul_nonneg hBeta (sq_nonneg s)) htail.2.2.1)
          (sq_nonneg _)
      have hterm2 : 0 ≤ 4 * ((alpha - 3) * s ^ 2 - 2 * beta * s * (alpha - 2)) *
          (f (u s + (s / 4) • uDot s) - f z) := by
        exact mul_nonneg (mul_nonneg (by norm_num) htail.2.2.2.1) htail.2.2.2.2.1
      linarith
  have hEle : ∀ t, tStart ≤ t →
      togesVLyapunov f u uDot uDdot grad z alpha beta t ≤
        togesVLyapunov f u uDot uDdot grad z alpha beta tStart := by
    intro t ht
    exact hEantitone (by simp) (by simpa using ht) ht
  let C : ℝ := (alpha - 2) * togesVLyapunov f u uDot uDdot grad z alpha beta tStart
  have hAuxRate : ∀ r, tStart ≤ r →
      f (u r + (r / 4) • uDot r) - f z ≤ C / (4 * r ^ 3) := by
    intro t ht
    have htail := htailFacts t ht
    have ht1t : t1 ≤ t := le_trans ht1Start ht
    have hthreshold : 2 * beta * (alpha - 2) ≤ t * (alpha - 3) := by
      dsimp [t1] at ht1t
      exact (div_le_iff₀ hA3).mp ht1t
    have hrecip : 1 / (alpha - 2) ≤ 1 - 2 * beta / t := by
      calc
        1 / (alpha - 2) = (t / (alpha - 2)) / t := by
          field_simp [htail.2.1, ne_of_gt hA2]
        _ ≤ (t - 2 * beta) / t := by
          apply (div_le_div_iff_of_pos_right htail.1).2
          rw [div_le_iff₀ hA2]
          nlinarith [hthreshold]
        _ = 1 - 2 * beta / t := by field_simp [htail.2.1]
    have hdeltaLower : t ^ 2 / (alpha - 2) ≤ togesVDelta beta t := by
      rw [togesVDelta]
      calc
        t ^ 2 / (alpha - 2) = t ^ 2 * (1 / (alpha - 2)) := by ring
        _ ≤ t ^ 2 * (1 - 2 * beta / t) :=
          mul_le_mul_of_nonneg_left hrecip (sq_nonneg t)
    have hEraw := hEle t ht
    rw [togesVLyapunov] at hEraw
    rw [hsInf] at hEraw
    have hsq : 0 ≤ (1 / 2 : ℝ) *
        ‖togesVLyapunovVector u uDot uDdot grad z alpha beta t‖ ^ 2 := by positivity
    have henergy : 4 * t * togesVDelta beta t *
        (f (u t + (t / 4) • uDot t) - f z) ≤
        togesVLyapunov f u uDot uDdot grad z alpha beta tStart := by
      have hraw := le_trans (le_add_of_nonneg_right hsq) hEraw
      simpa [togesVAuxiliary] using hraw
    have hmul : 0 ≤ 4 * t * (f (u t + (t / 4) • uDot t) - f z) := by
      exact mul_nonneg (mul_nonneg (by norm_num) htail.1.le) htail.2.2.2.2.1
    have hscaled := mul_le_mul_of_nonneg_left hdeltaLower hmul
    have haux : 4 * t ^ 3 / (alpha - 2) *
        (f (u t + (t / 4) • uDot t) - f z) ≤
        togesVLyapunov f u uDot uDdot grad z alpha beta tStart := by
      calc
        4 * t ^ 3 / (alpha - 2) *
            (f (u t + (t / 4) • uDot t) - f z) =
            (4 * t * (f (u t + (t / 4) • uDot t) - f z)) *
              (t ^ 2 / (alpha - 2)) := by ring
        _ ≤ (4 * t * (f (u t + (t / 4) • uDot t) - f z)) * togesVDelta beta t := hscaled
        _ = 4 * t * togesVDelta beta t *
            (f (u t + (t / 4) • uDot t) - f z) := by ring
        _ ≤ _ := henergy
    have ht3 : 0 < 4 * t ^ 3 := mul_pos (by norm_num) (pow_pos htail.1 _)
    have haux' : 4 * t ^ 3 * (f (u t + (t / 4) • uDot t) - f z) ≤ C := by
      calc
        4 * t ^ 3 * (f (u t + (t / 4) • uDot t) - f z) =
            (alpha - 2) * (4 * t ^ 3 / (alpha - 2) *
              (f (u t + (t / 4) • uDot t) - f z)) := by
                field_simp [ne_of_gt hA2]
        _ ≤ (alpha - 2) * togesVLyapunov f u uDot uDdot grad z alpha beta tStart :=
          mul_le_mul_of_nonneg_left haux hA2.le
        _ = C := by rfl
    exact (le_div_iff₀ ht3).2 (by simpa [mul_comm] using haux')
  have hCore : ∀ r, tStart ≤ r →
      4 * r ^ 3 * (f (u r) - f z) +
        r ^ 4 * inner ℝ (grad (u r)) (uDot r) ≤ C := by
    intro r hr
    have htail := htailFacts r hr
    have hsupp := togesVH_convex_gradient_le f grad hConvex hGradient
      (u r) (u r + (r / 4) • uDot r)
    have hsupport : 4 * (f (u r) - f z) +
        r * inner ℝ (grad (u r)) (uDot r) ≤
          4 * (f (u r + (r / 4) • uDot r) - f z) := by
      rw [show u r - (u r + (r / 4) • uDot r) = -(r / 4) • uDot r by module,
        real_inner_smul_right] at hsupp
      nlinarith
    have hrate := hAuxRate r hr
    have hCt : 4 * r ^ 3 * (f (u r + (r / 4) • uDot r) - f z) ≤ C := by
      have h4 : 0 < 4 * r ^ 3 := mul_pos (by norm_num) (pow_pos htail.1 3)
      have hscaled := mul_le_mul_of_nonneg_left hrate
        h4.le
      convert hscaled using 1 <;> field_simp [htail.2.1] <;> ring
    have hscaled := mul_le_mul_of_nonneg_left hsupport (pow_nonneg htail.1.le 3)
    nlinarith
  let G : ℝ → ℝ := fun r => r ^ 4 * (f (u r) - f z) - C * r
  have hGderiv : ∀ r, tStart ≤ r → deriv G r ≤ 0 := by
    intro r hr
    have hFderiv : HasDerivAt (fun s => f (u s) - f z)
        (inner ℝ (grad (u r)) (uDot r)) r := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr))).sub_const (f z)
    have hderiv : HasDerivAt G
        (4 * r ^ 3 * (f (u r) - f z) + r ^ 4 * inner ℝ (grad (u r)) (uDot r) - C) r := by
      convert (((hasDerivAt_pow 4 r).mul hFderiv).sub
        ((hasDerivAt_id r).const_mul C)) using 1 <;> ring
    rw [hderiv.deriv]
    linarith [hCore r hr]
  have hGcont : ContinuousOn G (Set.Ici tStart) := by
    intro r hr
    have hFderiv : HasDerivAt (fun s => f (u s) - f z)
        (inner ℝ (grad (u r)) (uDot r)) r := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr))).sub_const (f z)
    exact (((hasDerivAt_pow 4 r).mul hFderiv).sub
      ((hasDerivAt_id r).const_mul C)).continuousAt.continuousWithinAt
  have hGdiff : DifferentiableOn ℝ G (interior (Set.Ici tStart)) := by
    rw [interior_Ici]
    intro r hr
    have hFderiv : HasDerivAt (fun s => f (u s) - f z)
        (inner ℝ (grad (u r)) (uDot r)) r := by
      simpa [innerSL_apply_apply] using
        ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr.le))).sub_const (f z)
    exact (((hasDerivAt_pow 4 r).mul hFderiv).sub
      ((hasDerivAt_id r).const_mul C)).differentiableAt.differentiableWithinAt
  have hGanti : AntitoneOn G (Set.Ici tStart) :=
    antitoneOn_of_deriv_nonpos (convex_Ici tStart) hGcont hGdiff (by
      intro r hr
      exact hGderiv r (by
        rw [interior_Ici] at hr
        exact hr.le))
  intro t ht
  change tStart ≤ t at ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [C, hsInf] using hAuxRate t ht
  · have hGt := hGanti (by simp) (by exact ht) ht
    dsimp [G] at hGt
    have hsecond : f (u t) - f z ≤
        (tStart ^ 4 * (f (u tStart) - f z) - C * tStart) / t ^ 4 + C / t ^ 3 := by
      have hrewrite : C / t ^ 3 = C * t / t ^ 4 := by
        field_simp [ne_of_gt (htailFacts t ht).1]
      rw [hrewrite]
      rw [← add_div]
      apply (le_div_iff₀ (pow_pos (htailFacts t ht).1 4)).2
      nlinarith
    simpa [C, hsInf] using hsecond
  · let Hcorr : ℝ → ℝ := fun r => f (u r) - f z + C / (3 * r ^ 3)
    have hHderiv : ∀ r, tStart ≤ r → deriv Hcorr r ≤ 0 := by
      intro r hr
      have hFderiv : HasDerivAt (fun s => f (u s) - f z)
          (inner ℝ (grad (u r)) (uDot r)) r := by
        simpa [innerSL_apply_apply] using
          ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr))).sub_const (f z)
      have hderiv := hFderiv.add (togesVH_correction_hasDerivAt C r
        (htailFacts r hr).2.1)
      have hd : deriv Hcorr r = inner ℝ (grad (u r)) (uDot r) - C / r ^ 4 := by
        change deriv ((fun s => f (u s) - f z) + fun s => C / (3 * s ^ 3)) r = _
        convert hderiv.deriv using 1 <;> ring
      rw [hd]
      have htail := htailFacts r hr
      have hr4 : 0 < r ^ 4 := pow_pos htail.1 4
      have hinner : r ^ 4 * inner ℝ (grad (u r)) (uDot r) ≤ C := by
        nlinarith [hCore r hr]
      exact sub_nonpos.mpr ((le_div_iff₀ hr4).2 (by simpa [mul_comm] using hinner))
    have hHcont : ContinuousOn Hcorr (Set.Ici tStart) := by
      intro r hr
      have hFderiv : HasDerivAt (fun s => f (u s) - f z)
          (inner ℝ (grad (u r)) (uDot r)) r := by
        simpa [innerSL_apply_apply] using
          ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr))).sub_const (f z)
      exact (hFderiv.add (togesVH_correction_hasDerivAt C r
        (htailFacts r hr).2.1)).continuousAt.continuousWithinAt
    have hHdiff : DifferentiableOn ℝ Hcorr (interior (Set.Ici tStart)) := by
      rw [interior_Ici]
      intro r hr
      have hFderiv : HasDerivAt (fun s => f (u s) - f z)
          (inner ℝ (grad (u r)) (uDot r)) r := by
        simpa [innerSL_apply_apply] using
          ((hGradient (u r)).comp_hasDerivAt r (hu r (le_trans ht0Start hr.le))).sub_const (f z)
      exact (hFderiv.add (togesVH_correction_hasDerivAt C r
        (htailFacts r hr.le).2.1)).differentiableAt.differentiableWithinAt
    have hHanti : AntitoneOn Hcorr (Set.Ici tStart) :=
      antitoneOn_of_deriv_nonpos (convex_Ici tStart) hHcont hHdiff (by
        intro r hr
        exact hHderiv r (by
          rw [interior_Ici] at hr
          exact hr.le))
    intro x hx y hy hxy
    have h := hHanti hx hy hxy
    dsimp [Hcorr] at h
    linarith
  · intro hBetaPos
    let E : ℝ → ℝ := togesVLyapunov f u uDot uDdot grad z alpha beta
    let D : ℝ → ℝ := fun r => beta * r ^ 2 * togesVDelta beta r *
      ‖grad (u r + (r / 4) • uDot r)‖ ^ 2
    let p : ℝ → ℝ := fun r =>
      4 * r * togesVDelta beta r *
          inner ℝ (grad (u r + (r / 4) • uDot r))
            ((5 / 4 : ℝ) • uDot r + (r / 4) • uDdot r) +
        4 * (togesVDelta beta r + r * (2 * r - 2 * beta)) *
          (f (u r + (r / 4) • uDot r) - sInf (Set.range f)) +
        inner ℝ (togesVLyapunovVector u uDot uDdot grad z alpha beta r)
          (-(togesVDelta beta r) • grad (u r + (r / 4) • uDot r))
    have hEAt : ∀ r, tStart ≤ r → HasDerivAt E (p r) r := by
      intro r hr
      exact togesVH_energy_hasDerivAt f u uDot uDdot grad z alpha beta r hGradient
        (hv r hr) (hw r hr) (htailFacts r hr).2.1
    have hDnonneg : ∀ r, tStart ≤ r → 0 ≤ D r := by
      intro r hr
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hBeta (sq_nonneg r))
          (htailFacts r hr).2.2.1) (sq_nonneg _)
    have hDcont : ∀ T, tStart ≤ T → ContinuousOn D (Set.Icc tStart T) := by
      intro T hT r hr
      have hgrad := (hGradDeriv r (le_trans ht0Start hr.1)).continuousAt
      have hdelta := (togesVH_delta_hasDerivAt beta r
        (htailFacts r hr.1).2.1).continuousAt
      exact (((continuousAt_const.mul ((hasDerivAt_id r).pow 2).continuousAt).mul hdelta).mul
        (hgrad.norm.pow 2)).continuousWithinAt
    have hDp : ∀ r, tStart ≤ r → D r ≤ -p r := by
      intro r hr
      have hd := hDiss r hr
      rw [(hEAt r hr).deriv] at hd
      have hcoef : 0 ≤ (alpha - 3) * r ^ 2 - 2 * beta * r * (alpha - 2) :=
        (htailFacts r hr).2.2.2.1
      have hvalue : 0 ≤ f (u r + (r / 4) • uDot r) - f z :=
        (htailFacts r hr).2.2.2.2.1
      have hq : 0 ≤ 4 * ((alpha - 3) * r ^ 2 - 2 * beta * r * (alpha - 2)) *
          (f (u r + (r / 4) • uDot r) - f z) := by positivity
      change p r + D r + _ ≤ 0 at hd
      linarith
    have hPcont : ∀ T, tStart ≤ T → ContinuousOn p (Set.Icc tStart T) := by
      intro T hT r hr
      have hu' := (hu r (le_trans ht0Start hr.1)).continuousAt
      have huDot' := (huDot r (le_trans ht0Start hr.1)).continuousAt
      have huDdot' := (huDdot r (le_trans ht0Start hr.1)).continuousAt
      have hv' := (hv r hr.1).continuousAt
      have hvDot' : ContinuousAt
          (fun s => (5 / 4 : ℝ) • uDot s + (s / 4) • uDdot s) r := by
        exact (continuousAt_const.smul huDot').add
          (((hasDerivAt_id r).div_const 4).continuousAt.smul huDdot')
      have hgrad' := (hGradDeriv r (le_trans ht0Start hr.1)).continuousAt
      have hf' : ContinuousAt (fun s => f (u s + (s / 4) • uDot s) -
          sInf (Set.range f)) r := by
        exact ((hGradient (u r + (r / 4) • uDot r)).comp_hasDerivAt r (hv r hr.1)).continuousAt
          |>.sub continuousAt_const
      have hdelta' := (togesVH_delta_hasDerivAt beta r
        (htailFacts r hr.1).2.1).continuousAt
      have hw' := (hw r hr.1).continuousAt
      have hcoeff : ContinuousAt
          (fun s => togesVDelta beta s + s * (2 * s - 2 * beta)) r := by
        exact hdelta'.add ((hasDerivAt_id r).continuousAt.mul
          ((((hasDerivAt_id r).const_mul 2).continuousAt).sub
            (hasDerivAt_const r (2 * beta)).continuousAt))
      have hfirst : ContinuousAt (fun s => 4 * s * togesVDelta beta s *
          inner ℝ (grad (u s + (s / 4) • uDot s))
            ((5 / 4 : ℝ) • uDot s + (s / 4) • uDdot s)) r := by
        exact ((continuousAt_const.mul (hasDerivAt_id r).continuousAt).mul hdelta').mul
          (hgrad'.inner hvDot')
      have hsecond : ContinuousAt (fun s => 4 *
          (togesVDelta beta s + s * (2 * s - 2 * beta)) *
          (f (u s + (s / 4) • uDot s) - sInf (Set.range f))) r := by
        exact (continuousAt_const.mul hcoeff).mul hf'
      have hthird : ContinuousAt (fun s =>
          inner ℝ (togesVLyapunovVector u uDot uDdot grad z alpha beta s)
            (-(togesVDelta beta s) • grad (u s + (s / 4) • uDot s))) r := by
        simpa [neg_smul] using hw'.inner (hdelta'.smul hgrad').neg
      simpa [p] using ((hfirst.add hsecond).add hthird).continuousWithinAt
    have hEnonneg : ∀ r, tStart ≤ r → 0 ≤ E r := by
      intro r hr
      have htail := htailFacts r hr
      have hfirst : 0 ≤ 4 * r * togesVDelta beta r *
          (f (u r + (r / 4) • uDot r) - f z) := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) htail.1.le)
          htail.2.2.1) htail.2.2.2.2.1
      have hsecond : 0 ≤ (1 / 2 : ℝ) *
          ‖togesVLyapunovVector u uDot uDdot grad z alpha beta r‖ ^ 2 := by positivity
      change 0 ≤ 4 * r * togesVDelta beta r *
        (f (u r + (r / 4) • uDot r) - sInf (Set.range f)) + _
      rw [hsInf]
      linarith
    have hDcompact : ∀ T, tStart ≤ T → (∫ r in tStart..T, D r) ≤ E tStart := by
      intro T hT
      have hDint : IntervalIntegrable D MeasureTheory.volume tStart T :=
        (hDcont T hT).intervalIntegrable_of_Icc hT
      have hPint : IntervalIntegrable p MeasureTheory.volume tStart T :=
        (hPcont T hT).intervalIntegrable_of_Icc hT
      have hmono := intervalIntegral.integral_mono_on hT hDint hPint.neg (by
        intro r hr
        exact hDp r hr.1)
      change (∫ r in tStart..T, D r) ≤ (∫ r in tStart..T, -p r) at hmono
      rw [intervalIntegral.integral_neg] at hmono
      have hFTC : (∫ r in tStart..T, p r) = E T - E tStart := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro r hr
          rw [Set.uIcc_of_le hT] at hr
          exact hEAt r hr.1
        · exact hPint
      rw [hFTC] at hmono
      linarith [hEnonneg T hT]
    let g : ℝ → ℝ := fun r => r ^ 4 * ‖grad (u r + (r / 4) • uDot r)‖ ^ 2
    have hgcont : ∀ T, tStart ≤ T → ContinuousOn g (Set.Icc tStart T) := by
      intro T hT r hr
      have hgrad := (hGradDeriv r (le_trans ht0Start hr.1)).continuousAt
      exact (((hasDerivAt_id r).pow 4).continuousAt.mul (hgrad.norm.pow 2)).continuousWithinAt
    have hgcompact : ∀ T, tStart ≤ T → (∫ r in tStart..T, g r) ≤
        (alpha - 2) * E tStart / beta := by
      intro T hT
      have hGint : IntervalIntegrable g MeasureTheory.volume tStart T :=
        (hgcont T hT).intervalIntegrable_of_Icc hT
      have hDint : IntervalIntegrable D MeasureTheory.volume tStart T :=
        (hDcont T hT).intervalIntegrable_of_Icc hT
      have hpoint : ∀ r, r ∈ Set.Icc tStart T → beta * g r ≤ (alpha - 2) * D r := by
        intro r hr
        have htail := htailFacts r hr.1
        have ht1r : t1 ≤ r := le_trans ht1Start hr.1
        have hthreshold : 2 * beta * (alpha - 2) ≤ r * (alpha - 3) := by
          dsimp [t1] at ht1r
          exact (div_le_iff₀ hA3).mp ht1r
        have hlower : r ^ 2 / (alpha - 2) ≤ togesVDelta beta r := by
          rw [togesVDelta]
          have hrecip : 1 / (alpha - 2) ≤ 1 - 2 * beta / r := by
            calc
              1 / (alpha - 2) = (r / (alpha - 2)) / r := by
                field_simp [htail.2.1, ne_of_gt hA2]
              _ ≤ (r - 2 * beta) / r := by
                apply (div_le_div_iff_of_pos_right htail.1).2
                rw [div_le_iff₀ hA2]
                nlinarith [hthreshold]
              _ = 1 - 2 * beta / r := by field_simp [htail.2.1]
          calc
            r ^ 2 / (alpha - 2) = r ^ 2 * (1 / (alpha - 2)) := by ring
            _ ≤ r ^ 2 * (1 - 2 * beta / r) :=
              mul_le_mul_of_nonneg_left hrecip (sq_nonneg r)
        let q : ℝ := ‖grad (u r + (r / 4) • uDot r)‖ ^ 2
        have hq : 0 ≤ q := by
          dsimp [q]
          exact sq_nonneg _
        have hcompare := togesVH_weighted_gradient_compare alpha beta r q
          (togesVDelta beta r) hA2 hBeta htail.1.le hq hlower
        simpa only [g, D, q] using hcompare
      have hIntegrated := intervalIntegral.integral_mono_on hT
        (hGint.const_mul beta) (hDint.const_mul (alpha - 2)) (by
          intro r hr
          exact hpoint r hr)
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul] at hIntegrated
      have hDscaled : (alpha - 2) * (∫ r in tStart..T, D r) ≤
          (alpha - 2) * E tStart := by
        exact mul_le_mul_of_nonneg_left (hDcompact T hT) hA2.le
      have hbetaScaled : beta * (∫ r in tStart..T, g r) ≤
          (alpha - 2) * E tStart := le_trans hIntegrated hDscaled
      exact (le_div_iff₀ hBetaPos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbetaScaled)
    have hgnonneg : ∀ r, tStart ≤ r → 0 ≤ g r := by
      intro r hr
      exact mul_nonneg (pow_nonneg (htailFacts r hr).1.le 4) (sq_nonneg _)
    rcases togesVH_integrableOn_Ici_of_nonneg_compact_integral_bound hgcont hgnonneg
      ((alpha - 2) * E tStart / beta) hgcompact with ⟨hgi, hgb⟩
    exact hgb
