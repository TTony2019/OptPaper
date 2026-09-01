import Mathlib

/-!
# Integral analysis on the half-line

Real-analysis facts about integrable functions on `[0, ∞)`.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_thm_8).
-/


/-- A nonnegative uniformly continuous `L^p` function vanishes at infinity. -/
theorem integrable_uniformly_continuous_tendsto_zero (g : ℝ → ℝ) (p : ℝ)
    (hg : ∀ t, 0 ≤ g t) (hp : 1 ≤ p) (huc : UniformContinuous g)
    (hint : MeasureTheory.IntegrableOn (fun t => (g t) ^ p) (Set.Ici 0)) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨eps, heps, hbad⟩
  have htail : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ici (n : ℝ), (g x) ^ p)
      Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => (g x) ^ p) (fun n : ℕ => measurableSet_Ici)
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
  obtain ⟨delta, hdelta, hdelta_prop⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (eps / 2) (by linarith)
  have hp0 : 0 ≤ p := by linarith
  have hc : 0 < (eps / 2) ^ p * (delta / 2) := by
    apply mul_pos
    · exact Real.rpow_pos_of_pos (by linarith) _
    · linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) _ hc
  obtain ⟨u, huN, hubad⟩ := hbad (N : ℝ)
  have hub : eps ≤ g u := by
    simpa [Real.dist_eq, abs_of_nonneg (hg u)] using hubad
  have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg N) huN
  have hlow : ∀ x ∈ Set.Ioc u (u + delta / 2), (eps / 2) ^ p ≤ (g x) ^ p := by
    intro x hx
    have hxu : |x - u| < delta := by
      rw [abs_of_nonneg (le_of_lt (sub_pos.mpr hx.1))]
      linarith [hx.2, hdelta]
    have hgx : eps / 2 < g x := by
      have hclose : dist (g x) (g u) < eps / 2 := by
        exact hdelta_prop (by simpa [Real.dist_eq] using hxu)
      have htri : g u ≤ |g x - g u| + g x := by
        calc
          g u = |g u| := (abs_of_nonneg (hg u)).symm
          _ ≤ |g u - g x| + |g x| := by
            simpa using abs_sub_le (g u) (g x) 0
          _ = |g x - g u| + g x := by rw [abs_sub_comm, abs_of_nonneg (hg x)]
      rw [Real.dist_eq] at hclose
      linarith
    exact Real.rpow_le_rpow (by linarith) hgx.le hp0
  have hint_lower : (eps / 2) ^ p * (delta / 2) ≤
      ∫ x in Set.Ioc u (u + delta / 2), (g x) ^ p := by
    calc
      (eps / 2) ^ p * (delta / 2) =
          ∫ x in Set.Ioc u (u + delta / 2), (eps / 2) ^ p := by
            rw [MeasureTheory.integral_const]
            simp [max_eq_left (by linarith : 0 ≤ delta / 2)]
            ring
      _ ≤ ∫ x in Set.Ioc u (u + delta / 2), (g x) ^ p := by
        apply MeasureTheory.integral_mono_ae
        · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact hint.mono_set (by
            intro x hx
            exact le_trans hu0 (le_of_lt hx.1))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hlow x hx
  have hinter : Set.Ioc u (u + delta / 2) ⊆ Set.Ici (N : ℝ) := by
    intro x hx
    exact le_trans huN (le_of_lt hx.1)
  have hint_upper : ∫ x in Set.Ioc u (u + delta / 2), (g x) ^ p ≤
      ∫ x in Set.Ici (N : ℝ), (g x) ^ p := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hint.mono_set (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg N))
    · filter_upwards with x
      exact Real.rpow_nonneg (hg x) _
    · exact hinter.eventuallyLE
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), (g x) ^ p := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact Real.rpow_nonneg (hg x) _
  have hN'' : ∫ x in Set.Ici (N : ℝ), (g x) ^ p <
      (eps / 2) ^ p * (delta / 2) := by
    simpa [Real.dist_eq, abs_of_nonneg htail_nonneg] using hN N le_rfl
  linarith

/-! Promoted from `Attouch_CONTINUOUS_NEWTON_LIKE_METHODS_FEATURING_INERTIA_AND_VARIABLE_MASS_2024`
(items/rem_3, items/cor_1). -/

/-- Remark 4.4 in `Attouch_CONTINUOUS_NEWTON_LIKE_METHODS_FEATURING_INERTIA_AND_VARIABLE_MASS_2024`:
monotonicity and nonnegativity bound the total variation of `α` by its initial value. -/
theorem setIntegral_Ici_abs_deriv_le_initial_of_antitone_nonneg
    (α : ℝ → ℝ) (hanti : Antitone α) (hnonneg : ∀ t, 0 ≤ α t)
    (hdiff : Differentiable ℝ α)
    (hderiv_bdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |deriv α t| ≤ C) :
    (∃ C : ℝ, ∀ t, 0 ≤ t → |deriv α t| ≤ C) ∧
      MeasureTheory.IntegrableOn (fun s => |deriv α s|) (Set.Ici 0) ∧
      ∫ s in Set.Ici (0 : ℝ), |deriv α s| ≤ α 0 := by
  rcases hderiv_bdd with ⟨C, hC⟩
  refine ⟨⟨C, hC⟩, ?_⟩
  let F : ℝ → ℝ := fun t => α (max t 0)
  have hFanti : Antitone F := by
    intro s t hst
    exact hanti (max_le_max_right _ hst)
  have hFbelow : BddBelow (Set.range F) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hnonneg _
  let L : ℝ := ⨅ t, F t
  have hFlim : Filter.Tendsto F Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hFanti hFbelow
  have hlim : Filter.Tendsto α Filter.atTop (nhds L) := by
    apply hFlim.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [F, max_eq_left ht]
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt α (deriv α x) x := by
    intro x _
    exact (hdiff x).hasDerivAt
  have hderiv_nonpos : ∀ x ∈ Set.Ioi (0 : ℝ), deriv α x ≤ 0 := by
    intro x _
    exact hanti.deriv_nonpos
  have hderiv_int : MeasureTheory.IntegrableOn (deriv α) (Set.Ioi 0) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' hderiv hderiv_nonpos hlim
  have habs : (fun s => |deriv α s|) = fun s => -deriv α s := by
    funext s
    exact abs_of_nonpos hanti.deriv_nonpos
  have habs_int_ioi : MeasureTheory.IntegrableOn (fun s => |deriv α s|) (Set.Ioi 0) := by
    rw [habs]
    exact hderiv_int.neg
  have habs_int : MeasureTheory.IntegrableOn (fun s => |deriv α s|) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr habs_int_ioi
  refine ⟨habs_int, ?_⟩
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact le_ciInf fun t => hnonneg _
  have hftc : ∫ s in Set.Ioi (0 : ℝ), deriv α s = L - α 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hderiv_nonpos hlim
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, habs, MeasureTheory.integral_neg, hftc]
  linarith

/-- Exponential-kernel convolution bound (Corollary 3.6 in
`Attouch_CONTINUOUS_NEWTON_LIKE_METHODS_FEATURING_INERTIA_AND_VARIABLE_MASS_2024`):
for `ε : ℝ → ℝ` positive on `[0, ∞)` with `|deriv ε s| ≤ c₁ * ε s` on `[0, ∞)`,
`0 < β` and `c₁ < 2 / β`, the convolution of the exponential kernel with the
square root of `ε` is bounded by `(2 * β / (2 - c₁ * β)) * Real.sqrt (ε t)`:

  ∫ s in (0)..t, Real.exp ((s - t) / β) * Real.sqrt (ε s) ≤
    (2 * β / (2 - c₁ * β)) * Real.sqrt (ε t)

for every `t ≥ 0`. -/
theorem exponential_sqrt_epsilon_convolution_le
    (ε : ℝ → ℝ) (β c₁ : ℝ)
    (hεpos : ∀ s : ℝ, 0 ≤ s → 0 < ε s)
    (hεsmooth : ContDiffOn ℝ 2 ε (Set.Ici 0))
    (hbound : ∀ s : ℝ, 0 ≤ s → |deriv ε s| ≤ c₁ * ε s)
    (hβ : 0 < β) (hc₁ : c₁ < 2 / β) :
    ∀ t : ℝ, 0 ≤ t →
      ∫ s in (0 : ℝ)..t, Real.exp ((s - t) / β) * Real.sqrt (ε s) ≤
        (2 * β / (2 - c₁ * β)) * Real.sqrt (ε t) := by
  intro t ht
  have hc₁nonneg : 0 ≤ c₁ := by
    have hεzero := hεpos 0 (by norm_num)
    have hboundzero := hbound 0 (by norm_num)
    nlinarith [abs_nonneg (deriv ε 0)]
  have hcβ : c₁ * β < 2 := (lt_div_iff₀ hβ).mp hc₁
  have hdenom : 0 < 2 - c₁ * β := by linarith
  let q : ℝ → ℝ := fun s => derivWithin ε (Set.Ici 0) s / (2 * Real.sqrt (ε s))
  have hεcont : ContinuousOn ε (Set.Icc 0 t) :=
    hεsmooth.continuousOn.mono (by intro s hs; exact hs.1)
  have hqcont : ContinuousOn q (Set.Icc 0 t) := by
    have hderivcont : ContinuousOn (derivWithin ε (Set.Ici 0)) (Set.Icc 0 t) :=
      (hεsmooth.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)).mono
        (by intro s hs; exact hs.1)
    apply hderivcont.div
    · simpa [Function.comp_def] using
        (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hεcont))
    · intro s hs
      have hspos : 0 < ε s := hεpos s hs.1
      positivity
  have hqint : IntervalIntegrable q MeasureTheory.volume 0 t :=
    by
      have hqcont' : ContinuousOn q (Set.uIcc 0 t) := by
        simpa [Set.uIcc_of_le ht] using hqcont
      exact hqcont'.intervalIntegrable
  have hvderiv : ∀ s ∈ Set.Ioo (min (0 : ℝ) t) (max (0 : ℝ) t),
      HasDerivAt (fun r => Real.sqrt (ε r)) (q s) s := by
    intro s hs
    have hs0 : 0 < s := by simpa [min_eq_left ht, max_eq_right ht] using hs.1
    have hεderiv : HasDerivAt ε (deriv ε s) s :=
      (hεsmooth.contDiffAt (Ici_mem_nhds hs0)).differentiableAt (by norm_num) |>.hasDerivAt
    have hwithin : derivWithin ε (Set.Ici 0) s = deriv ε s := by
      simp only [derivWithin, deriv, fderivWithin_of_mem_nhds (Ici_mem_nhds hs0)]
    simpa [q, hwithin] using hεderiv.sqrt (ne_of_gt (hεpos s hs0.le))
  let u : ℝ → ℝ := fun s => β * Real.exp (s / β)
  let v : ℝ → ℝ := fun s => Real.sqrt (ε s)
  have hucont : ContinuousOn u (Set.uIcc 0 t) :=
    (continuous_const.mul (Real.continuous_exp.comp
      ((continuous_id.div continuous_const) (fun _ => hβ.ne')))).continuousOn
  have hvcont : ContinuousOn v (Set.uIcc 0 t) := by
    rw [Set.uIcc_of_le ht]
    simpa [v, Function.comp_def] using Real.continuous_sqrt.comp_continuousOn hεcont
  have huprime : ∀ s ∈ Set.Ioo (min (0 : ℝ) t) (max (0 : ℝ) t),
      HasDerivAt u (Real.exp (s / β)) s := by
    intro s hs
    dsimp [u]
    convert (hasDerivAt_const s β).mul
      ((Real.hasDerivAt_exp (s / β)).comp s ((hasDerivAt_id s).div_const β)) using 1
    all_goals
      field_simp [hβ.ne']
      ring
  have huprimeint : IntervalIntegrable (fun s => Real.exp (s / β))
      MeasureTheory.volume 0 t :=
    by
      simpa [Function.comp_def] using
        (Real.continuous_exp.comp ((continuous_id.div continuous_const)
          (fun _ => hβ.ne'))).intervalIntegrable 0 t
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hucont hvcont huprime hvderiv huprimeint hqint
  have hnegint : IntervalIntegrable (fun s => -(u s * q s)) MeasureTheory.volume 0 t := by
    apply IntervalIntegrable.neg
    rw [show (fun s => u s * q s) = u * q by rfl]
    have hqcont' : ContinuousOn q (Set.uIcc 0 t) := by
      simpa [Set.uIcc_of_le ht] using hqcont
    exact hucont.intervalIntegrable.mul_continuousOn hqcont'
  have hmajorcont : ContinuousOn (fun s => (c₁ * β / 2) * Real.exp (s / β) * Real.sqrt (ε s))
      (Set.uIcc 0 t) := by
    rw [Set.uIcc_of_le ht]
    exact (continuousOn_const.mul
      ((Real.continuous_exp.comp ((continuous_id.div continuous_const)
        (fun _ => hβ.ne'))).continuousOn)).mul
        (Real.continuous_sqrt.comp_continuousOn hεcont)
  have hnegpoint : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      -(u s * q s) ≤ (c₁ * β / 2) * Real.exp (s / β) * Real.sqrt (ε s) := by
    intro s hs
    have hspos : 0 < s := hs.1
    have hεs : 0 < ε s := hεpos s hspos.le
    have hsqrt : 0 < Real.sqrt (ε s) := Real.sqrt_pos.2 hεs
    have hwithin : derivWithin ε (Set.Ici 0) s = deriv ε s := by
      simp only [derivWithin, deriv, fderivWithin_of_mem_nhds (Ici_mem_nhds hspos)]
    have hderiv : -deriv ε s ≤ c₁ * ε s :=
      le_trans (neg_le_abs (deriv ε s)) (hbound s hspos.le)
    have hsq : (Real.sqrt (ε s)) ^ 2 = ε s := Real.sq_sqrt hεs.le
    dsimp [u, q]
    rw [hwithin]
    have hexp : 0 < Real.exp (s / β) := Real.exp_pos _
    calc
      -(β * Real.exp (s / β) * (deriv ε s / (2 * Real.sqrt (ε s)))) =
          (β * Real.exp (s / β) / (2 * Real.sqrt (ε s))) * (-deriv ε s) := by ring
      _ ≤ (β * Real.exp (s / β) / (2 * Real.sqrt (ε s))) * (c₁ * ε s) := by
        gcongr
      _ = c₁ * β / 2 * Real.exp (s / β) * Real.sqrt (ε s) := by
        field_simp [hsqrt.ne']
        all_goals nlinarith [hsq]
  have hmajorint : IntervalIntegrable (fun s => (c₁ * β / 2) * Real.exp (s / β) * Real.sqrt (ε s))
      MeasureTheory.volume 0 t := hmajorcont.intervalIntegrable
  have hnegmono := intervalIntegral.integral_mono_on_of_le_Ioo ht hnegint hmajorint hnegpoint
  have hnegmajor : ∫ s in (0 : ℝ)..t, -(u s * q s) ≤
      (c₁ * β / 2) * ∫ s in (0 : ℝ)..t, Real.exp (s / β) * Real.sqrt (ε s) := by
    calc
      (∫ s in (0 : ℝ)..t, -(u s * q s)) ≤
          ∫ s in (0 : ℝ)..t, (c₁ * β / 2) * Real.exp (s / β) * Real.sqrt (ε s) := hnegmono
      _ = (c₁ * β / 2) * ∫ s in (0 : ℝ)..t, Real.exp (s / β) * Real.sqrt (ε s) := by
        rw [show (fun s => (c₁ * β / 2) * Real.exp (s / β) * Real.sqrt (ε s)) =
          fun s => (c₁ * β / 2) * (Real.exp (s / β) * Real.sqrt (ε s)) by
            funext s; ring]
        rw [intervalIntegral.integral_const_mul]
  let J : ℝ := ∫ s in (0 : ℝ)..t, Real.exp (s / β) * Real.sqrt (ε s)
  have hibp' : (∫ s in (0 : ℝ)..t, u s * q s) =
      u t * v t - u 0 * v 0 - J := by
    simpa [J, v] using hibp
  have hJ_eq : J = u t * v t - u 0 * v 0 +
      ∫ s in (0 : ℝ)..t, -(u s * q s) := by
    rw [intervalIntegral.integral_neg]
    linarith [hibp']
  have hinit : 0 ≤ u 0 * v 0 := by
    dsimp [u, v]
    positivity
  have hJ_bound : J ≤ β * Real.exp (t / β) * Real.sqrt (ε t) +
      (c₁ * β / 2) * J := by
    calc
      J = u t * v t - u 0 * v 0 +
          ∫ s in (0 : ℝ)..t, -(u s * q s) := hJ_eq
      _ ≤ u t * v t + (c₁ * β / 2) * J := by
        linarith [hnegmajor]
      _ = β * Real.exp (t / β) * Real.sqrt (ε t) +
          (c₁ * β / 2) * J := rfl
  have hJ_final : J ≤ (2 * β / (2 - c₁ * β)) *
      Real.exp (t / β) * Real.sqrt (ε t) := by
    rw [show (2 * β / (2 - c₁ * β)) * Real.exp (t / β) * Real.sqrt (ε t) =
      (2 * β * Real.exp (t / β) * Real.sqrt (ε t)) / (2 - c₁ * β) by ring]
    apply (le_div_iff₀ hdenom).mpr
    nlinarith [hJ_bound]
  have hkernel : (∫ s in (0 : ℝ)..t,
      Real.exp ((s - t) / β) * Real.sqrt (ε s)) =
      Real.exp (-t / β) * J := by
    calc
      (∫ s in (0 : ℝ)..t, Real.exp ((s - t) / β) * Real.sqrt (ε s)) =
          ∫ s in (0 : ℝ)..t,
            Real.exp (-t / β) *
              (Real.exp (s / β) * Real.sqrt (ε s)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            change Real.exp ((s - t) / β) * Real.sqrt (ε s) =
              Real.exp (-t / β) * (Real.exp (s / β) * Real.sqrt (ε s))
            have hexp : (s - t) / β = -t / β + s / β := by ring
            rw [hexp, Real.exp_add]
            ring
      _ = Real.exp (-t / β) * J := by
        rw [intervalIntegral.integral_const_mul]
  have hexp_cancel : Real.exp (-t / β) * Real.exp (t / β) = 1 := by
    rw [← Real.exp_add]
    have : -t / β + t / β = 0 := by ring
    rw [this, Real.exp_zero]
  rw [hkernel]
  calc
    Real.exp (-t / β) * J ≤ Real.exp (-t / β) *
        ((2 * β / (2 - c₁ * β)) * Real.exp (t / β) * Real.sqrt (ε t)) :=
      mul_le_mul_of_nonneg_left hJ_final (Real.exp_pos _).le
    _ = (2 * β / (2 - c₁ * β)) * Real.sqrt (ε t) := by
      calc
        Real.exp (-t / β) *
            ((2 * β / (2 - c₁ * β)) * Real.exp (t / β) * Real.sqrt (ε t)) =
            (2 * β / (2 - c₁ * β)) *
              (Real.exp (-t / β) * Real.exp (t / β)) * Real.sqrt (ε t) := by ring
        _ = (2 * β / (2 - c₁ * β)) * Real.sqrt (ε t) := by
          rw [hexp_cancel]
          ring
