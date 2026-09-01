import Mathlib

namespace AbbasDynamical2015

open MeasureTheory Filter

private theorem increment_le_interval_integral
    (F G : ℝ → ℝ) (r : ENNReal) (hr : 1 ≤ r)
    (hF_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval F 0 b)
    (hG : MemLp G r volume)
    (hderiv : ∀ᵐ t ∂volume, deriv F t ≤ G t) :
    ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → F b - F a ≤ ∫ x in a..b, G x := by
  intro a b ha hab
  by_cases hb : b = 0
  · subst b
    have : a = 0 := le_antisymm hab ha
    subst a
    simp
  have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
  have hGint : IntegrableOn G (Set.Icc a b) :=
    (hG.locallyIntegrable hr).integrableOn_isCompact isCompact_Icc
  have hle : deriv F ≤ᵐ[volume.restrict (Set.Icc a b)] G :=
    ae_restrict_of_ae hderiv
  have hacab : AbsolutelyContinuousOnInterval F a b := (hF_ac b hbpos).mono (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (ha.trans hab)]
    exact Set.Icc_subset_Icc ha le_rfl)
  rw [← hacab.integral_deriv_eq_sub]
  exact intervalIntegral.integral_mono_ae_restrict hab hacab.intervalIntegrable_deriv
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hGint) hle

private theorem ae_upper_bound_of_memLp_top {g : ℝ → ℝ}
    (hg : MemLp g ⊤ (volume.restrict (Set.Ioi 0))) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), g t ≤ C) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hfin : eLpNormEssSup g μ < ⊤ := by
    simpa [μ, eLpNorm_exponent_top] using hg.eLpNorm_lt_top
  refine ⟨(eLpNormEssSup g μ).toReal + 1, by positivity, ?_⟩
  filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with t ht
  have hreal : |g t| ≤ (eLpNormEssSup g μ).toReal := by
    simpa only [← ENNReal.ofReal_le_iff_le_toReal hfin.ne, ← Real.enorm_eq_ofReal_abs] using ht
  linarith [le_abs_self (g t)]

private theorem integral_interval_le_of_memLp_top {g : ℝ → ℝ} {C a b : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), g t ≤ C)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ t in Set.Icc a b, g t ≤ C * (b - a) := by
  by_cases hg : IntegrableOn g (Set.Icc a b)
  · have hboundIoc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), g t ≤ C :=
      ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_of_le_of_lt ha hx.1) hbound
    have hboundIcc : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), g t ≤ C :=
      ae_restrict_of_ae_eq_of_ae_restrict Ioc_ae_eq_Icc hboundIoc
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) := by
      simp [Real.volume_Icc]
    calc
      ∫ t in Set.Icc a b, g t ≤ ∫ _t in Set.Icc a b, C :=
        integral_mono_ae hg hconst hboundIcc
      _ = C * (b - a) := by
        rw [integral_const]
        simp [hab]
        ring
  · rw [integral_undef hg]
    nlinarith

private theorem integrable_tail_indicator_tendsto_zero {f : ℝ → ℝ} {μ : Measure ℝ}
    (hf : Integrable f μ) :
    Tendsto (fun T => ∫ x, (Set.Ioi T).indicator f x ∂μ) atTop (nhds 0) := by
  have h : Tendsto (fun T => ∫ x, (Set.Ioi T).indicator f x ∂μ)
      atTop (nhds (∫ x, (0 : ℝ) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (ι := ℝ) (l := atTop) (F := fun T x => (Set.Ioi T).indicator f x)
      (f := fun _ => 0) (fun x => |f x|)
      (Eventually.of_forall fun T => hf.aestronglyMeasurable.indicator measurableSet_Ioi)
      (Eventually.of_forall fun T => Eventually.of_forall fun x => by
        rw [norm_indicator_eq_indicator_norm]
        have hle := Set.indicator_le_indicator_of_subset (s := Set.Ioi T) (t := Set.univ)
          (f := fun y => ‖f y‖) (fun _ _ => trivial) (fun y => norm_nonneg (f y))
        simpa only [Set.indicator_univ, Real.norm_eq_abs] using hle x)
      (by simpa only [Real.norm_eq_abs] using hf.norm)
      (Eventually.of_forall fun x => Filter.Tendsto.congr'
        (by filter_upwards [eventually_ge_atTop x] with T hT
            simp [not_lt_of_ge hT]) tendsto_const_nhds)
  simpa using h

private theorem setIntegral_restrict_Ioi_eq_setIntegral_volume {f : ℝ → ℝ} {s : Set ℝ}
    (hs : s ⊆ Set.Ioi 0) :
    (∫ x in s, f x ∂(volume.restrict (Set.Ioi 0))) = ∫ x in s, f x := by
  rw [Measure.restrict_restrict_of_subset hs]

private theorem integral_interval_eventually_le_of_memLp_one {g : ℝ → ℝ}
    (hg : MemLp g 1 (volume.restrict (Set.Ioi 0)))
    {eta L : ℝ} (heta : 0 < eta) (_hL : 0 < L) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ {a b : ℝ}, T ≤ a → a ≤ b → b - a ≤ L →
      ∫ t in Set.Icc a b, g t ≤ eta := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have habs : Integrable (fun x => |g x|) μ :=
    (memLp_one_iff_integrable.mp hg).norm
  have htail := integrable_tail_indicator_tendsto_zero habs
  rcases (Metric.tendsto_atTop.mp htail eta heta) with ⟨R, hR⟩
  let T : ℝ := max R 0 + 2
  refine ⟨T, by dsimp [T]; linarith [le_max_right R 0], ?_⟩
  intro a b ha hab hlength
  have hTa : T ≤ a := ha
  have ha_pos : 0 < a := by
    dsimp [T] at hTa
    linarith [le_max_right R 0]
  let V : ℝ := T - 1
  have hVR : R ≤ V := by
    dsimp [V, T]
    linarith [le_max_left R 0]
  have hVpos : 0 < V := by
    dsimp [V, T]
    linarith [le_max_right R 0]
  have hIa : Set.Icc a b ⊆ Set.Ioi 0 :=
    fun x hx => lt_of_lt_of_le ha_pos hx.1
  have htail_pos : 0 ≤ ∫ x in Set.Ioi V, |g x| :=
    integral_nonneg (fun x => abs_nonneg (g x))
  have htail_lt : ∫ x in Set.Ioi V, |g x| < eta := by
    have hraw := hR V hVR
    change dist (∫ x, (Set.Ioi V).indicator (fun x => |g x|) x ∂μ) 0 < eta at hraw
    rw [integral_indicator measurableSet_Ioi,
      setIntegral_restrict_Ioi_eq_setIntegral_volume (f := fun x => |g x|)
        (by intro x hx; exact lt_trans hVpos hx)] at hraw
    rw [Real.dist_eq, sub_zero, abs_of_nonneg htail_pos] at hraw
    exact hraw
  have hint : IntegrableOn (fun x => |g x|) (Set.Ioi V) := by
    change Integrable (fun x => |g x|) (volume.restrict (Set.Ioi V))
    rw [← Measure.restrict_restrict_of_subset
      (by intro x hx; exact lt_trans hVpos hx)]
    exact habs.restrict
  have hsubset : Set.Icc a b ⊆ Set.Ioi V := by
    intro x hx
    have hVa : V < a := by
      dsimp [V]
      linarith [ha]
    exact lt_of_lt_of_le hVa hx.1
  have habs_bound : ∫ x in Set.Icc a b, |g x| ≤ ∫ x in Set.Ioi V, |g x| :=
    setIntegral_mono_set hint (Eventually.of_forall fun x => abs_nonneg (g x))
      (Eventually.of_forall fun x hx => hsubset hx)
  have hgabs : ∫ x in Set.Icc a b, g x ≤ ∫ x in Set.Icc a b, |g x| := by
    have hgint : IntegrableOn g (Set.Icc a b) :=
      (hg.mono_measure (Measure.restrict_mono hIa le_rfl)).integrable (by norm_num)
    exact integral_mono_ae hgint (hint.mono_set hsubset)
      (Eventually.of_forall fun x => le_abs_self (g x))
  exact hgabs.trans (habs_bound.trans (le_of_lt htail_lt))

private theorem integral_interval_le_holder {g : ℝ → ℝ} {s q a b : ℝ} (hs : 1 < s)
    (hsq : s.HolderConjugate q) (_ha : 0 ≤ a) (hab : a ≤ b)
    (hg : MemLp g (ENNReal.ofReal s) (volume.restrict (Set.Icc a b))) :
    ∫ t in Set.Icc a b, g t ≤
      (∫ t in Set.Icc a b, |g t| ^ s) ^ (1 / s) * (b - a) ^ (1 / q) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  haveI hμfin : IsFiniteMeasure μ := inferInstance
  have hgabs : MemLp (fun t => |g t|) (ENNReal.ofReal s) μ := hg.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal q) μ :=
    memLp_const 1
  have hleft : ∫ t in Set.Icc a b, g t ≤ ∫ t in Set.Icc a b, |g t| :=
    integral_mono_ae (hg.integrable (by simpa using hs.le))
      (hgabs.integrable (by simpa using hs.le))
      (Eventually.of_forall fun t => le_abs_self (g t))
  calc
    ∫ t in Set.Icc a b, g t ≤ ∫ t in Set.Icc a b, |g t| := hleft
    _ = ∫ t, |g t| * 1 ∂μ := by simp [μ]
    _ ≤ (∫ t, |g t| ^ s ∂μ) ^ (1 / s) *
        (∫ t, (1 : ℝ) ^ q ∂μ) ^ (1 / q) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg hsq
        (Eventually.of_forall fun t => abs_nonneg (g t))
        (Eventually.of_forall fun _ => zero_le_one) hgabs hone
    _ = (∫ t in Set.Icc a b, |g t| ^ s) ^ (1 / s) * (b - a) ^ (1 / q) := by
      simp [μ, integral_const, hab]

private theorem finite_memLp_small_interval_integral {g : ℝ → ℝ} {r : ENNReal}
    (hr_one : 1 < r) (hr_top : r ≠ ⊤) (hg : MemLp g r (volume.restrict (Set.Ioi 0))) :
    ∀ eta : ℝ, 0 < eta → ∃ L : ℝ, 0 < L ∧
      ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b - a ≤ L →
        ∫ t in Set.Icc a b, g t ≤ eta := by
  let s : ℝ := r.toReal
  have hs : 1 < s := by
    dsimp [s]
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_top]
    exact hr_one
  have hr_eq : ENNReal.ofReal s = r := ENNReal.ofReal_toReal hr_top
  have hg_s : MemLp g (ENNReal.ofReal s) (volume.restrict (Set.Ioi 0)) := by
    simpa [hr_eq] using hg
  have hpow : Integrable (fun t => |g t| ^ s)
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [Real.norm_eq_abs,
      ENNReal.toReal_ofReal (le_trans zero_le_one hs.le)] using hg_s.integrable_norm_rpow
      (by rw [hr_eq]; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hr_one.le))
      (by rw [hr_eq]; exact hr_top)
  intro eta heta
  let q : ℝ := s / (s - 1)
  have hsq : s.HolderConjugate q := Real.HolderConjugate.conjExponent hs
  have hq_pos : 0 < q := div_pos (lt_trans zero_lt_one hs) (sub_pos.mpr hs)
  let K : ℝ := (∫ t in Set.Ioi 0, |g t| ^ s) ^ (1 / s)
  have hK : 0 ≤ K :=
    Real.rpow_nonneg (integral_nonneg fun t => Real.rpow_nonneg (abs_nonneg (g t)) s) _
  have hinterval : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      ∫ t in Set.Icc a b, g t ≤ K * (b - a) ^ (1 / q) := by
    intro a b ha hab
    have hgIcc : MemLp g (ENNReal.ofReal s)
        (volume.restrict (Set.Icc a b)) := by
      have hgIoc : MemLp g (ENNReal.ofReal s)
          (volume.restrict (Set.Ioc a b)) :=
        hg_s.mono_measure (Measure.restrict_mono (fun x hx => lt_of_le_of_lt ha hx.1) le_rfl)
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hgIoc
    have hpow_le : ∫ t in Set.Icc a b, |g t| ^ s ≤ ∫ t in Set.Ioi 0, |g t| ^ s := by
      rw [integral_Icc_eq_integral_Ioc]
      apply setIntegral_mono_set hpow
        (Eventually.of_forall fun t => Real.rpow_nonneg (abs_nonneg (g t)) s)
      filter_upwards with t ht
      exact lt_of_le_of_lt ha ht.1
    have hroot : (∫ t in Set.Icc a b, |g t| ^ s) ^ (1 / s) ≤ K :=
      Real.rpow_le_rpow (by
        rw [integral_Icc_eq_integral_Ioc]
        exact integral_nonneg fun t => Real.rpow_nonneg (abs_nonneg (g t)) s) hpow_le
        (by positivity)
    calc
      ∫ t in Set.Icc a b, g t ≤
          (∫ t in Set.Icc a b, |g t| ^ s) ^ (1 / s) * (b - a) ^ (1 / q) :=
        integral_interval_le_holder hs hsq ha hab hgIcc
      _ ≤ K * (b - a) ^ (1 / q) := by
        exact mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (sub_nonneg.mpr hab) _)
  let L : ℝ := (eta / (K + 1)) ^ q
  have hK1 : 0 < K + 1 := by linarith
  have hbase : 0 < eta / (K + 1) := div_pos heta hK1
  have hL : 0 < L := Real.rpow_pos_of_pos hbase _
  refine ⟨L, hL, ?_⟩
  intro a b ha hab habL
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have hpow_len : (b - a) ^ (1 / q) ≤ L ^ (1 / q) :=
    Real.rpow_le_rpow hlen habL (by positivity)
  have hL_eval : L ^ (1 / q) = eta / (K + 1) := by
    dsimp [L]
    rw [← Real.rpow_mul hbase.le]
    have hqq : q * (1 / q) = 1 := by field_simp
    rw [hqq, Real.rpow_one]
  calc
    ∫ t in Set.Icc a b, g t ≤ K * (b - a) ^ (1 / q) := hinterval ha hab
    _ ≤ K * (eta / (K + 1)) := by
      rw [← hL_eval]
      exact mul_le_mul_of_nonneg_left hpow_len hK
    _ = (K / (K + 1)) * eta := by ring
    _ ≤ 1 * eta := by
      exact mul_le_mul_of_nonneg_right ((div_le_one₀ hK1).mpr (by linarith)) (le_of_lt heta)
    _ = eta := one_mul eta

private theorem eventual_interval_integral_upper {G : ℝ → ℝ} {r : ENNReal}
    (hr : 1 ≤ r) (hG : MemLp G r volume) :
    ∀ eta : ℝ, 0 < eta → ∃ T L : ℝ, 0 ≤ T ∧ 0 < L ∧
      ∀ {a b : ℝ}, T ≤ a → a ≤ b → b - a ≤ L →
        (∫ x in a..b, G x) ≤ eta := by
  intro eta heta
  have hG0 : MemLp G r (volume.restrict (Set.Ioi 0)) :=
    hG.restrict (Set.Ioi 0)
  by_cases hr_one : r = 1
  · rcases integral_interval_eventually_le_of_memLp_one
        (by simpa [hr_one] using hG0) heta (by norm_num : (0 : ℝ) < 1) with
      ⟨T, hT, htail⟩
    refine ⟨T, 1, hT, by norm_num, ?_⟩
    intro a b ha hab hlen
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact htail ha hab hlen
  by_cases hr_top : r = ⊤
  · rcases ae_upper_bound_of_memLp_top (by simpa [hr_top] using hG0) with
      ⟨C, hC, hbound⟩
    let L : ℝ := eta / (C + 1)
    have hL : 0 < L := div_pos heta (by linarith)
    refine ⟨0, L, le_rfl, hL, ?_⟩
    intro a b ha hab hlen
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    calc
      ∫ x in Set.Icc a b, G x ≤ C * (b - a) :=
        integral_interval_le_of_memLp_top hC hbound ha hab
      _ ≤ C * (eta / (C + 1)) := mul_le_mul_of_nonneg_left hlen hC
      _ = (C / (C + 1)) * eta := by ring
      _ ≤ eta := by
        calc
          (C / (C + 1)) * eta ≤ 1 * eta :=
            mul_le_mul_of_nonneg_right ((div_le_one₀ (by linarith)).mpr (by linarith))
              (le_of_lt heta)
          _ = eta := one_mul eta
  · have hr_strict : 1 < r := lt_of_le_of_ne hr (Ne.symm hr_one)
    rcases finite_memLp_small_interval_integral hr_strict hr_top hG0 eta heta with
      ⟨L, hL, hsmall⟩
    refine ⟨0, L, le_rfl, hL, ?_⟩
    intro a b ha hab hlen
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact hsmall ha hab hlen

/-- Lemma 2.11: a nonnegative locally absolutely continuous `L^p` function vanishes at infinity. -/
theorem limit_zero_of_memLp_deriv_bound (F G : ℝ → ℝ) (p r : ENNReal)
    (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ENNReal)) (hr : 1 ≤ r)
    (hF_nonneg : ∀ t, 0 ≤ F t) (hF_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval F 0 b)
    (hF : MemLp F p volume) (hG : MemLp G r volume)
    (hderiv : ∀ᵐ t ∂volume, deriv F t ≤ G t) : Tendsto F atTop (nhds 0) := by
  have hincrement : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b →
      F b - F a ≤ ∫ x in a..b, G x :=
    fun a b ha hab => increment_le_interval_integral F G r hr hF_ac hG hderiv ha hab
  have hsmall : ∀ eta : ℝ, 0 < eta → ∃ T L : ℝ, 0 ≤ T ∧ 0 < L ∧
      ∀ {a b : ℝ}, T ≤ a → a ≤ b → b - a ≤ L →
        (∫ x in a..b, G x) ≤ eta :=
    eventual_interval_integral_upper hr hG
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨epsilon, hepsilon, hhigh⟩
  have hhigh' : ∀ R : ℝ, ∃ t ≥ R, epsilon ≤ F t :=
    fun R => by
      rcases hhigh R with ⟨t, htR, ht⟩
      exact ⟨t, htR, by simpa [Real.dist_eq, abs_of_nonneg (hF_nonneg t)] using ht⟩
  rcases hsmall (epsilon / 2) (by linarith) with
    ⟨T, L, hT, hL, hsmall_interval⟩
  let t : ℕ → ℝ := Nat.rec (Classical.choose (hhigh' (T + L)))
    (fun _ x => Classical.choose (hhigh' (x + 2 * L)))
  have ht_zero : T + L ≤ t 0 := (Classical.choose_spec (hhigh' (T + L))).1
  have ht_high : ∀ n, epsilon ≤ F (t n) := by
    intro n
    induction n with
    | zero => exact (Classical.choose_spec (hhigh' (T + L))).2
    | succ n ih =>
      exact (Classical.choose_spec (hhigh' (t n + 2 * L))).2
  have ht_step : ∀ n, t n + 2 * L ≤ t (n + 1) :=
    fun n => (Classical.choose_spec (hhigh' (t n + 2 * L))).1
  have ht_lower : ∀ n, T + L ≤ t n := by
    intro n
    induction n with
    | zero => exact ht_zero
    | succ n ih => linarith [ht_step n]
  let J : ℕ → Set ℝ := fun n => Set.Ioc (t n - L) (t n)
  have hJpos : ∀ n, J n ⊆ Set.Ioi 0 := by
    intro n x hx
    change t n - L < x ∧ x ≤ t n at hx
    have hn := ht_lower n
    change 0 < x
    linarith
  have hlower : ∀ n x, x ∈ J n → epsilon / 2 ≤ F x := by
    intro n x hx
    change t n - L < x ∧ x ≤ t n at hx
    have hxn : T ≤ x := by
      have hn := ht_lower n
      linarith
    have hlen : t n - x ≤ L := by linarith
    have hinc := hincrement (a := x) (b := t n) (le_trans hT hxn) hx.2
    have hsmall' := hsmall_interval hxn hx.2 hlen
    linarith [ht_high n]
  have hsep : ∀ {m n : ℕ}, m < n → t m + 2 * L ≤ t n := by
    intro m n hmn
    exact Nat.le_induction (ht_step m)
      (fun k _ ih => by linarith [ht_step k]) n (by omega : m + 1 ≤ n)
  have hpointpow : ∀ n x, x ∈ J n →
      (epsilon / 2) ^ p.toReal ≤ |F x| ^ p.toReal := by
    intro n x hx
    have hlow := hlower n x hx
    rw [abs_of_nonneg (hF_nonneg x)]
    exact Real.rpow_le_rpow (by linarith) hlow ENNReal.toReal_nonneg
  have hFpow : IntegrableOn (fun x => |F x| ^ p.toReal) (Set.Ioi 0) :=
    (hF.integrable_norm_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top).restrict
  have hint : ∀ n, IntegrableOn (fun x => |F x| ^ p.toReal) (J n) :=
    fun n => hFpow.mono_set (hJpos n)
  have hmass_one : ∀ n, (epsilon / 2) ^ p.toReal * L ≤
      ∫ x in J n, |F x| ^ p.toReal := by
    intro n
    have hconst : IntegrableOn (fun _ : ℝ => (epsilon / 2) ^ p.toReal) (J n) := by
      simp [J, Real.volume_Ioc]
    have hmono : (∫ _x in J n, (epsilon / 2) ^ p.toReal) ≤
        ∫ x in J n, |F x| ^ p.toReal := by
      apply integral_mono_ae hconst (hint n)
      change (fun _x => (epsilon / 2) ^ p.toReal) ≤ᵐ[
        volume.restrict (Set.Ioc (t n - L) (t n))] fun x => |F x| ^ p.toReal
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (by
        filter_upwards with x hx
        exact hpointpow n x hx)
    calc
      (epsilon / 2) ^ p.toReal * L = ∫ _x in J n, (epsilon / 2) ^ p.toReal := by
        rw [integral_const]
        simp [J, hL.le]
        ring
      _ ≤ ∫ x in J n, |F x| ^ p.toReal := hmono
  have hmass : ∀ N : ℕ, (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤
      ∫ x in Set.Ioi 0, |F x| ^ p.toReal := by
    intro N
    let U : Set ℝ := ⋃ n ∈ Finset.range N, J n
    have hU : U ⊆ Set.Ioi 0 := by
      intro x hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hx⟩
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨hn, hx⟩
      exact hJpos n hx
    have hdisj : Set.Pairwise Set.univ (Function.onFun Disjoint J) := by
      intro m hm n hn hmn
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · apply Set.disjoint_left.2
        intro x hxm hxn
        change t m - L < x ∧ x ≤ t m at hxm
        change t n - L < x ∧ x ≤ t n at hxn
        have hs := hsep hlt
        linarith
      · apply Set.disjoint_left.2
        intro x hxm hxn
        change t m - L < x ∧ x ≤ t m at hxm
        change t n - L < x ∧ x ≤ t n at hxn
        have hs := hsep hgt
        linarith
    have hsum : (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤
        ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
      calc
        (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) =
            ∑ _n ∈ Finset.range N, ((epsilon / 2) ^ p.toReal * L) := by simp
        _ ≤ ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
          gcongr with n hn
          exact hmass_one n
    have hUnion : (∫ x in U, |F x| ^ p.toReal) =
        ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
      dsimp [U]
      exact integral_biUnion_finset (Finset.range N)
        (fun n _ => measurableSet_Ioc) (fun m hm n hn hmn => hdisj (by simp) (by simp) hmn)
        (fun n _ => hint n)
    calc
      (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤ ∫ x in U, |F x| ^ p.toReal := by
        rw [hUnion]
        exact hsum
      _ ≤ ∫ x in Set.Ioi 0, |F x| ^ p.toReal :=
        setIntegral_mono_set hFpow
          (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (F x)) p.toReal)
          (Eventually.of_forall fun x hx => hU hx)
  have hc_pos : 0 < (epsilon / 2) ^ p.toReal * L :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) hL
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x in Set.Ioi 0, |F x| ^ p.toReal) /
    ((epsilon / 2) ^ p.toReal * L))
  have hN' : ∫ x in Set.Ioi 0, |F x| ^ p.toReal <
      (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) :=
    (div_lt_iff₀ hc_pos).mp (by exact_mod_cast hN)
  linarith [hmass N]

end AbbasDynamical2015
