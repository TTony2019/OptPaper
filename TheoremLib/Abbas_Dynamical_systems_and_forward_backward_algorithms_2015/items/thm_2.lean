import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.Subdifferential
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.prop_1
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_6
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_7

namespace AbbasDynamical2015

open Filter MeasureTheory

private theorem operator_constant_on_solution_set_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (beta : ℝ) (S : Set H)
    (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∀ z ∈ S, ∀ w ∈ S, B z = B w := by
  intro z hz w hw
  have hzsub := (hsolution z).1 hz
  have hwsub := (hsolution w).1 hw
  have hmono := ERealFunction.isMonotone_subdifferential
    (fun x : H => (Phi x : EReal))
    (ERealFunction.isProper_of_mem_gammaZero hPhi)
    (-B z) hzsub (-B w) hwsub
  have hsubmono : inner ℝ (B z - B w) (z - w) ≤ 0 := by
    rw [show (-B z) - (-B w) = -(B z - B w) by abel, inner_neg_left] at hmono
    linarith
  have hc := hB.ineq
    (⟨z, Set.mem_univ z⟩ : Set.univ) (⟨w, Set.mem_univ w⟩ : Set.univ)
  have hcobound : beta * ‖B z - B w‖ ^ 2 ≤
      inner ℝ (B z - B w) (z - w) := by
    simpa [real_inner_comm] using hc
  have hzero : beta * ‖B z - B w‖ ^ 2 = 0 :=
    le_antisymm (hcobound.trans hsubmono) (mul_nonneg hbeta.le (sq_nonneg _))
  have hnorm : ‖B z - B w‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hbeta.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

private theorem uniformContinuousOn_sq_integrable_tendsto_zero_local
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E)
    (huc : UniformContinuousOn f (Set.Ici 0))
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2) (Set.Ici 0)) :
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
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  change |(∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

private theorem uniformContinuousOn_of_deriv_integral_eq_sub_sq_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H}
    (hFTC : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      x t - x s = ∫ r in s..t, deriv x r)
    (hlocal : ∀ T : ℝ, 0 < T →
      MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 T)))
    (hint : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0)) :
    UniformContinuousOn x (Set.Ici 0) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  let C : ℝ := ∫ t in Set.Ici 0, ‖deriv x t‖ ^ 2
  have hC : 0 ≤ C := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  let δ : ℝ := (ε / (C + 1)) ^ 2
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := sq_pos_of_pos (div_pos hε hC1)
  have hforward : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → dist s t < δ →
      dist (x s) (x t) < ε := by
    intro s t hs hst hdist
    have hlength : 0 ≤ t - s := sub_nonneg.mpr hst
    have hlength_lt : t - s < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] at hdist
      linarith
    have hlocal_le : ∫ r in s..t, ‖deriv x r‖ ^ 2 ≤ C := by
      rw [intervalIntegral.integral_of_le hst]
      apply MeasureTheory.setIntegral_mono_set hint
      · filter_upwards with r
        exact sq_nonneg _
      · filter_upwards with r hr
        exact le_trans hs hr.1.le
    have hmem : MemLp (deriv x) 2 (volume.restrict (Set.Ioc s t)) :=
      (hlocal (max t 1) (by positivity)).mono_measure
        (Measure.restrict_mono
          (show Set.Ioc s t ⊆ Set.Icc 0 (max t 1) from fun r hr =>
            ⟨le_trans hs hr.1.le, le_trans hr.2 (le_max_left _ _)⟩) le_rfl)
    have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2
        (volume.restrict (Set.Ioc s t)) := MeasureTheory.memLp_const 1
    have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume.restrict (Set.Ioc s t)) (p := (2 : ℝ)) (q := (2 : ℝ))
      (f := fun r => ‖deriv x r‖) (g := fun _ : ℝ => (1 : ℝ))
      (Real.holderConjugate_iff.mpr (by norm_num))
      (by simpa using hmem.norm) (by simpa using hone)
    have hnormint : ∫ r in s..t, ‖deriv x r‖ ≤
        Real.sqrt C * Real.sqrt (t - s) := by
      rw [intervalIntegral.integral_of_le hst]
      have hholder' : ∫ r in Set.Ioc s t, ‖deriv x r‖ ≤
          Real.sqrt (∫ r in Set.Ioc s t, ‖deriv x r‖ ^ 2) *
            Real.sqrt (t - s) := by
        simpa [Real.sqrt_eq_rpow, Real.volume_Ioc, hlength] using hholder
      have hrootlocal : Real.sqrt (∫ r in Set.Ioc s t, ‖deriv x r‖ ^ 2) ≤
          Real.sqrt C := by
        rw [intervalIntegral.integral_of_le hst] at hlocal_le
        exact Real.sqrt_le_sqrt hlocal_le
      calc
        ∫ r in Set.Ioc s t, ‖deriv x r‖ ≤
            Real.sqrt (∫ r in Set.Ioc s t, ‖deriv x r‖ ^ 2) * Real.sqrt (t - s) := hholder'
        _ ≤ Real.sqrt C * Real.sqrt (t - s) :=
          mul_le_mul_of_nonneg_right hrootlocal (Real.sqrt_nonneg _)
    have hrootC : Real.sqrt C ≤ C + 1 := by
      have hsqrt : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
      have hsq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
      nlinarith
    have hroot_len : Real.sqrt (t - s) < ε / (C + 1) := by
      have hsqrt : 0 ≤ Real.sqrt (t - s) := Real.sqrt_nonneg _
      have hsq : (Real.sqrt (t - s)) ^ 2 = t - s := Real.sq_sqrt hlength
      dsimp [δ] at hlength_lt
      nlinarith [div_pos hε hC1]
    have hbound : ‖x t - x s‖ < ε := by
      rw [hFTC s t hs hst]
      calc
        ‖∫ r in s..t, deriv x r‖ ≤ ∫ r in s..t, ‖deriv x r‖ :=
          intervalIntegral.norm_integral_le_integral_norm hst
        _ ≤ Real.sqrt C * Real.sqrt (t - s) := hnormint
        _ < ε := by
          calc
            Real.sqrt C * Real.sqrt (t - s) ≤ (C + 1) * Real.sqrt (t - s) :=
              mul_le_mul_of_nonneg_right hrootC (Real.sqrt_nonneg _)
            _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hroot_len hC1
            _ = ε := by field_simp
    rw [dist_eq_norm_sub, norm_sub_rev]
    exact hbound
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hdist
  rcases le_total s t with hst | hts
  · exact hforward hs hst hdist
  · simpa [dist_comm] using hforward ht hts (by simpa [dist_comm] using hdist)

private theorem inner_tendsto_zero_of_tendsto_zero_of_bounded_range_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : ℕ → H)
    (ha : Tendsto a atTop (nhds 0))
    (hb : Bornology.IsBounded (Set.range b)) :
    Tendsto (fun n ↦ inner ℝ (a n) (b n)) atTop (nhds 0) := by
  rcases (isBounded_iff_forall_norm_le (s := Set.range b)).mp hb with ⟨C, hC⟩
  let M : ℝ := max C 0
  have hbM (n : ℕ) : ‖b n‖ ≤ M :=
    le_trans (hC (b n) ⟨n, rfl⟩) (le_max_left _ _)
  have hanorm : Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0) := by simpa using ha.norm
  have hbound (n : ℕ) : |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
    calc
      |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
      _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hbM n) (norm_nonneg _)
  have hmajor : Tendsto (fun n ↦ ‖a n‖ * M) atTop (nhds 0) := by
    simpa [zero_mul] using hanorm.mul tendsto_const_nhds
  have habs : Tendsto (fun n ↦ |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _) hbound hmajor
  have hneg : Tendsto (fun n ↦ -|inner ℝ (a n) (b n)|) atTop (nhds 0) := by simpa using habs.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs (fun n => neg_abs_le _)
    (fun n => le_abs_self _)

private theorem intervalIntegral_deriv_eq_sub_of_ac_ae_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hAC : AbsolutelyContinuousOnInterval f a b)
    (hInt : IntervalIntegrable (deriv f) volume a b)
    (hDeriv : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      HasDerivAt f (deriv f t) t) :
    ∫ t in a..b, deriv f t = f b - f a := by
  have hDeriv' : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt f (deriv f t) t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hDeriv
    simpa [Set.uIcc_of_le hab] using hDeriv
  apply ext_inner_right ℝ
  intro w
  have hscalarAC : AbsolutelyContinuousOnInterval (fun t => inner ℝ (f t) w) a b := by
    have hnonneg : ∀ E : ℕ × (ℕ → ℝ × ℝ), 0 ≤
        ∑ i ∈ Finset.range E.1,
          dist ((fun t => inner ℝ (f t) w) (E.2 i).1)
            ((fun t => inner ℝ (f t) w) (E.2 i).2) :=
      fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg
    have hbound : ∀ E : ℕ × (ℕ → ℝ × ℝ),
        ∑ i ∈ Finset.range E.1,
            dist ((fun t => inner ℝ (f t) w) (E.2 i).1)
              ((fun t => inner ℝ (f t) w) (E.2 i).2) ≤
          ‖w‖ * ∑ i ∈ Finset.range E.1,
            dist (f (E.2 i).1) (f (E.2 i).2) := by
      intro E
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => by
        simpa [Real.dist_eq, dist_eq_norm_sub, inner_sub_left, mul_comm] using
          norm_inner_le_norm (𝕜 := ℝ) (f (E.2 i).1 - f (E.2 i).2) w
    have hmajor : Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) =>
        ‖w‖ * ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b)) (nhds 0) := by
      simpa [AbsolutelyContinuousOnInterval, Finset.mul_sum, dist_smul₀] using
        hAC.const_smul ‖w‖
    exact squeeze_zero hnonneg hbound hmajor
  have hscalarFTC := hscalarAC.integral_deriv_eq_sub
  calc
    inner ℝ (∫ t in a..b, deriv f t) w = ∫ t in a..b, inner ℝ (deriv f t) w := by
      simpa [real_inner_comm] using
        ((innerSL ℝ w).intervalIntegral_comp_comm hInt).symm
    _ = ∫ t in a..b, deriv (fun u => inner ℝ (f u) w) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hDeriv'] with t hft ht
      have hderiv := hft (Set.uIoc_subset_uIcc ht)
      simpa using (hderiv.inner ℝ (hasDerivAt_const t w)).deriv.symm
    _ = inner ℝ (f b - f a) w := by
      simpa [inner_sub_left] using hscalarFTC

/-- The four conclusions of Theorem 2.8 for a strong orbit of (8)--(9). -/
theorem theorem_2_8_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (lam beta : ℝ)
    (hS : S.Nonempty) (hlam : 0 < lam) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hvL2 : ∀ T, 0 < T → MemLp v 2 (volume.restrict (Set.Icc 0 T)))
    (hdxL2 : ∀ T, 0 < T → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 T)))
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    (Tendsto (fun t ↦ ‖v t + B (x t)‖) atTop (nhds 0)) ∧
    (∀ z ∈ S, Tendsto (fun t ↦ B (x t)) atTop (nhds (B z))) ∧
    (∀ z ∈ S, Tendsto v atTop (nhds (-B z))) ∧
    ∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z)) := by
  obtain ⟨z₀, hz₀⟩ := hS
  have hdomPhi : (ERealFunction.effectiveDomain Phi).Nonempty :=
    (ERealFunction.isProper_of_mem_gammaZero hPhi).2
  have hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ z, z ∈ S → z ∈ ERealFunction.effectiveDomain Phi := by
    constructor
    · intro t ht
      exact ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
        ⟨v t, hsubgradient t ht⟩
    · intro z hz
      exact ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
        ⟨-B z, (hsolution z).1 hz⟩
  have horbit_pair : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici, horbit] with t ht hEq
    exact ⟨hsubgradient t ht, hEq⟩
  have hBconst : ∀ z, z ∈ S → B z = B z₀ :=
    fun z hz => operator_constant_on_solution_set_local Phi hPhi B beta S hbeta hB hsolution
      z hz z₀ hz₀
  have hmu : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hmu_lam : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
  have hLyapunov := proposition_2_12 S Phi hPhi B x v z₀ lam lam⁻¹ beta
    (show S.Nonempty from ⟨z₀, hz₀⟩) hz₀
    hlam hmu hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient
    hvL2 hdxL2 horbit_pair (fun w hw => (hsolution w).1 hw) hdom
  rcases hLyapunov with ⟨hGammaAnti, hGammaLim, hBsq, hxBound,
    hdxsq, hshiftDvsq, hdvsq, hvBound, hEnergyLim⟩
  have hdvL2 (T : ℝ) (hT : 0 < T) :
      MemLp (deriv v) 2 (volume.restrict (Set.Icc 0 T)) :=
    (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_deriv v (volume.restrict (Set.Icc 0 T)))).mpr
      (hdvsq.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl))
  have hFTC_x : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      x t - x s = ∫ r in s..t, deriv x r := by
    intro s t hs hst
    by_cases ht0 : t = 0
    · subst t
      have hs0 : s = 0 := le_antisymm hst hs
      subst s
      simp
    · have ht : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht0)
      have hdxIcc : IntegrableOn (deriv x) (Set.Icc s t) :=
        ((hdxL2 t ht).mono_measure
          (Measure.restrict_mono (Set.Icc_subset_Icc hs le_rfl) le_rfl)).integrable (by norm_num)
      have hdxInt : IntervalIntegrable (deriv x) volume s t :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
          (hdxIcc.mono_set Set.Ioc_subset_Icc_self)
      exact (intervalIntegral_deriv_eq_sub_of_ac_ae_local hst
        ((hx_ac t ht).mono (by
          rw [Set.uIcc_of_le hst, Set.uIcc_of_le ht.le]
          exact Set.Icc_subset_Icc hs le_rfl)) hdxInt
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset
          (Set.Icc_subset_Icc hs le_rfl) (hx_deriv t ht))).symm
  have hFTC_v : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      v t - v s = ∫ r in s..t, deriv v r := by
    intro s t hs hst
    by_cases ht0 : t = 0
    · subst t
      have hs0 : s = 0 := le_antisymm hst hs
      subst s
      simp
    · have ht : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht0)
      have hdvIcc : IntegrableOn (deriv v) (Set.Icc s t) :=
        ((hdvL2 t ht).mono_measure
          (Measure.restrict_mono (Set.Icc_subset_Icc hs le_rfl) le_rfl)).integrable (by norm_num)
      have hdvInt : IntervalIntegrable (deriv v) volume s t :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
          (hdvIcc.mono_set Set.Ioc_subset_Icc_self)
      exact (intervalIntegral_deriv_eq_sub_of_ac_ae_local hst
        ((hv_ac t ht).mono (by
          rw [Set.uIcc_of_le hst, Set.uIcc_of_le ht.le]
          exact Set.Icc_subset_Icc hs le_rfl)) hdvInt
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset
          (Set.Icc_subset_Icc hs le_rfl) (hv_deriv t ht))).symm
  have hxUC := uniformContinuousOn_of_deriv_integral_eq_sub_sq_local hFTC_x hdxL2 hdxsq
  have hvUC := uniformContinuousOn_of_deriv_integral_eq_sub_sq_local hFTC_v hdvL2 hdvsq
  have hBuc : UniformContinuous B := by
    have hsub : UniformContinuous (fun y : H => (⟨y, Set.mem_univ y⟩ : Set.univ)) :=
      uniformContinuous_id.subtype_mk _
    simpa [Function.comp_def] using (lipschitzWith_of_cocoercive hB).uniformContinuous.comp hsub
  have hBxUC : UniformContinuousOn (fun t => B (x t)) (Set.Ici 0) :=
    hBuc.uniformContinuousOn.comp hxUC (Set.mapsTo_univ _ _)
  have hBdiffUC : UniformContinuousOn (fun t => B (x t) - B z₀) (Set.Ici 0) := by
    rw [Metric.uniformContinuousOn_iff] at hBxUC ⊢
    intro ε hε
    rcases hBxUC ε hε with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro s hs t ht hst
    simpa only [dist_sub_right] using hδprop s hs t ht hst
  have hBlim0 : Tendsto (fun t => B (x t) - B z₀) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero_local _ hBdiffUC hBsq
  have hresUC : UniformContinuousOn (fun t => v t + B (x t)) (Set.Ici 0) := by
    rw [Metric.uniformContinuousOn_iff] at hvUC hBxUC ⊢
    intro ε hε
    rcases hvUC (ε / 2) (by linarith) with ⟨δv, hδv, hvprop⟩
    rcases hBxUC (ε / 2) (by linarith) with ⟨δB, hδB, hBprop⟩
    refine ⟨min δv δB, lt_min hδv hδB, ?_⟩
    intro s hs t ht hst
    have hsv : dist (v s) (v t) < ε / 2 :=
      hvprop s hs t ht (lt_of_lt_of_le hst (min_le_left _ _))
    have hsB : dist (B (x s)) (B (x t)) < ε / 2 :=
      hBprop s hs t ht (lt_of_lt_of_le hst (min_le_right _ _))
    calc
      dist (v s + B (x s)) (v t + B (x t)) ≤
          dist (v s) (v t) + dist (B (x s)) (B (x t)) := dist_add_add_le _ _ _ _
      _ < ε := by linarith
  have hresSq : IntegrableOn (fun t => ‖v t + B (x t)‖ ^ 2) (Set.Ici 0) := by
    apply Integrable.mono' ((hdxsq.const_mul (2 * lam ^ 2)).add (hdvsq.const_mul 2))
    · exact (hvUC.continuousOn.add hBxUC.continuousOn).aestronglyMeasurable
        measurableSet_Ici |>.norm.pow 2
    · filter_upwards [horbit] with t ht
      have hres : v t + B (x t) = -(lam • deriv x t + deriv v t) := by
        have hzero : (lam • deriv x t + deriv v t) + (v t + B (x t)) = 0 := by
          simpa [add_assoc] using ht
        exact eq_neg_of_add_eq_zero_right hzero
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hres, norm_neg]
      have htri := norm_add_le (lam • deriv x t) (deriv v t)
      have hlam : ‖lam • deriv x t‖ = lam * ‖deriv x t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
      rw [hlam] at htri
      have hsq := (sq_le_sq₀ (norm_nonneg (lam • deriv x t + deriv v t))
        (by positivity)).mpr htri
      have hbound : (lam * ‖deriv x t‖ + ‖deriv v t‖) ^ 2 ≤
          2 * lam ^ 2 * ‖deriv x t‖ ^ 2 + 2 * ‖deriv v t‖ ^ 2 := by
        nlinarith [sq_nonneg (lam * ‖deriv x t‖ - ‖deriv v t‖)]
      exact hsq.trans hbound
  have hreslim : Tendsto (fun t => v t + B (x t)) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero_local _ hresUC hresSq
  have hvlim0 : Tendsto v atTop (nhds (-B z₀)) := by
    have hplus : Tendsto (fun t => v t + B z₀) atTop (nhds 0) := by
      convert hreslim.sub hBlim0 using 1 <;> ext t <;> abel_nf
    simpa using hplus.sub (tendsto_const_nhds (x := B z₀))
  have hBlim (z : H) (hz : z ∈ S) : Tendsto (fun t => B (x t)) atTop (nhds (B z)) := by
    have hsum : Tendsto (fun t => B z₀ + (B (x t) - B z₀)) atTop (nhds (B z₀)) :=
      by simpa using (tendsto_const_nhds (x := B z₀)).add hBlim0
    simpa [hBconst z hz] using hsum
  have hvlim (z : H) (hz : z ∈ S) : Tendsto v atTop (nhds (-B z)) := by
    simpa [hBconst z hz] using hvlim0
  refine ⟨?_, hBlim, hvlim, ?_⟩
  · simpa using hreslim.norm
  · rcases hxBound with ⟨C, hxC⟩
    have hdist (z : H) (hz : z ∈ S) : ∃ l : ℝ,
        Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l) := by
      have hLyap_z := proposition_2_12 S Phi hPhi B x v z lam lam⁻¹ beta
        (show S.Nonempty from ⟨z₀, hz₀⟩) hz hlam hmu hmu_lam hbeta hB
        hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit_pair
        (fun w hw => (hsolution w).1 hw) hdom
      rcases hLyap_z with ⟨_, hGammaLim_z, _, _, _, _, _, _, hEnergyLim_z⟩
      rcases hGammaLim_z with ⟨lGamma, hGamma⟩
      rcases hEnergyLim_z with ⟨lEnergy, hEnergy⟩
      have hvplus : Tendsto (fun t ↦ v t + B z) atTop (nhds 0) := by
        simpa using (hvlim z hz).add (tendsto_const_nhds (x := B z))
      have hxevent : ∀ᶠ t in atTop, ‖x t‖ ≤ C :=
        Filter.eventually_atTop.2 ⟨0, fun t ht ↦ hxC t ht⟩
      let M : ℝ := max C 0
      have hxM : ∀ᶠ t in atTop, ‖x t‖ ≤ M := by
        filter_upwards [hxevent] with t ht
        exact ht.trans (le_max_left _ _)
      have hcross : Tendsto (fun t ↦ inner ℝ (x t) (v t + B z)) atTop (nhds 0) := by
        have hvplusnorm : Tendsto (fun t ↦ ‖v t + B z‖) atTop (nhds 0) := by
          simpa using hvplus.norm
        have hbound : ∀ᶠ t in atTop,
            |inner ℝ (x t) (v t + B z)| ≤ M * ‖v t + B z‖ := by
          filter_upwards [hxM] with t ht
          calc
            |inner ℝ (x t) (v t + B z)| ≤ ‖x t‖ * ‖v t + B z‖ := by
              simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (x t) (v t + B z)
            _ ≤ M * ‖v t + B z‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
        have hmajor : Tendsto (fun t ↦ M * ‖v t + B z‖) atTop (nhds 0) := by
          simpa [mul_zero] using (tendsto_const_nhds (x := M)).mul hvplusnorm
        have hnegmajor : Tendsto (fun t ↦ -(M * ‖v t + B z‖)) atTop (nhds 0) := by
          simpa using hmajor.neg
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegmajor hmajor
          (hbound.mono fun t ht => (neg_le_neg ht).trans (neg_abs_le _))
          (hbound.mono fun t ht => (le_abs_self _).trans ht)
      have hgap : Tendsto (fun t ↦
          (Phi z : EReal).toReal -
            ((Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) +
            inner ℝ (x t) (v t + B z) - inner ℝ z (v t))
          atTop
          (nhds ((Phi z : EReal).toReal - lEnergy + 0 - inner ℝ z (-B z))) := by
        simpa using (tendsto_const_nhds.sub hEnergy).add hcross |>.sub
          ((tendsto_const_nhds (x := z)).inner (hvlim z hz))
      have hGamma_expand (t : ℝ) :
          (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + lam⁻¹ *
            ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
              inner ℝ (z - x t) (v t)) =
          (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 + lam⁻¹ *
            ((Phi z : EReal).toReal -
              ((Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) +
              inner ℝ (x t) (v t + B z) - inner ℝ z (v t)) := by
        rw [inner_sub_left, inner_add_right]
        ring
      have hsq : Tendsto (fun t ↦ ‖x t - z‖ ^ 2) atTop
          (nhds (2 * (lGamma - lam⁻¹ *
            ((Phi z : EReal).toReal - lEnergy - inner ℝ z (-B z)))) ) := by
        convert ((hGamma.congr' (Filter.Eventually.of_forall hGamma_expand)).sub
          (hgap.const_mul lam⁻¹)).const_mul 2 using 1 <;> ext t <;> ring_nf
      refine ⟨Real.sqrt (2 * (lGamma - lam⁻¹ *
        ((Phi z : EReal).toReal - lEnergy - inner ℝ z (-B z)))), ?_⟩
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg] using
        Real.continuous_sqrt.tendsto _ |>.comp hsq
    have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z))) → z ∈ S := by
      intro z hzcluster
      obtain ⟨u, hu_top, hu_weak⟩ := hzcluster
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
        ((Filter.tendsto_atTop.1 hu_top) 0)
      let q : ℕ → ℝ := fun n ↦ u (n + N)
      have hq_nonneg (n : ℕ) : 0 ≤ q n :=
        hN (n + N) (Nat.le_add_left N n)
      have hq_top : Tendsto q atTop atTop := by
        simpa [q] using (Filter.tendsto_add_atTop_iff_nat N).2 hu_top
      have hq_weak : Tendsto (fun n ↦ toWeakSpace ℝ H (x (q n))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [q] using (Filter.tendsto_add_atTop_iff_nat N).2 hu_weak
      have hvq : Tendsto (fun n ↦ v (q n)) atTop (nhds (-B z₀)) :=
        hvlim0.comp hq_top
      have hvq_mem : ∀ n, v (q n) ∈ ERealFunction.subdifferential Phi (x (q n)) :=
        fun n ↦ hsubgradient (q n) (hq_nonneg n)
      have hBq : Tendsto (fun n ↦ B (x (q n))) atTop (nhds (B z₀)) :=
        (hBlim z₀ hz₀).comp hq_top
      let d : H := B z₀ - B z
      have hdiff : Tendsto (fun n ↦ B (x (q n)) - B z) atTop (nhds d) := by
        simpa [d] using hBq.sub tendsto_const_nhds
      have herr : Tendsto (fun n ↦ B (x (q n)) - B z - d) atTop (nhds 0) := by
        simpa [d] using hdiff.sub (tendsto_const_nhds (x := B z₀ - B z))
      have hxbdd : Bornology.IsBounded (Set.range (fun n ↦ x (q n))) :=
        bounded_range_of_tendsto_weakly hq_weak
      have hcross : Tendsto
          (fun n ↦ inner ℝ (x (q n) - z) (B (x (q n)) - B z - d)) atTop (nhds 0) := by
        have hcross' : Tendsto
            (fun n ↦ inner ℝ (B (x (q n)) - B z - d) (x (q n) - z)) atTop (nhds 0) := by
          apply inner_tendsto_zero_of_tendsto_zero_of_bounded_range_local _ _ herr
          rcases (isBounded_iff_forall_norm_le (s := Set.range (fun n ↦ x (q n)))).mp hxbdd
            with ⟨C, hC⟩
          refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖z‖, ?_⟩
          rintro _ ⟨n, rfl⟩
          calc
            ‖x (q n) - z‖ ≤ ‖x (q n)‖ + ‖z‖ := norm_sub_le _ _
            _ ≤ C + ‖z‖ := add_le_add (hC _ ⟨n, rfl⟩) le_rfl
        simpa [real_inner_comm] using hcross'
      have hxinner : Tendsto (fun n ↦ inner ℝ (x (q n)) d) atTop
          (nhds (inner ℝ z d)) := by
        simpa using
          ((weakSpace_continuous_inner_right d).tendsto (toWeakSpace ℝ H z)).comp hq_weak
      have hfixed : Tendsto (fun n ↦ inner ℝ (x (q n) - z) d) atTop (nhds 0) := by
        simpa [inner_sub_left] using hxinner.sub (tendsto_const_nhds (x := inner ℝ z d))
      have hright : Tendsto (fun n ↦ inner ℝ (x (q n) - z)
          (B (x (q n)) - B z)) atTop (nhds 0) := by
        have hsum := hcross.add hfixed
        convert hsum using 1
        · ext n
          rw [← inner_add_right]
          congr 1
          dsimp [d]
          abel
        · simp
      have hleft : Tendsto (fun n ↦ beta * ‖B (x (q n)) - B z‖ ^ 2) atTop
          (nhds (beta * ‖d‖ ^ 2)) := by
        simpa using tendsto_const_nhds.mul (hdiff.norm.pow 2)
      have hineq (n : ℕ) : beta * ‖B (x (q n)) - B z‖ ^ 2 ≤
          inner ℝ (x (q n) - z) (B (x (q n)) - B z) := by
        simpa using hB.ineq ⟨x (q n), Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
      have hdle : beta * ‖d‖ ^ 2 ≤ 0 :=
        le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hineq)
      have hdnorm : ‖d‖ = 0 := by
        have hprod : beta * ‖d‖ ^ 2 = 0 := le_antisymm hdle
          (mul_nonneg hbeta.le (sq_nonneg _))
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left hbeta.ne')
      have hBz : B z = B z₀ := (sub_eq_zero.mp (norm_eq_zero.mp hdnorm)).symm
      have hclosed : -B z₀ ∈ ERealFunction.subdifferential Phi z :=
        maximal_monotone_graph_weak_strong_closed
          (ERealFunction.subdifferential Phi)
          (ERealFunction.subdifferential_isMaximalMonotone_of_mem_gammaZero hPhi)
          (fun n ↦ x (q n)) (fun n ↦ v (q n)) z (-B z₀)
          hq_weak hvq hvq_mem
      exact (hsolution z).mpr (by simpa [hBz] using hclosed)
    exact opial_trajectory_lemma S x (show S.Nonempty from ⟨z₀, hz₀⟩) hdist hcluster

end AbbasDynamical2015
