import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_5
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_6
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.lem_7
import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.WeakTopology
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory Filter
open scoped Pointwise

/-- Regularity and minimal-residual properties of a forward-backward semigroup orbit. -/
structure ForwardBackwardSemigroupOrbit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Phi : H → Set.Ioi (⊥ : EReal))
    (B : H → H) (x : ℝ → H) where
  locally_absolutelyContinuous : ∀ T : ℝ, 0 < T → AbsolutelyContinuousOnInterval x 0 T
  selection : ℝ → H
  selection_mem : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
    selection t ∈ ERealFunction.subdifferential Phi (x t)
  effectiveDomain : ∀ t : ℝ, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi
  selection_memLp : ∀ T : ℝ, 0 < T → MemLp selection 2 (volume.restrict (Set.Icc 0 T))
  deriv_memLp : ∀ T : ℝ, 0 < T → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 T))
  /-- The strong derivative identity implicit in an orbit of the differential inclusion. -/
  deriv_hasDerivAt : ∀ T : ℝ, 0 < T →
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t
  /-- The Hilbert-valued fundamental theorem for the strong orbit velocity. -/
  deriv_integral_eq_sub : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    x t - x s = ∫ r in s..t, deriv x r
  equation_ae : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
    deriv x t + selection t + B (x t) = 0
  residual : ℝ → H
  residual_mem : ∀ t : ℝ, 0 ≤ t →
    residual t ∈ ERealFunction.subdifferential Phi (x t) + ({B (x t)} : Set H)
  residual_eq_neg_deriv : residual =ᵐ[volume.restrict (Set.Ici 0)] fun t ↦ -deriv x t
  residual_minimal : ∀ t : ℝ, 0 ≤ t → ∀ w ∈
    ERealFunction.subdifferential Phi (x t) + ({B (x t)} : Set H), ‖residual t‖ ≤ ‖w‖
  residual_norm_antitone : AntitoneOn (fun t ↦ ‖residual t‖) (Set.Ici 0)

private theorem integrableOn_Ici_of_nonneg_interval_bound
    {g : ℝ → ℝ} {a C : ℝ}
    (hlocal : ∀ T, IntegrableOn g (Set.Ioc a T))
    (hnonneg : ∀ s, a ≤ s → 0 ≤ g s)
    (hbound : ∀ T, a ≤ T → ∫ s in a..T, g s ≤ C) :
    IntegrableOn g (Set.Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded C a hlocal
    Filter.tendsto_id
  filter_upwards [Filter.eventually_ge_atTop a] with T hT
  have hnorm : (∫ s in a..T, ‖g s‖) = ∫ s in a..T, g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le hT] at hs
    exact Real.norm_of_nonneg (hnonneg s hs.1.le)
  rw [hnorm]
  exact hbound T hT

private theorem uniformContinuousOn_of_deriv_integral_eq_sub_sq
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
        (volume.restrict (Set.Ioc s t)) :=
      MeasureTheory.memLp_const 1
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
            Real.sqrt (∫ r in Set.Ioc s t, ‖deriv x r‖ ^ 2) *
              Real.sqrt (t - s) := hholder'
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
            _ < (C + 1) * (ε / (C + 1)) :=
              mul_lt_mul_of_pos_left hroot_len hC1
            _ = ε := by field_simp
    rw [dist_eq_norm_sub, norm_sub_rev]
    exact hbound
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hdist
  rcases le_total s t with hst | hts
  · exact hforward hs hst hdist
  · simpa [dist_comm] using hforward ht hts (by simpa [dist_comm] using hdist)

private theorem uniformContinuousOn_sq_integrable_tendsto_zero
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
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2 := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact sq_nonneg _
  change |(∫ x in Set.Ici (N : ℝ), ‖f x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

private theorem antitone_norm_sq_integrableOn_Ici_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (r : ℝ → E)
    (hanti : AntitoneOn (fun t => ‖r t‖) (Set.Ici 0))
    (hint : IntegrableOn (fun t : ℝ => ‖r t‖ ^ 2) (Set.Ici 0)) :
    Tendsto r atTop (nhds 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  rcases h with ⟨ε, hε, hbad⟩
  have htail : Tendsto (fun n : ℕ => ∫ x in Set.Ici (n : ℝ), ‖r x‖ ^ 2)
      atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_setIntegral_of_antitone
      (f := fun x : ℝ => ‖r x‖ ^ 2) (fun n : ℕ => measurableSet_Ici)
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
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) _ (sq_pos_of_pos hε)
  obtain ⟨u, huN, hubad⟩ := hbad ((N : ℝ) + 1)
  have hu0 : 0 ≤ u := by linarith
  have hlow : ∀ x ∈ Set.Ioc (u - 1) u, ε ^ 2 ≤ ‖r x‖ ^ 2 := by
    intro x hx
    have hub : ε ≤ ‖r u‖ := by simpa using hubad
    have hxu : x ≤ u := hx.2
    have hxnorm : ‖r u‖ ≤ ‖r x‖ :=
      hanti (Set.mem_Ici.mpr (by linarith [hx.1])) (Set.mem_Ici.mpr hu0) hxu
    nlinarith [norm_nonneg (r x)]
  have hint_lower : ε ^ 2 ≤ ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 := by
    calc
      ε ^ 2 = ∫ x in Set.Ioc (u - 1) u, ε ^ 2 := by
        rw [MeasureTheory.integral_const]
        simp
      _ ≤ ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 := by
        apply MeasureTheory.integral_mono_ae
        · exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
        · exact hint.mono_set (by
            intro x hx
            have : 0 ≤ x := by linarith [hx.1]
            exact this)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
          exact hlow x hx
  have hinter : Set.Ioc (u - 1) u ⊆ Set.Ici (N : ℝ) := by
    intro x hx
    exact (by linarith [hx.1, huN] : (N : ℝ) < x).le
  have hint_upper : ∫ x in Set.Ioc (u - 1) u, ‖r x‖ ^ 2 ≤
      ∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2 := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hint.mono_set (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg N))
    · filter_upwards with x
      exact sq_nonneg _
    · exact hinter.eventuallyLE
  have hN' := hN N le_rfl
  have htail_nonneg : 0 ≤ ∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2 := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact sq_nonneg _
  change |(∫ x in Set.Ici (N : ℝ), ‖r x‖ ^ 2) - 0| < _ at hN'
  simp only [sub_zero, abs_of_nonneg htail_nonneg] at hN'
  linarith

private theorem sqdist_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H} {a b : ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b) (z : H) :
    AbsolutelyContinuousOnInterval (fun t => (1 / 2 : ℝ) * ‖x t - z‖ ^ 2) a b := by
  have hsub : AbsolutelyContinuousOnInterval (fun t => x t - z) a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
      contDiffOn_const.absolutelyContinuousOnInterval
    simpa using hx.sub hconst
  have hnorm : AbsolutelyContinuousOnInterval (fun t => ‖x t - z‖) a b := by
    rw [absolutelyContinuousOnInterval_iff] at hsub ⊢
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hsub ε hε
    refine ⟨δ, hδ, ?_⟩
    intro E hE hsum
    refine lt_of_le_of_lt ?_ (hbound _ hE hsum)
    apply Finset.sum_le_sum
    intro i hi
    simpa [Real.norm_eq_abs, dist_eq_norm] using
      (abs_norm_sub_norm_le (x (E.2 i).1 - z) (x (E.2 i).2 - z))
  have hsq : AbsolutelyContinuousOnInterval
      (fun t => ‖x t - z‖ * ‖x t - z‖) a b := hnorm.mul hnorm
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq.const_mul (1 / 2 : ℝ)

private theorem inner_const_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℝ → H} {a b : ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b) (z : H) :
    AbsolutelyContinuousOnInterval (fun t => inner ℝ z (x t)) a b := by
  have hinner : AbsolutelyContinuousOnInterval (fun t => inner ℝ (x t) z) a b := by
    unfold AbsolutelyContinuousOnInterval at hx ⊢
    apply squeeze_zero (fun E => ?_) (fun E => ?_)
      (by simpa using hx.const_mul ‖z‖)
    · exact Finset.sum_nonneg fun _ _ => dist_nonneg
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.dist_eq, ← inner_sub_left]
      calc
        |inner ℝ (x (E.2 i).1 - x (E.2 i).2) z| ≤
            ‖x (E.2 i).1 - x (E.2 i).2‖ * ‖z‖ := abs_real_inner_le_norm _ _
        _ = ‖z‖ * dist (x (E.2 i).1) (x (E.2 i).2) := by
          rw [dist_eq_norm_sub, mul_comm]
  simpa only [real_inner_comm] using hinner

private theorem semigroup_lyapunov_absolutelyContinuousOnInterval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Phi : H → Set.Ioi (⊥ : EReal)} {B : H → H} {x : ℝ → H}
    {beta a b : ℝ} (hx : AbsolutelyContinuousOnInterval x a b)
    (hphi : AbsolutelyContinuousOnInterval (fun t => (Phi (x t) : EReal).toReal) a b)
    (z : H) :
    AbsolutelyContinuousOnInterval (fun t =>
      (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
        2 * beta * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
          inner ℝ (B z) (x t - z))) a b := by
  have hdist := sqdist_absolutelyContinuousOnInterval hx z
  have hconst_phi : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => (Phi z : EReal).toReal) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  have hphi' := hphi.sub hconst_phi
  have hinner : AbsolutelyContinuousOnInterval (fun t => inner ℝ (B z) (x t)) a b :=
    inner_const_absolutelyContinuousOnInterval hx (B z)
  have hconst_inner : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => inner ℝ (B z) z) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  have hinner' := hinner.sub hconst_inner
  simpa [inner_sub_right, mul_add, mul_sub, mul_assoc] using
    hdist.add ((hphi'.add hinner').const_mul (2 * beta))

private theorem inner_tendsto_zero_of_tendsto_zero_of_bounded_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : ℕ → H)
    (ha : Tendsto a atTop (nhds 0))
    (hb : Bornology.IsBounded (Set.range b)) :
    Tendsto (fun n ↦ inner ℝ (a n) (b n)) atTop (nhds 0) := by
  rcases (isBounded_iff_forall_norm_le (s := Set.range b)).mp hb with ⟨C, hC⟩
  let M : ℝ := max C 0
  have hbM (n : ℕ) : ‖b n‖ ≤ M :=
    le_trans (hC (b n) ⟨n, rfl⟩) (le_max_left _ _)
  have hanorm : Tendsto (fun n ↦ ‖a n‖) atTop (nhds 0) := by
    simpa using ha.norm
  have hbound (n : ℕ) : |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
    calc
      |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
      _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hbM n) (norm_nonneg _)
  have hmajor : Tendsto (fun n ↦ ‖a n‖ * M) atTop (nhds 0) := by
    simpa [zero_mul] using hanorm.mul tendsto_const_nhds
  have habs : Tendsto (fun n ↦ |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
    squeeze_zero (fun _ ↦ abs_nonneg _) hbound hmajor
  have hneg : Tendsto (fun n ↦ -|inner ℝ (a n) (b n)|) atTop (nhds 0) := by
    simpa using habs.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
  · intro n
    exact neg_abs_le _
  · intro n
    exact le_abs_self _

/-- Theorem 4.1: finite energy and convergence for an orbit of (59). -/
theorem semigroup_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (x : ℝ → H) (beta : ℝ)
    (hS : S.Nonempty) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (horbit : ForwardBackwardSemigroupOrbit Phi B x) :
    IntegrableOn (fun t ↦ ‖deriv x t‖ ^ 2) (Set.Ici 0) ∧
    (∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))) ∧
    ∀ z ∈ S, Tendsto (fun t ↦ B (x t)) atTop (nhds (B z)) := by
  rcases horbit with ⟨hlocalAC, v, hsubgrad, hdomain, hvL2, hdxL2, hdiff, hFTC, hequation,
    residual, hresMem, hresDeriv, hresMinimal, hresAntitone⟩
  have hchain (T : ℝ) (hT : 0 < T) :
      AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t) := by
    apply subgradient_chain_rule Phi hPhi x v T hT (hlocalAC T hT)
    · exact ae_restrict_of_ae_restrict_of_subset (fun _ ht ↦ ht.1) hsubgrad
    · intro t ht
      exact hdomain t ht.1
    · exact hdiff T hT
    · exact hvL2 T hT
    · exact hdxL2 T hT
  have hlyap (T : ℝ) (hT : 0 < T) (z : H) (hz : z ∈ S) :
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2) t +
          beta * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    filter_upwards [hdiff T hT, (hchain T hT).2,
      ae_restrict_of_ae_restrict_of_subset (fun _ ht ↦ ht.1) hsubgrad,
      ae_restrict_of_ae_restrict_of_subset (fun _ ht ↦ ht.1) hequation] with
      t hdiff_t hchain_t hsub_t heq_t
    have hhz : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hdiff_t.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have h62 : deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2) t =
        inner ℝ (x t - z) (deriv x t) := hhz.deriv
    have hmono := ERealFunction.isMonotone_subdifferential (fun y : H ↦ (Phi y : EReal))
      (ERealFunction.isProper_of_mem_gammaZero hPhi) (v t) hsub_t (-B z)
        ((hsolution z).mp hz)
    have hcoco := hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hmono' : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      rw [real_inner_comm]
      simpa [inner_sub_right, inner_add_right, inner_neg_right] using hmono
    have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
        inner ℝ (x t - z) (B (x t) - B z) := by
      simpa using hcoco
    have heq' : inner ℝ (x t - z) (deriv x t) =
        -inner ℝ (x t - z) (v t) - inner ℝ (x t - z) (B (x t)) := by
      have hvec : deriv x t = -(v t + B (x t)) :=
        eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using heq_t)
      rw [show deriv x t = -v t - B (x t) by
        simpa [sub_eq_add_neg, add_comm] using hvec]
      simp [inner_sub_right, inner_neg_right]
    rw [h62, heq']
    rw [inner_add_right] at hmono'
    rw [inner_sub_right] at hcoco'
    linarith
  have henergy (T : ℝ) (hT : 0 < T) (z : H) (hz : z ∈ S) :
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
          2 * beta * ((Phi (x s) : EReal).toReal - (Phi z : EReal).toReal +
            inner ℝ (B z) (x s - z))) t +
          beta * ‖deriv x t‖ ^ 2 + beta * ‖v t + B z‖ ^ 2 ≤ 0 := by
    filter_upwards [hlyap T hT z hz, hdiff T hT, (hchain T hT).2,
      ae_restrict_of_ae (hchain T hT).1.ae_differentiableAt,
      ae_restrict_of_ae_restrict_of_subset (fun _ ht ↦ ht.1) hequation,
      ae_restrict_mem measurableSet_Icc] with
      t hlyap_t hdiff_t hchain_t hphi_diff heq_t ht
    have hphi : HasDerivAt (fun s ↦ (Phi (x s) : EReal).toReal)
        (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t) t :=
      (hphi_diff (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hlin : HasDerivAt (fun s ↦ inner ℝ (B z) (x s - z))
        (inner ℝ (B z) (deriv x t)) t := by
      simpa using (hasDerivAt_const (x := t) (B z)).inner ℝ (hdiff_t.sub_const z)
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hdiff_t.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hE : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        2 * beta * ((Phi (x s) : EReal).toReal - (Phi z : EReal).toReal +
          inner ℝ (B z) (x s - z)))
        (inner ℝ (x t - z) (deriv x t) +
          2 * beta * (inner ℝ (v t) (deriv x t) + inner ℝ (B z) (deriv x t))) t := by
      convert hsq.add (((hphi.sub_const _).add hlin).const_mul (2 * beta)) using 1
      rw [hchain_t]
    rw [hE.deriv]
    have hBdiff : B (x t) - B z = -(deriv x t + (v t + B z)) := by
      have hvec : B (x t) = -(deriv x t + v t) :=
        eq_neg_of_add_eq_zero_left (by simpa [add_comm, add_left_comm, add_assoc] using heq_t)
      rw [hvec]
      abel
    rw [hBdiff, norm_neg, norm_add_sq_real] at hlyap_t
    have hinner : inner ℝ (deriv x t) (v t + B z) =
        inner ℝ (v t) (deriv x t) + inner ℝ (B z) (deriv x t) := by
      simp [inner_add_right, real_inner_comm]
    rw [hsq.deriv, hinner] at hlyap_t
    linarith
  have hE_nonneg (z : H) (hz : z ∈ S) (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
        2 * beta * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
          inner ℝ (B z) (x t - z)) := by
    have hsub := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      ((hsolution z).mp hz) (hdomain t ht)
    have hk : 0 ≤ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
        inner ℝ (B z) (x t - z) := by
      rw [inner_neg_left] at hsub
      linarith
    exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hbeta.le) hk)
  have hfinite (z : H) (hz : z ∈ S) (T : ℝ) (hT : 0 < T) :
      ∫ t in 0..T, beta * ‖deriv x t‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 +
          2 * beta * ((Phi (x 0) : EReal).toReal - (Phi z : EReal).toReal +
            inner ℝ (B z) (x 0 - z)) := by
    let E : ℝ → ℝ := fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
      2 * beta * ((Phi (x s) : EReal).toReal - (Phi z : EReal).toReal +
        inner ℝ (B z) (x s - z))
    have hEac : AbsolutelyContinuousOnInterval E 0 T :=
      semigroup_lyapunov_absolutelyContinuousOnInterval (hlocalAC T hT)
        (hchain T hT).1 z
    have hdxsq : IntegrableOn (fun t ↦ ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
    have hDint : IntervalIntegrable (fun t ↦ beta * ‖deriv x t‖ ^ 2) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
        (IntegrableOn.mono_set (hdxsq.const_mul beta) Set.Ioc_subset_Icc_self)
    have hderiv_int : IntervalIntegrable (fun t ↦ -deriv E t) volume 0 T :=
      hEac.intervalIntegrable_deriv.neg
    have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        beta * ‖deriv x t‖ ^ 2 ≤ -deriv E t := by
      filter_upwards [henergy T hT z hz] with t ht
      dsimp [E]
      have hvnonneg : 0 ≤ beta * ‖v t + B z‖ ^ 2 :=
        mul_nonneg hbeta.le (sq_nonneg _)
      linarith
    have hint := intervalIntegral.integral_mono_ae_restrict hT.le hDint hderiv_int hpoint
    calc
      ∫ t in 0..T, beta * ‖deriv x t‖ ^ 2 ≤ ∫ t in 0..T, -deriv E t := hint
      _ = -(∫ t in 0..T, deriv E t) := by rw [intervalIntegral.integral_neg]
      _ = -(E T - E 0) := by rw [hEac.integral_deriv_eq_sub]
      _ ≤ E 0 := by
        have hET : 0 ≤ E T := hE_nonneg z hz T hT.le
        linarith
      _ = (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 +
          2 * beta * ((Phi (x 0) : EReal).toReal - (Phi z : EReal).toReal +
            inner ℝ (B z) (x 0 - z)) := rfl
  obtain ⟨z, hz⟩ := hS
  have hSnonempty : S.Nonempty := ⟨z, hz⟩
  have hscaled : IntegrableOn (fun t ↦ beta * ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    apply integrableOn_Ici_of_nonneg_interval_bound
      (C := (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 +
        2 * beta * ((Phi (x 0) : EReal).toReal - (Phi z : EReal).toReal +
          inner ℝ (B z) (x 0 - z)))
    · intro T
      by_cases hT : 0 < T
      · have hdxsq : IntegrableOn (fun t ↦ ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
          (memLp_two_iff_integrable_sq_norm (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
        exact IntegrableOn.mono_set (hdxsq.const_mul beta) Set.Ioc_subset_Icc_self
      · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
        exact integrableOn_empty
    · intro t ht
      exact mul_nonneg hbeta.le (sq_nonneg _)
    · intro T hT
      rcases hT.eq_or_lt with rfl | hT
      · simpa using hE_nonneg z hz 0 le_rfl
      · exact hfinite z hz T hT
  have hdxint : IntegrableOn (fun t ↦ ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    refine Integrable.congr (hscaled.const_mul beta⁻¹) ?_
    filter_upwards with t
    field_simp [hbeta.ne']
  have hx_uc : UniformContinuousOn x (Set.Ici 0) :=
    uniformContinuousOn_of_deriv_integral_eq_sub_sq hFTC hdxL2 hdxint
  have hBcont : Continuous B := by
    have hsub : Continuous (fun y : H => (⟨y, Set.mem_univ y⟩ : Set.univ)) :=
      continuous_id.subtype_mk _
    simpa [Function.comp_def] using (lipschitzWith_of_cocoercive hB).continuous.comp hsub
  have hBfinite (T : ℝ) (hT : 0 < T) (z : H) (hz : z ∈ S) :
      ∫ t in 0..T, beta * ‖B (x t) - B z‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 := by
    let hzfun : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2
    have hzac : AbsolutelyContinuousOnInterval hzfun 0 T :=
      sqdist_absolutelyContinuousOnInterval (hlocalAC T hT) z
    have hBdiffcont : ContinuousOn (fun t ↦ B (x t) - B z) (Set.Icc 0 T) := by
      simpa [Function.comp_def, Set.uIcc_of_le hT.le] using
        (hBcont.continuousOn.comp (hlocalAC T hT).continuousOn
          (Set.mapsTo_univ _ _)).sub continuousOn_const
    have hBint : IntervalIntegrable (fun t ↦ beta * ‖B (x t) - B z‖ ^ 2)
        volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
        (IntegrableOn.mono_set ((hBdiffcont.norm.pow 2).const_mul beta).integrableOn_Icc
          Set.Ioc_subset_Icc_self)
    have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        beta * ‖B (x t) - B z‖ ^ 2 ≤ -deriv hzfun t := by
      filter_upwards [hlyap T hT z hz] with t ht
      dsimp [hzfun]
      linarith
    have hint := intervalIntegral.integral_mono_ae_restrict hT.le hBint
      hzac.intervalIntegrable_deriv.neg hpoint
    calc
      ∫ t in 0..T, beta * ‖B (x t) - B z‖ ^ 2 ≤ ∫ t in 0..T, -deriv hzfun t := hint
      _ = -(∫ t in 0..T, deriv hzfun t) := by rw [intervalIntegral.integral_neg]
      _ = -(hzfun T - hzfun 0) := by rw [hzac.integral_deriv_eq_sub]
      _ ≤ hzfun 0 := by
        have : 0 ≤ hzfun T := by positivity
        linarith
      _ = (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 := rfl
  have hBscaled (z : H) (hz : z ∈ S) :
      IntegrableOn (fun t ↦ beta * ‖B (x t) - B z‖ ^ 2) (Set.Ici 0) := by
    apply integrableOn_Ici_of_nonneg_interval_bound
      (C := (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2)
    · intro T
      by_cases hT : 0 < T
      · have hcont : ContinuousOn (fun t ↦ B (x t) - B z) (Set.Icc 0 T) := by
          simpa [Function.comp_def, Set.uIcc_of_le hT.le] using
            (hBcont.continuousOn.comp (hlocalAC T hT).continuousOn
              (Set.mapsTo_univ _ _)).sub continuousOn_const
        exact IntegrableOn.mono_set ((hcont.norm.pow 2).const_mul beta).integrableOn_Icc
          Set.Ioc_subset_Icc_self
      · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
        exact integrableOn_empty
    · intro t _
      exact mul_nonneg hbeta.le (sq_nonneg _)
    · intro T hT
      rcases hT.eq_or_lt with rfl | hT
      · simp
      · exact hBfinite T hT z hz
  have hBsqint (z : H) (hz : z ∈ S) :
      IntegrableOn (fun t ↦ ‖B (x t) - B z‖ ^ 2) (Set.Ici 0) := by
    refine Integrable.congr ((hBscaled z hz).const_mul beta⁻¹) ?_
    filter_upwards with t
    field_simp [hbeta.ne']
  have hBlim (z : H) (hz : z ∈ S) :
      Tendsto (fun t ↦ B (x t)) atTop (nhds (B z)) := by
    have hBuc : UniformContinuous B := by
      have hsub : UniformContinuous (fun y : H => (⟨y, Set.mem_univ y⟩ : Set.univ)) :=
        uniformContinuous_id.subtype_mk _
      simpa [Function.comp_def] using (lipschitzWith_of_cocoercive hB).uniformContinuous.comp hsub
    have hcomp : UniformContinuousOn (fun t ↦ B (x t)) (Set.Ici 0) :=
      hBuc.uniformContinuousOn.comp hx_uc (Set.mapsTo_univ _ _)
    have hdiffuc : UniformContinuousOn (fun t ↦ B (x t) - B z) (Set.Ici 0) := by
      rw [Metric.uniformContinuousOn_iff] at hcomp ⊢
      intro ε hε
      rcases hcomp ε hε with ⟨δ, hδ, hprop⟩
      refine ⟨δ, hδ, ?_⟩
      intro s hs t ht hst
      simpa only [dist_sub_right] using hprop s hs t ht hst
    have hzero := uniformContinuousOn_sq_integrable_tendsto_zero
      (fun t ↦ B (x t) - B z) hdiffuc (hBsqint z hz)
    have hsum : Tendsto (fun t ↦ B z + (B (x t) - B z)) atTop (nhds (B z + 0)) :=
      tendsto_const_nhds.add hzero
    simpa using hsum
  have hdist (z : H) (hz : z ∈ S) : ∃ l : ℝ,
      Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l) := by
    have hanti : AntitoneOn (fun t ↦ ‖x t - z‖ ^ 2) (Set.Ici 0) := by
      intro s hs t ht hst
      by_cases htzero : t = 0
      · simp [htzero, le_antisymm (by simpa [htzero] using hst) hs]
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
        let hzfun : ℝ → ℝ := fun r ↦ (1 / 2 : ℝ) * ‖x r - z‖ ^ 2
        have hzac : AbsolutelyContinuousOnInterval hzfun 0 t :=
          sqdist_absolutelyContinuousOnInterval (hlocalAC t htpos) z
        have hsac : AbsolutelyContinuousOnInterval hzfun s t :=
          hzac.mono (by
            rw [Set.uIcc_of_le hst, Set.uIcc_of_le htpos.le]
            exact Set.Icc_subset_Icc hs le_rfl)
        have hpoint : ∀ᵐ r ∂volume.restrict (Set.Icc s t), deriv hzfun r ≤ 0 := by
          apply ae_restrict_of_ae_restrict_of_subset
            (show Set.Icc s t ⊆ Set.Icc 0 t from fun r hr => ⟨le_trans hs hr.1, hr.2⟩)
          filter_upwards [hlyap t htpos z hz] with r hr
          dsimp [hzfun]
          have hnonneg : 0 ≤ beta * ‖B (x r) - B z‖ ^ 2 :=
            mul_nonneg hbeta.le (sq_nonneg _)
          linarith
        have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume s t :=
          intervalIntegrable_const
        have hint := intervalIntegral.integral_mono_ae_restrict hst
          hsac.intervalIntegrable_deriv hzero hpoint
        rw [hsac.integral_deriv_eq_sub] at hint
        dsimp [hzfun] at hint
        simp at hint
        nlinarith
    have hbelow : BddBelow (Set.range (fun t ↦ ‖x t - z‖ ^ 2)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact sq_nonneg _
    let F : ℝ → ℝ := fun t ↦ ‖x (max t 0) - z‖ ^ 2
    have hFanti : Antitone F := by
      intro s t hst
      exact hanti (Set.mem_Ici.mpr (le_max_right _ _))
        (Set.mem_Ici.mpr (le_max_right _ _)) (max_le_max_right _ hst)
    have hFbelow : BddBelow (Set.range F) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨t, rfl⟩
      dsimp [F]
      exact sq_nonneg _
    have hsqF : Tendsto F atTop (nhds (⨅ t, F t)) := tendsto_atTop_ciInf hFanti hFbelow
    have hsq : Tendsto (fun t ↦ ‖x t - z‖ ^ 2) atTop (nhds (⨅ t, F t)) := by
      apply hsqF.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [F, max_eq_left ht]
    refine ⟨Real.sqrt (⨅ t, F t), ?_⟩
    have hsqrt := Real.continuous_sqrt.tendsto _ |>.comp hsq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  have hressqint : IntegrableOn (fun t ↦ ‖residual t‖ ^ 2) (Set.Ici 0) := by
    refine Integrable.congr hdxint ?_
    filter_upwards [hresDeriv] with t ht
    rw [ht, norm_neg]
  have hreszero : Tendsto residual atTop (nhds 0) :=
    antitone_norm_sq_integrableOn_Ici_tendsto_zero residual hresAntitone hressqint
  refine ⟨hdxint, ?_⟩
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
    obtain ⟨z0, hz0⟩ := hSnonempty
    let r : ℕ → H := fun n ↦ residual (q n) - B (x (q n))
    have hr : Tendsto r atTop (nhds (-B z0)) := by
      simpa [r] using (hreszero.comp hq_top).sub ((hBlim z0 hz0).comp hq_top)
    have hr_mem : ∀ n, r n ∈ ERealFunction.subdifferential Phi (x (q n)) := by
      intro n
      rcases Set.mem_add.mp (hresMem (q n) (hq_nonneg n)) with ⟨a, ha, b, hb, hab⟩
      have hb' : b = B (x (q n)) := by simpa using hb
      change residual (q n) - B (x (q n)) ∈ ERealFunction.subdifferential Phi (x (q n))
      rw [← hb']
      have hsub : residual (q n) - b = a := by
        rw [← hab]
        abel
      rw [hsub]
      exact ha
    have hBq : Tendsto (fun n ↦ B (x (q n))) atTop (nhds (B z0)) :=
      (hBlim z0 hz0).comp hq_top
    let d : H := B z0 - B z
    have hdiff : Tendsto (fun n ↦ B (x (q n)) - B z) atTop (nhds d) := by
      simpa [d] using hBq.sub tendsto_const_nhds
    have herr : Tendsto (fun n ↦ B (x (q n)) - B z - d) atTop (nhds 0) := by
      simpa [d] using hdiff.sub (tendsto_const_nhds (x := B z0 - B z))
    have hxbdd : Bornology.IsBounded (Set.range (fun n ↦ x (q n))) :=
      bounded_range_of_tendsto_weakly hq_weak
    have hcross : Tendsto
        (fun n ↦ inner ℝ (x (q n) - z) (B (x (q n)) - B z - d)) atTop (nhds 0) := by
      have hcross' : Tendsto
          (fun n ↦ inner ℝ (B (x (q n)) - B z - d) (x (q n) - z)) atTop (nhds 0) := by
        apply inner_tendsto_zero_of_tendsto_zero_of_bounded_range _ _ herr
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
    have hBz : B z = B z0 := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp hdnorm)).symm
    have hclosed : -B z0 ∈ ERealFunction.subdifferential Phi z :=
      maximal_monotone_graph_weak_strong_closed
        (ERealFunction.subdifferential Phi)
        (ERealFunction.subdifferential_isMaximalMonotone_of_mem_gammaZero hPhi)
        (fun n ↦ x (q n)) r z (-B z0) hq_weak hr hr_mem
    apply (hsolution z).mpr
    simpa [hBz] using hclosed
  obtain ⟨zinf, hzinf, hxweak⟩ :=
    opial_trajectory_lemma S x hSnonempty hdist hcluster
  exact ⟨⟨zinf, hzinf, hxweak⟩, hBlim⟩

end AbbasDynamical2015
