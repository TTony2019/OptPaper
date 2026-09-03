## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/thm_2.lean`

## Lean statement
```lean
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
    ∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
Let H be a real Hilbert space: it is a type with a normed additive group structure, a real inner product space structure, and completeness. Fix a set S in H, and let Phi be an extended-real-valued function on H whose values lie strictly above the bottom element of EReal, so the value -∞ is excluded. Let B:H→H, let x,v:ℝ→H be curves, and let lam and beta be real numbers.

The hypotheses are:
- S is nonempty.
- lam > 0 and beta > 0.
- B is beta-cocoercive on the whole space H.
- For almost every t ≥ 0 with respect to Lebesgue measure restricted to [0,∞), the forward-backward evolution equation holds:
  lam • deriv x t + deriv v t + v t + B (x t) = 0.
- For every b > 0, both x and v are absolutely continuous on the interval [0,b].
- For every T > 0, for almost every t ∈ [0,T], deriv x t is actually the derivative of x at t; similarly deriv v t is the derivative of v at t.
- For every T > 0, v is in L² on [0,T], and deriv x is in L² on [0,T].
- For every t ≥ 0, v t belongs to the subdifferential of Phi at x t.
- For every point z, z belongs to S exactly when -B z belongs to the subdifferential of Phi at z. Thus S is the set of equilibrium points of the inclusion: -B z ∈ ∂Phi(z).

The conclusion is fourfold:
1. ‖v t + B (x t)‖ tends to 0 as t → ∞.
2. For every z ∈ S, B (x t) tends to B z as t → ∞.
3. For every z ∈ S, v t tends to -B z as t → ∞.
4. There exists some z ∈ S such that x t converges weakly to z as t → ∞, expressed using the map to the weak topological space `toWeakSpace ℝ H`.

## Lean proof
```lean
by
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
```

## Proof explanation
The proof begins by using the nonemptiness of S to choose a point z₀ ∈ S. From the fact that Phi belongs to the class `gammaZero` and from hsubgradient and hsolution, the argument first shows that every x t with t ≥ 0 and every z ∈ S lies in the effective domain of Phi. It also combines the a.e. differential equation with the subgradient condition into one `horbit_pair`: almost everywhere on [0,∞), both v t ∈ ∂Phi(x t) and the differential equation hold.

The central analytic input is then obtained by invoking `proposition_2_12` with the coefficient lam⁻¹. The variable lam⁻¹ is positive because lam > 0. This proposition supplies a large Lyapunov-style package: gamma along the orbit has a limit; the square of ‖B(x t) - B z₀‖ is integrable on [0,∞); x is bounded; derivative norms are square-integrable; derivative of v is square-integrable; and an energy term has a limit. The proof uses `rcases` to decompose this package into its named pieces, for example hBsq for the integrability of ‖B(x t)-B z₀‖², hdxsq and hdvsq for the L² estimates, hxBound for the boundedness of x, and hEnergyLim for the energy limit.

Next the proof builds the fundamental theorem of calculus for x and v on intervals [s,t] with 0 ≤ s ≤ t. The zero endpoint cases are handled separately, and the nonsingleton cases use absolute continuity, the a.e. derivative hypotheses, and the integrability of deriv x and deriv v. The resulting identities express x t - x s and v t - v s as interval integrals of their derivatives.

From these identities and the square-integrability estimates, a library lemma gives uniform continuity of x and v on [0,∞). B itself is uniformly continuous because a cocoercive map is Lipschitz, and composing this uniform continuity of B with that of x gives uniform continuity of B∘x. Subtracting the constant B z₀ preserves uniform continuity. A general lemma, `uniformContinuousOn_sq_integrable_tendsto_zero_local`, converts uniform continuity plus square-integrability on [0,∞) into convergence to zero at infinity. Applied to B(x t)-B z₀, it gives B(x t) → B z₀.

The proof then shows that v t + B(x t) is uniformly continuous and lies in L² on [0,∞). The L² bound is a pointwise estimate obtained from the differential equation: v t + B(x t) equals -(lam • deriv x t + deriv v t), and its squared norm is bounded by a combination of ‖deriv x t‖² and ‖deriv v t‖² using the triangle inequality and the inequality (a+b)² ≤ 2a²+2b². In the formal proof this is done after `filter_upwards [horbit]`, which uses the a.e. equation pointwise, followed by arithmetic simplifications and `linarith`-type estimates. Then the same uniform-continuity-plus-square-integrability lemma gives v t + B(x t) → 0. Its norm therefore also tends to 0, proving the first conclusion.

Since B(x t)-B z₀ → 0 and v t + B(x t) → 0, their difference v t + B z₀ tends to 0, hence v t → -B z₀. A separate argument, using the theorem `operator_constant_on_solution_set_local`, proves that B is constant on S, so B z = B z₀ for every z ∈ S. Therefore, for every z ∈ S, B(x t) → B z and v t → -B z. This proves the second and third conclusions.

For the fourth, weak convergence of x, the proof uses an Opial-type trajectory lemma. For an arbitrary z ∈ S, it applies `proposition_2_12` again, this time to z, to obtain the limit of the Lyapunov/energy expression associated with z. Combining this with the already proved convergence v t → -B z, and expanding the gamma expression using inner-product algebra, the proof shows that ‖x t - z‖² has a limit as t → ∞. This is the key fact `hdist`: for every z ∈ S, the distance ‖x t - z‖ tends to some real limit.

The proof then establishes a cluster-point property: if a subsequence of x(t_n) converges weakly to some z, then z must belong to S. In more detail, after passing to a subsubsequence with nonnegative times, weak convergence x(t_n) ⇀ z and strong convergence v(t_n) → -B z₀ are known. Using beta-cocoercivity of B, the proof shows that the distance between B z and B z₀ must be zero, so B z = B z₀. Then, because the graph of the subdifferential of Phi is maximal monotone and closed under mixed weak-strong limits, the facts v(t_n) ∈ ∂Phi(x(t_n)), x(t_n) ⇀ z, and v(t_n) → -B z₀ imply -B z₀ ∈ ∂Phi(z). By the hypothesis characterizing S, this gives z ∈ S.

Finally, the proof applies the Opial trajectory lemma: since S is nonempty, for every z ∈ S the distance ‖x t - z‖ has a limit, and every weak subsequential limit of x is in S, the whole trajectory x t must converge weakly to some point of S. This is the final existential statement.

The important Lean commands used in the proof have the following roles: `obtain` and `rcases` destruct existential claims or split conjunctive data; `intro` proves universal statements by naming arbitrary variables; `have` creates intermediate claims; `filter_upwards` applies pointwise or a.e. arguments inside filtered limits; `rw` rewrites a goal using equalities such as inner-product or norm identities; `simp` simplifies goals, especially trivial zero or endpoint cases; `exact` closes a goal by providing a precisely matching proof term; and `linarith` solves linear inequalities arising from estimates like the epsilon/2 distance bound. The proof is a single long formal argument that ends by combining the previously established limits with `opial_trajectory_lemma`.

