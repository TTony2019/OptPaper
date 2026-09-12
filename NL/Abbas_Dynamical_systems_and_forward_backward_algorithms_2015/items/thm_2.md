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
Let \(H\) be a real inner product space which is complete, hence a Hilbert space. Let \(S\subseteq H\) be a nonempty set. Let
\[
\Phi:H\to (-\infty,+\infty]
\]
be an extended-real-valued function, encoded in Lean as a map into the subtype of extended reals strictly greater than \(-\infty\). Assume \(\Phi\in\Gamma_0(H)\), i.e. \(\Phi\) is proper, convex, and lower semicontinuous. Let \(B:H\to H\) be a single-valued operator, let \(\beta>0\), and assume that \(B\) is \(\beta\)-cocoercive on all of \(H\): for all \(u,w\in H\),
\[
\beta\|B(u)-B(w)\|^2\le \langle u-w,B(u)-B(w)\rangle .
\]
Let \(x,v:\mathbb R\to H\) be two trajectories, and let \(\lambda>0\). The hypotheses of the theorem say, in mathematical language, that:

- \(S\) is the solution set of the equilibrium/subdifferential inclusion:
\[
z\in S \quad\Longleftrightarrow\quad -B(z)\in\partial\Phi(z).
\]
- Almost everywhere on \([0,\infty)\) with respect to Lebesgue measure, the orbit equation holds:
\[
\lambda\,\operatorname{deriv} x(t)+\operatorname{deriv} v(t)+v(t)+B(x(t))=0.
\]
- For every \(b>0\), \(x\) and \(v\) are absolutely continuous on \([0,b]\).
- For every \(T>0\), almost everywhere on \([0,T]\), \(x\) and \(v\) have derivatives equal to \(\operatorname{deriv} x(t)\) and \(\operatorname{deriv} v(t)\), respectively.
- \(v\) and \(\operatorname{deriv} x\) are locally square-integrable on intervals \([0,T]\), \(T>0\).
- For every \(t\ge0\),
\[
v(t)\in\partial\Phi(x(t)).
\]

The conclusion is fourfold. First, the residual tends to zero:
\[
\|v(t)+B(x(t))\|\to0 \qquad (t\to\infty).
\]
Second, for every equilibrium \(z\in S\), the image \(B(x(t))\) converges strongly to \(B(z)\):
\[
\forall z\in S,\qquad B(x(t))\to B(z).
\]
Third, for every \(z\in S\), the subgradient trajectory converges strongly to \(-B(z)\):
\[
\forall z\in S,\qquad v(t)\to -B(z).
\]
Fourth, the primal trajectory has a weak limit in the solution set:
\[
\exists z\in S,\qquad x(t)\rightharpoonup z
\]
weakly as \(t\to\infty\). Thus the theorem states convergence of the continuous-time forward-backward dynamical system to an equilibrium in \(S\), with strong convergence of \(v+B(x)\) and of the quantities \(B(x(t))\) and \(v(t)\), and weak convergence of \(x(t)\).

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
The proof begins by choosing an element \(z_0\in S\), using `obtain ⟨z₀, hz₀⟩ := hS`, which is possible because \(hS\) says that \(S\) is nonempty.

Next, the proof extracts a finiteness fact for \(\Phi\). The declaration `isProper_of_mem_gammaZero` says that if \(\Phi\in\Gamma_0(H)\), then the function \(x\mapsto \Phi(x)\), viewed as an extended-real-valued function, is proper. In particular, its effective domain
\[
\operatorname{dom}\Phi=\{x\in H:\Phi(x)<+\infty\}
\]
is nonempty. The proof writes this as `hdomPhi`. It then shows that both the trajectory \(x(t)\) and every equilibrium \(z\in S\) lie in the effective domain of \(\Phi\). For \(x(t)\), this follows from the subgradient hypothesis \(v(t)\in\partial\Phi(x(t))\): the lemma `SubdifferentiableAt.mem_effectiveDomain` says that a point admitting a subgradient lies in the effective domain. For \(z\in S\), the same argument is applied to \(-B(z)\in\partial\Phi(z)\), which holds by the characterization of \(S\). This gives
\[
\forall t\ge0,\quad x(t)\in\operatorname{dom}\Phi,
\qquad
\forall z\in S,\quad z\in\operatorname{dom}\Phi.
\]
This is necessary because the later Lyapunov function uses the real numbers \((\Phi z)_{\mathbb R}\) and \((\Phi(x(t)))_{\mathbb R}\), which require finite values.

The proof then combines the almost-everywhere orbit equation with the everywhere subgradient condition. Using `filter_upwards` with `ae_restrict_mem measurableSet_Ici`, it obtains an almost-everywhere statement on \([0,\infty)\) of the form
\[
v(t)\in\partial\Phi(x(t))
\quad\text{and}\quad
\lambda\,\operatorname{deriv} x(t)+\operatorname{deriv} v(t)+v(t)+B(x(t))=0.
\]
This paired statement is exactly what `proposition_2_12` expects.

Next, the proof applies `operator_constant_on_solution_set_local`. That theorem says that under the hypotheses \(\Phi\in\Gamma_0(H)\), \(\beta>0\), \(B\) \(\beta\)-cocoercive on all of \(H\), and
\[
z\in S\iff -B(z)\in\partial\Phi(z),
\]
the operator \(B\) is constant on \(S\): for all \(z,w\in S\), \(B(z)=B(w)\). Applying it to arbitrary \(z\in S\) and to the fixed \(z_0\in S\), the proof obtains
\[
\forall z\in S,\qquad B(z)=B(z_0).
\]
This will later identify all possible strong limits of \(B(x(t))\) and \(v(t)\).

The proof sets \(\mu=\lambda^{-1}\). Since \(\lambda>0\), \(\mu>0\), and \(\mu\lambda=1\). It then applies the cited theorem `proposition_2_12` with \(z=z_0\). That theorem is the Lyapunov/energy estimate for the system. In the present variables, it gives:

- the function
\[
\Gamma_{z_0}(t)
=\frac12\|x(t)-z_0\|^2
+\lambda^{-1}\Bigl(
(\Phi(z_0))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}
-\langle z_0-x(t),v(t)\rangle
\Bigr)
\]
is antitone on \([0,\infty)\), and it converges to some real limit as \(t\to\infty\);
- the function \(t\mapsto \|B(x(t))-B(z_0)\|^2\) is integrable on \([0,\infty)\);
- \(x\) is bounded on \([0,\infty)\);
- \(t\mapsto \|\operatorname{deriv} x(t)\|^2\) is integrable on \([0,\infty)\);
- \(t\mapsto \|\operatorname{deriv} v(t)+v(t)+B(z_0)\|^2\) is integrable on \([0,\infty)\);
- \(t\mapsto \|\operatorname{deriv} v(t)\|^2\) is integrable on \([0,\infty)\);
- \(v\) is bounded on \([0,\infty)\);
- the energy \(t\mapsto (\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z_0)\rangle\) converges to some real limit.

These are the outputs collected by `rcases hLyapunov with ...`.

Using the integrability of \(\|\operatorname{deriv} v\|^2\) on \([0,\infty)\), the proof obtains local \(L^2\) membership of \(\operatorname{deriv} v\). The criterion `memLp_two_iff_integrable_sq_norm` says that, for an almost-everywhere strongly measurable function, being in \(L^2\) is equivalent to integrability of the square of its norm. Since \(\operatorname{deriv} v\) is almost-everywhere strongly measurable, and since the square-norm integrability restricts from \([0,\infty)\) to \([0,T]\), the proof concludes
\[
\operatorname{deriv} v\in L^2([0,T])
\]
for every \(T>0\).

The proof then establishes the fundamental theorem of calculus for \(x\) and \(v\). The cited result `intervalIntegral_deriv_eq_sub_of_ac_ae_local` says that if \(a\le b\), \(f\) is absolutely continuous on \([a,b]\), \(\operatorname{deriv} f\) is interval-integrable on \([a,b]\), and almost everywhere on \([a,b]\) one has
\[
\operatorname{HasDerivAt} f\,(\operatorname{deriv} f(t))\,t,
\]
then
\[
\int_a^b \operatorname{deriv} f(t)\,dt=f(b)-f(a).
\]
The proof applies this to \(f=x\) and to \(f=v\), for \(0\le s\le t\). The cases \(t=0\) are trivial because then \(s=0\), handled by `simp`. In the nontrivial case \(t>0\), the local \(L^2\) hypotheses give integrability on \([s,t]\), the absolute continuity hypotheses restrict from \([0,t]\) to \([s,t]\), and the almost-everywhere derivative hypotheses restrict similarly. The conclusion is
\[
x(t)-x(s)=\int_s^t \operatorname{deriv} x(r)\,dr,
\qquad
v(t)-v(s)=\int_s^t \operatorname{deriv} v(r)\,dr
\]
whenever \(0\le s\le t\).

These FTC identities are then fed into the cited theorem `uniformContinuousOn_of_deriv_integral_eq_sub_sq_local`. That theorem says that if a curve satisfies the FTC on all nonnegative intervals, has locally \(L^2\) derivative on \([0,T]\), and has globally integrable squared derivative norm on \([0,\infty)\), then the curve is uniformly continuous on \([0,\infty)\). Applying it to \(x\) and to \(v\), the proof obtains
\[
x\text{ uniformly continuous on }[0,\infty),
\qquad
v\text{ uniformly continuous on }[0,\infty).
\]

Next, the proof shows \(B\) is uniformly continuous. The cited theorem `lipschitzWith_of_cocoercive` says that a \(\beta\)-cocoercive operator is Lipschitz with constant \(\operatorname{Real.toNNReal}(1/\beta)\), which is \(1/\beta\) because \(\beta>0\). Applying this to \(B\) restricted to all of \(H\) and composing with the inclusion \(y\mapsto \langle y,\operatorname{univ}\rangle\), the proof concludes that \(B:H\to H\) is uniformly continuous. Therefore the composition \(t\mapsto B(x(t))\) is uniformly continuous on \([0,\infty)\), because it is the composition of uniformly continuous maps. Subtracting the constant \(B(z_0)\) preserves uniform continuity, so
\[
t\mapsto B(x(t))-B(z_0)
\]
is uniformly continuous on \([0,\infty)\).

The proof now applies `uniformContinuousOn_sq_integrable_tendsto_zero_local`. That theorem says that if \(f\) is uniformly continuous on \([0,\infty)\) and \(\int_0^\infty \|f(t)\|^2\,dt<\infty\), then \(f(t)\to0\) as \(t\to\infty\). Here it is applied to \(f(t)=B(x(t))-B(z_0)\). The square-integrability was supplied by `proposition_2_12`. Hence
\[
B(x(t))-B(z_0)\to0.
\]

The proof then treats the residual \(v(t)+B(x(t))\). Since \(v\) and \(B\circ x\) are uniformly continuous on \([0,\infty)\), their sum is uniformly continuous. The proof next proves that the square of the residual is integrable. On the almost-everywhere set where the orbit equation holds,
\[
v(t)+B(x(t))
=-\bigl(\lambda\,\operatorname{deriv} x(t)+\operatorname{deriv} v(t)\bigr).
\]
Therefore, by the triangle inequality and the elementary inequality
\[
(a+b)^2\le 2a^2+2b^2,
\]
one has
\[
\|v(t)+B(x(t))\|^2
\le
\bigl(\lambda\|\operatorname{deriv} x(t)\|+\|\operatorname{deriv} v(t)\|\bigr)^2
\le
2\lambda^2\|\operatorname{deriv} x(t)\|^2
+2\|\operatorname{deriv} v(t)\|^2.
\]
The right-hand side is integrable on \([0,\infty)\) by the Lyapunov estimates. The proof uses `Integrable.mono'` to deduce that
\[
t\mapsto \|v(t)+B(x(t))\|^2
\]
is integrable on \([0,\infty)\). Applying `uniformContinuousOn_sq_integrable_tendsto_zero_local` once more, this time to the residual \(v+B(x)\), yields
\[
v(t)+B(x(t))\to0.
\]
Taking norms gives the first conclusion:
\[
\|v(t)+B(x(t))\|\to0.
\]

From here the proof derives the strong limits. Since
\[
v(t)+B(x(t))\to0
\quad\text{and}\quad
B(x(t))-B(z_0)\to0,
\]
subtracting gives
\[
v(t)+B(z_0)\to0,
\]
hence
\[
v(t)\to -B(z_0).
\]
Also
\[
B(x(t))=B(z_0)+(B(x(t))-B(z_0))\to B(z_0).
\]
Using the earlier constancy \(B(z)=B(z_0)\) for every \(z\in S\), the proof rewrites these limits as
\[
\forall z\in S,\qquad B(x(t))\to B(z),
\qquad
\forall z\in S,\qquad v(t)\to -B(z).
\]
These are the second and third conclusions of the theorem.

It remains to prove weak convergence of \(x(t)\). The proof uses the cited Opial trajectory lemma. To apply it, one must verify two hypotheses. First, for every \(z\in S\), the distance \(\|x(t)-z\|\) must converge as \(t\to\infty\). Second, every weak cluster point of \(x(t)\) at infinity must belong to \(S\).

For the distance convergence, the proof fixes \(z\in S\) and applies `proposition_2_12` again, now with this arbitrary \(z\). That gives a Lyapunov function
\[
\Gamma_z(t)
=
\frac12\|x(t)-z\|^2
+\lambda^{-1}\Bigl(
(\Phi(z))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle
\Bigr)
\]
which converges to some limit \(l_\Gamma\). It also gives convergence of the energy
\[
E_z(t)=(\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle
\]
to some limit \(l_E\). Since \(v(t)\to -B(z)\), one has
\[
\langle z,v(t)\rangle\to \langle z,-B(z)\rangle.
\]
Also \(x\) is bounded on \([0,\infty)\), say \(\|x(t)\|\le M\) eventually, and \(v(t)+B(z)\to0\). By Cauchy–Schwarz,
\[
|\langle x(t),v(t)+B(z)\rangle|
\le \|x(t)\|\,\|v(t)+B(z)\|
\le M\|v(t)+B(z)\|,
\]
so the cross term tends to \(0\). The proof uses the squeeze theorem `tendsto_of_tendsto_of_tendsto_of_le_of_le'` to conclude
\[
\langle x(t),v(t)+B(z)\rangle\to0.
\]
Therefore the gap
\[
(\Phi(z))_{\mathbb R}
-\bigl((\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle\bigr)
+\langle x(t),v(t)+B(z)\rangle
-\langle z,v(t)\rangle
\]
converges. The proof rewrites \(\Gamma_z(t)\) as
\[
\frac12\|x(t)-z\|^2
+\lambda^{-1}
\Bigl(
(\Phi(z))_{\mathbb R}
-\bigl((\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle\bigr)
+\langle x(t),v(t)+B(z)\rangle
-\langle z,v(t)\rangle
\Bigr),
\]
which is just the expansion of the inner product term. Since \(\Gamma_z(t)\) converges and the gap converges, the squared distance \(\|x(t)-z\|^2\) converges to an explicit real limit. Taking square roots, using continuity of the square root, gives convergence of \(\|x(t)-z\|\). Thus the first hypothesis of the Opial lemma holds for every \(z\in S\).

For the second hypothesis, the proof shows that every weak cluster point of \(x(t)\) at infinity belongs to \(S\). Suppose \(u_n\to\infty\) and
\[
x(u_n)\rightharpoonup z
\]
weakly. Since the sequence \(u_n\) may not be nonnegative, the proof shifts it by a large integer \(N\) so that \(q_n=u_{n+N}\ge0\) for all \(n\). Then \(q_n\to\infty\) and still
\[
x(q_n)\rightharpoonup z.
\]
From the previously established limits,
\[
v(q_n)\to -B(z_0),
\qquad
B(x(q_n))\to B(z_0).
\]
The proof sets \(d=B(z_0)-B(z)\). Then
\[
B(x(q_n))-B(z)-d\to0.
\]
The sequence \(x(q_n)-z\) is bounded: indeed weak convergence of \(x(q_n)\) to \(z\) implies boundedness of the range by `bounded_range_of_tendsto_weakly`, and subtracting the fixed vector \(z\) preserves boundedness. The cited lemma `inner_tendsto_zero_of_tendsto_zero_of_bounded_range_local` says that if \(a_n\to0\) and \(b_n\) has bounded range, then \(\langle a_n,b_n\rangle\to0\). Applying it to
\[
a_n=B(x(q_n))-B(z)-d,
\qquad
b_n=x(q_n)-z,
\]
and then using symmetry of the real inner product, gives
\[
\langle x(q_n)-z,B(x(q_n))-B(z)-d\rangle\to0.
\]
On the other hand, since \(x(q_n)\rightharpoonup z\), the cited weak-continuity theorem `weakSpace_continuous_inner_right` gives
\[
\langle x(q_n),d\rangle\to\langle z,d\rangle,
\]
so
\[
\langle x(q_n)-z,d\rangle\to0.
\]
Adding the last two limits yields
\[
\langle x(q_n)-z,B(x(q_n))-B(z)\rangle\to0.
\]
But \(\beta\)-cocoercivity gives, for every \(n\),
\[
\beta\|B(x(q_n))-B(z)\|^2
\le
\langle x(q_n)-z,B(x(q_n))-B(z)\rangle.
\]
Taking limits and using that limits preserve non-strict inequalities, the proof obtains
\[
\beta\|d\|^2\le0.
\]
Since \(\beta>0\), this forces \(\|d\|=0\), hence \(d=0\), i.e.
\[
B(z)=B(z_0).
\]
Now the proof uses maximal monotonicity of the subdifferential. The theorem `subdifferential_isMaximalMonotone_of_mem_gammaZero` says that if \(\Phi\in\Gamma_0(H)\), then \(\partial\Phi\) is a maximal monotone operator. The cited result `maximal_monotone_graph_weak_strong_closed` says that for a maximal monotone operator \(T\), if \(x_n\rightharpoonup x_0\), \(v_n\to v_0\) strongly, and \(v_n\in T(x_n)\) for all \(n\), then \(v_0\in T(x_0)\). Applying this to
\[
T=\partial\Phi,\qquad x_n=x(q_n),\qquad v_n=v(q_n),
\]
with weak limit \(z\) and strong limit \(-B(z_0)\), and using \(v(q_n)\in\partial\Phi(x(q_n))\), gives
\[
-B(z_0)\in\partial\Phi(z).
\]
Since \(B(z)=B(z_0)\), this is
\[
-B(z)\in\partial\Phi(z).
\]
By the defining characterization of \(S\), this implies \(z\in S\). Thus every weak cluster point of the trajectory belongs to \(S\).

Finally, the proof applies `opial_trajectory_lemma`. That lemma states that if \(S\) is nonempty, every distance \(\|x(t)-z\|\) with \(z\in S\) has a limit as \(t\to\infty\), and every weak cluster point of \(x(t)\) at infinity lies in \(S\), then there exists \(z\in S\) such that
\[
x(t)\rightharpoonup z
\]
weakly. All hypotheses have been verified: \(S\) is nonempty, the distance limits were proved using `proposition_2_12`, and the cluster-point property was proved using cocoercivity, weak continuity of the inner product, and maximal monotonicity of \(\partial\Phi\). This yields the final conclusion:
\[
\exists z\in S,\qquad x(t)\rightharpoonup z.
\]
Combined with the earlier strong limits of the residual, of \(B(x(t))\), and of \(v(t)\), this completes the proof of the theorem.

