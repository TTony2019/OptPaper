## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/thm_4.lean`

## Lean statement
```lean
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
    ∀ z ∈ S, Tendsto (fun t ↦ B (x t)) atTop (nhds (B z))
```

## Statement explanation
The declaration concerns a continuous-time forward-backward trajectory in a real Hilbert space $H$. The function $\Phi:H\to(-\infty,+\infty]$ is extended-real-valued and is assumed to lie in $\Gamma_0(H)$, the class of proper convex lower semicontinuous functions; the Lean type $H\to \mathrm{Ioi}(\bot:\mathbb E\mathbb R)$ encodes that $\Phi$ never takes the value $-\infty$. The set $S\subseteq H$ is nonempty, $B:H\to H$ is a forward operator, $x:\mathbb R\to H$ is a trajectory, and $\beta\gt 0$.

The hypotheses are:

- $B$ is $\beta$-cocoercive on all of $H$: for all $u,v\in H$,

```math
\langle Bu-Bv,u-v\rangle \ge \beta\|Bu-Bv\|^2.
```

- The set $S$ is exactly the solution set of the inclusion

$$
z\in S \quad\Longleftrightarrow\quad -Bz\in\partial\Phi(z),
$$

  equivalently $0\in Bz+\partial\Phi(z)$. Here $\partial\Phi$ is the subdifferential.
- $x$ is a forward-backward semigroup orbit for $\Phi$ and $B$. The proof unpacks this as follows: $x$ is locally absolutely continuous on every interval $[0,T]$ with $T\gt 0$; there is $v:\mathbb R\to H$ with $v(t)\in\partial\Phi(x(t))$ for almost every $t\ge0$; $x(t)$ lies in the effective domain of $\Phi$ for $t\ge0$; $v$ and $\dot x$ are locally $L^2$ on $[0,T]$; $x$ is differentiable almost everywhere; $x$ satisfies the fundamental-theorem-of-calculus identity

```math
x(t)-x(s)=\int_s^t \dot x(r)\,dr \qquad(0\le s\le t);
```

  and the differential inclusion is realized as the equation

$$
\dot x(t)+v(t)+B(x(t))=0
$$

  for almost every $t\ge0$. There is also a residual function $r:\mathbb R\to H$ such that

$$
r(t)-B(x(t))\in\partial\Phi(x(t)),
$$

$$
r(t)=-\dot x(t)\quad\text{for almost every }t\ge0,
$$

  and $`t\mapsto \|r(t)\|`$is antitone on$[0,\infty)$. The proof unpacks a further minimality field for$r$, but it is not used later.

The conclusion has three parts:

```math
\int_0^\infty \|\dot x(t)\|^2\,dt<\infty,
```

there exists $z\in S$ such that

$$
x(t)\rightharpoonup z \qquad(t\to\infty)
$$

weakly in $H$, and for every $z\in S$,

$$
B(x(t))\to Bz \qquad(t\to\infty)
$$

strongly. Thus the trajectory has finite energy, converges weakly to some solution, and the forward operator values converge strongly to the corresponding solution value.

## Lean proof
```lean
by
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
```

## Proof explanation
The proof proceeds as follows.

First, `rcases horbit` unpacks the forward-backward orbit hypothesis into local absolute continuity of $x$, the selection $v$ from the subdifferential, the effective-domain condition, local $L^2$ bounds, almost-everywhere differentiability, the fundamental-theorem identity, the differential equation, and the residual function $r$ with its membership, derivative identity, and antitone norm.

For each $T\gt 0$, the chain rule `subgradient_chain_rule` is applied to $\Phi$, $x$, and $v$ on $[0,T]$. Its mathematical content is: if $\Phi\in\Gamma_0(H)$, if $x$ is absolutely continuous on $[0,T]$, if $v(t)\in\partial\Phi(x(t))$ almost everywhere, if $x(t)\in\mathrm{dom}\Phi$, if $x$ is differentiable almost everywhere, and if $v,\dot x\in L^2(0,T)$, then

$$
t\mapsto (\Phi(x(t)))_{\mathbb R}
$$

is absolutely continuous on $[0,T]$, and almost everywhere

$$
\frac{d}{dt}(\Phi(x(t)))_{\mathbb R}
=\langle v(t),\dot x(t)\rangle.
$$

The restrictions from $[0,\infty)$ to $[0,T]$ are obtained with `ae_restrict_of_ae_restrict_of_subset`.

Next, the proof establishes the Lyapunov inequality `hlyap`: for every $T\gt 0$ and $z\in S$,

```math
\frac{d}{dt}\left(\frac12\|x(t)-z\|^2\right)
+\beta\|B(x(t))-Bz\|^2\le0
```

for almost every $t\in[0,T]$. The derivative of $`\frac12\|x(t)-z\|^2`$ is computed as

$$
\langle x(t)-z,\dot x(t)\rangle.
$$

Since $v(t)\in\partial\Phi(x(t))$ and $-Bz\in\partial\Phi(z)$, the monotonicity of the subdifferential, supplied by `isMonotone_subdifferential` together with properness from `isProper_of_mem_gammaZero`, gives

$$
0\le \langle x(t)-z,v(t)+Bz\rangle.
$$

Cocoercivity gives

```math
\beta\|B(x(t))-Bz\|^2
\le
\langle x(t)-z,B(x(t))-Bz\rangle.
```

The differential equation gives $\dot x(t)=-(v(t)+B(x(t)))$. Combining these inequalities yields the Lyapunov inequality. Here `rw` rewrites the derivative and inner-product expressions, and `linarith` closes the resulting arithmetic inequality.

The proof then defines the energy

```math
E_z(s)=\frac12\|x(s)-z\|^2
+2\beta\left((\Phi(x(s)))_{\mathbb R}-(\Phi(z))_{\mathbb R}
+\langle Bz,x(s)-z\rangle\right).
```

Using the chain rule for the $\Phi$-term and differentiating the square-distance and inner-product terms, the proof obtains

$$
E_z'(t)
=\langle x(t)-z,\dot x(t)\rangle
+2\beta\bigl(\langle v(t),\dot x(t)\rangle
+\langle Bz,\dot x(t)\rangle\bigr).
$$

The differential equation gives

$$
B(x(t))-Bz=-(\dot x(t)+v(t)+Bz).
$$

Expanding the square norm in the Lyapunov inequality and comparing with the derivative of $E_z$ gives the energy dissipation inequality `henergy`: for almost every $t\in[0,T]$,

```math
E_z'(t)+\beta\|\dot x(t)\|^2+\beta\|v(t)+Bz\|^2\le0.
```

The tactic `filter_upwards` combines the almost-everywhere hypotheses, and `linarith` finishes the algebra.

Next, the proof shows that $E_z(t)\ge0$ for $t\ge0$. It applies `subgradient_ineq_toReal_of_mem_gammaZero`: since $-Bz\in\partial\Phi(z)$ and $x(t)\in\mathrm{dom}\Phi$,

$$
(\Phi(x(t)))_{\mathbb R}
\ge
(\Phi(z))_{\mathbb R}
+\langle -Bz,x(t)-z\rangle
=(\Phi(z))_{\mathbb R}
-\langle Bz,x(t)-z\rangle.
$$

Hence

$$
(\Phi(x(t)))_{\mathbb R}-(\Phi(z))_{\mathbb R}
+\langle Bz,x(t)-z\rangle\ge0.
$$

Since $\beta\gt 0$ and $`\frac12\|x(t)-z\|^2\ge0`$, the energy$E_z(t)$ is nonnegative.

From the energy inequality and nonnegativity of $`\beta\|v(t)+Bz\|^2`$, the proof gets

```math
\beta\|\dot x(t)\|^2\le -E_z'(t)
```

almost everywhere on $[0,T]$. The energy $E_z$ is absolutely continuous by `semigroup_lyapunov_absolutelyContinuousOnInterval`, which combines absolute continuity of $x$ and of $(\Phi(x(t)))_{\mathbb R}$. Therefore the fundamental theorem of calculus applies:

```math
\int_0^T E_z'(t)\,dt=E_z(T)-E_z(0).
```

Since $E_z(T)\ge0$, this gives

```math
\int_0^T \beta\|\dot x(t)\|^2\,dt\le E_z(0).
```

Using `integrableOn_Ici_of_nonneg_interval_bound` with $`g(t)=\beta\|\dot x(t)\|^2`$,$a=0$, and$C=E_z(0)$, the proof concludes that$`\beta\|\dot x(t)\|^2`$is integrable on$[0,\infty)$. The cited lemma says that a locally integrable nonnegative function whose integrals over$[0,T]$are uniformly bounded has an integrable extension to$[0,\infty)$. Multiplying by$\beta^{-1}$ yields

```math
\int_0^\infty \|\dot x(t)\|^2\,dt<\infty,
```

which is the first conclusion.

The proof then applies `uniformContinuousOn_of_deriv_integral_eq_sub_sq` to $x$. Its content is: if $x$ satisfies the fundamental-theorem identity

```math
x(t)-x(s)=\int_s^t \dot x(r)\,dr,
```

if $\dot x$ is locally $L^2$ on $[0,T]$, and if $`\|\dot x\|^2`$is integrable on$[0,\infty)$, then$x$is uniformly continuous on$[0,\infty)$. Thus$x$ is uniformly continuous.

Cocoercivity implies a Lipschitz bound for $B$: `lipschitzWith_of_cocoercive` gives that $B$ is Lipschitz with constant $(1/\beta)_{\ge0}$. Hence $B$ is continuous and uniformly continuous.

For $z\in S$, the proof next bounds the forward residual. From the Lyapunov inequality,

```math
\beta\|B(x(t))-Bz\|^2
\le
-\frac{d}{dt}\left(\frac12\|x(t)-z\|^2\right).
```

The function $`t\mapsto \frac12\|x(t)-z\|^2`$ is absolutely continuous by `sqdist_absolutelyContinuousOnInterval`. Integrating over $[0,T]$ gives

```math
\int_0^T \beta\|B(x(t))-Bz\|^2\,dt
\le
\frac12\|x(0)-z\|^2.
```

Again using `integrableOn_Ici_of_nonneg_interval_bound`, this time with $`g(t)=\beta\|B(x(t))-Bz\|^2`$and$`C=\frac12\|x(0)-z\|^2`$, the proof gets integrability on$[0,\infty)$. After multiplying by$\beta^{-1}$,

```math
\int_0^\infty \|B(x(t))-Bz\|^2\,dt<\infty.
```

Since $B$ is uniformly continuous and $x$ is uniformly continuous, the map $t\mapsto B(x(t))-Bz$ is uniformly continuous. Because its square norm is integrable on $[0,\infty)$, the lemma `uniformContinuousOn_sq_integrable_tendsto_zero` gives

$$
B(x(t))-Bz\to0.
$$

Hence

$$
B(x(t))\to Bz
$$

strongly. This holds for every $z\in S$, proving the third conclusion.

To prepare for Opial’s lemma, the proof shows that for every $z\in S$, the distance $`\|x(t)-z\|`$has a finite limit as$t\to\infty$. It first proves that$`t\mapsto\|x(t)-z\|^2`$is antitone on$[0,\infty)$. Indeed, for$0\le s\le t$, the Lyapunov inequality gives

```math
\frac{d}{dr}\left(\frac12\|x(r)-z\|^2\right)\le0
```

almost everywhere on $[s,t]$. The function $`\frac12\|x(r)-z\|^2`$ is absolutely continuous by `sqdist_absolutelyContinuousOnInterval`, so integrating this inequality via the fundamental theorem of calculus yields

```math
\|x(t)-z\|^2\le\|x(s)-z\|^2.
```

Thus the square distance is antitone and bounded below by $0$. Extending it to all real $t$ by $`F(t)=\|x(\max(t,0))-z\|^2`$, the theorem `tendsto_atTop_ciInf` shows that $F(t)$ tends to its infimum at $+\infty$. Since eventually $`F(t)=\|x(t)-z\|^2`$, the square distance converges. Taking square roots, using continuity of$\sqrt{\cdot}$, gives a finite limit for$`\|x(t)-z\|`$.

The proof also proves convergence of the residual to zero. Since $r(t)=-\dot x(t)$ almost everywhere and $`\|\dot x\|^2`$is integrable,$`\|r(t)\|^2`$is integrable on$[0,\infty)$. Because$`\|r(t)\|`$ is antitone, the lemma `antitone_norm_sq_integrableOn_Ici_tendsto_zero` gives

$$
r(t)\to0.
$$

The next major step is showing that every weak cluster point of $x(t)$ as $t\to\infty$ belongs to $S$. Suppose $u_n\to\infty$ and $x(u_n)\rightharpoonup z$ weakly. After shifting, one may assume $u_n\ge0$. Choose $z_0\in S$, which is possible because $S$ is nonempty. Define

$$
r_n=r(u_n)-B(x(u_n)).
$$

The residual property gives $r_n\in\partial\Phi(x(u_n))$. Also $r(u_n)\to0$ and $B(x(u_n))\to Bz_0$, so

$$
r_n\to -Bz_0.
$$

To show $z\in S$, the proof first proves $Bz=Bz_0$. Let $d=Bz_0-Bz$. Since $B(x(u_n))\to Bz_0$, one has

$$
B(x(u_n))-Bz-d\to0.
$$

The weakly convergent sequence $x(u_n)$ is bounded in norm by `bounded_range_of_tendsto_weakly`. The lemma `inner_tendsto_zero_of_tendsto_zero_of_bounded_range` therefore gives

$$
\langle x(u_n)-z,B(x(u_n))-Bz-d\rangle\to0.
$$

Weak continuity of the inner product with fixed right argument, from `weakSpace_continuous_inner_right`, gives

$$
\langle x(u_n)-z,d\rangle\to0.
$$

Adding these two limits yields

$$
\langle x(u_n)-z,B(x(u_n))-Bz\rangle\to0.
$$

On the other hand, cocoercivity gives

```math
\beta\|B(x(u_n))-Bz\|^2
\le
\langle x(u_n)-z,B(x(u_n))-Bz\rangle.
```

The left side tends to $`\beta\|d\|^2`$. Taking limits in the inequality gives$`\beta\|d\|^2\le0`$, hence$d=0$, so$Bz=Bz_0$.

The proof then uses maximal monotonicity of the subdifferential. The theorem `subdifferential_isMaximalMonotone_of_mem_gammaZero` says that $\partial\Phi$ is maximal monotone because $\Phi\in\Gamma_0(H)$. The theorem `maximal_monotone_graph_weak_strong_closed` says that the graph of a maximal monotone operator is closed under weak convergence in the domain variable and strong convergence in the value variable. Applying it to $x(u_n)\rightharpoonup z$, $r_n\to -Bz_0$, and $r_n\in\partial\Phi(x(u_n))$, one obtains

$$
-Bz_0\in\partial\Phi(z).
$$

Since $Bz=Bz_0$, this is equivalent to

$$
-Bz\in\partial\Phi(z).
$$

By the characterization of $S$, this means $z\in S$. Thus every weak cluster point belongs to $S$.

Finally, the proof invokes `opial_trajectory_lemma`. Its statement is: if $S$ is nonempty, if for every $z\in S$ the distance $`\|x(t)-z\|`$has a finite limit as$t\to\infty$, and if every weak cluster point of$x(t)$at infinity lies in$S$, then there exists$z\in S$ such that

$$
x(t)\rightharpoonup z
$$

weakly. Applying this lemma gives the second conclusion.

Combining the established global integrability of $`\|\dot x\|^2`$, the weak convergence to some$z\in S$, and the strong convergence$B(x(t))\to Bz$for every$z\in S$, the proof finishes the theorem.

In the formal proof, `intro` introduces variables or hypotheses, `rw` rewrites with equalities such as derivative formulas and inner-product identities, `simp` and `simpa` simplify definitions and algebraic expressions, `linarith` and `nlinarith` close linear or nonlinear arithmetic inequalities, and `exact` supplies an already established lemma or proof term. Commands such as `filter_upwards` combine almost-everywhere assertions, while `calc` chains equalities and inequalities.

