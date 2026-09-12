## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/prop_1.lean`

## Lean statement
```lean
theorem projection_estimate_for_scalar_damped_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 uhat : H}
    (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hgamma : 0 < gamma)
    (hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v0))
    (hhat : uhat ∈ argmin Phi (potential_range_bddBelow hPhi))
    (hWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) Filter.atTop
      (nhds (toWeakSpace ℝ H uhat)))
    (hS_cheb : IsChebyshev (argmin Phi (potential_range_bddBelow hPhi)))
    (x : H) (hx : x ∈ argmin Phi (potential_range_bddBelow hPhi)) :
    ‖uhat - x‖ ≤ ‖u0 + gamma⁻¹ • v0 - x‖ +
      gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ∧
    ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
        (u0 + gamma⁻¹ • v0)‖ ≤
      Metric.infDist (u0 + gamma⁻¹ • v0) (argmin Phi (potential_range_bddBelow hPhi)) +
        gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ∧
    ((∃ L : AffineSubspace ℝ H,
        (argmin Phi (potential_range_bddBelow hPhi) : Set H) = L) →
      ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0)‖ ≤
        gamma⁻¹ * (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))))) ∧
    ((∃ A : H →L[ℝ] H, IsSelfAdjoint A ∧ (∀ x : H, 0 ≤ ⟪A x, x⟫_ℝ) ∧
        (∀ x : H, Phi x = (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)) →
      Tendsto sys.u Filter.atTop
        (nhds (projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0))))
```

## Statement explanation
The declaration is a theorem about a damped second-order dissipative system in a complete real inner product space $H$, i.e. a real Hilbert space. The data are a damping coefficient $\gamma \in \mathbb{R}$, a potential $\Phi : H \to \mathbb{R}$, a gradient field $\operatorname{gradPhi} : H \to H$, initial position $u_0 \in H$, initial velocity $v_0 \in H$, a weak limit $\hat u \in H$, and a minimizer $x \in H$. Let

$$
S=\{q\in H:\Phi(q)=\inf \Phi(H)\}
$$

be the set of global minimizers of $\Phi$, represented in Lean by `argmin Phi (potential_range_bddBelow hPhi)`. The definition of `argmin` says that $q \in S$ exactly when $\Phi(q)=\operatorname{sInf}(\operatorname{range}\Phi)$, i.e. exactly when $\Phi(q)$ is the infimum of the values of $\Phi$.

The hypotheses are:

- `hPhi : HasPotentialAssumption Phi`: a potential-theoretic hypothesis on $\Phi$. The proof uses visible consequences of it: $\Phi$ is convex, its range is bounded below, and $\operatorname{sInf}(\operatorname{range}\Phi)\le \Phi(q)$ for every $q$.
- `sys : DissipativeSystem gamma Phi gradPhi u0 v0`: the dissipative system. It supplies the trajectory $u=\texttt{sys.u}$, the gradient relation between $\operatorname{gradPhi}$ and $\Phi$, and the differential equation. In the proof the equation is used in the form

  $$
  u''(t)+\gamma u'(t)+\operatorname{gradPhi}(u(t))=0.
  $$

- `hgamma : 0 < gamma`: the damping coefficient is positive.
- `hvel0`: the initial velocity has right limit $v_0$, namely

  $$
  u'(t)\to v_0 \quad\text{as } t\to 0^+.
  $$

- `hhat : uhat ∈ S`: the point $\hat u$ is a minimizer of $\Phi$.
- `hWeak`: the trajectory converges weakly to $\hat u$:

  $$
  u(t)\rightharpoonup \hat u \quad\text{as } t\to\infty.
  $$

- `hS_cheb : IsChebyshev S`: the minimizer set is Chebyshev, meaning every point of $H$ has a unique best approximation in $S$.
- `x : H` and `hx : x ∈ S`: an arbitrary minimizer.

The conclusion is a conjunction of four statements. Put

$$
y=u_0+\gamma^{-1}v_0,\qquad
\Delta=\Phi(u_0)-\inf \Phi(H),\qquad
c=\gamma^{-1}\sqrt{2\Delta}.
$$

Also write $P_S(y)$ for the Chebyshev projection point of $y$ onto $S$, i.e. `projectionPoint (argmin Phi …) hS_cheb (u0 + gamma⁻¹ • v0)`. The four conclusions are:

1. $\|\hat u-x\|\le \|y-x\|+c$. Thus the weak limit is controlled in norm by the projected initial “damped” point $y$ and by the energy gap $\Delta$.
2. $\|\hat u-P_S(y)\|\le \operatorname{infDist}(y,S)+c$. This is the same estimate after replacing $x$ by the projection of $y$ onto $S$.
3. If $S$ happens to be an affine subspace of $H$, then the stronger bound

   $$
   \|\hat u-P_S(y)\|\le c
   $$

   holds, with no $\operatorname{infDist}(y,S)$ term.
4. If $\Phi$ is quadratic, i.e. there is a self-adjoint positive semidefinite continuous linear operator $A:H\to H$ such that

   $$
   \Phi(q)=\frac12\langle Aq,q\rangle
   $$

   for all $q$, then the trajectory converges strongly to the projection point:

   $$
   u(t)\to P_S(y)\quad\text{as }t\to\infty.
   $$

## Lean proof
```lean
by
  have hu0 := dissipativeSystem_tendsto_initial_position_right sys
  have hgap : 0 ≤ Phi u0 - sInf (Set.range Phi) :=
    sub_nonneg.mpr (potential_sInf_le hPhi u0)
  have hvelocity_integrable :
      IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    (scalar_damped_minimizing_property hPhi sys).1
  have henergy_from_zero : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      ((1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)) +
          gamma * (∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2) =
        (1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 := by
    intro t ht
    exact scalar_damped_energy_from_zero hPhi sys hvel0 ht
  have hprojection_step :
      (∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
        ‖uhat - z‖ ≤ ‖u0 + gamma⁻¹ • v0 - z‖ +
          gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) →
      ‖uhat - projectionPoint (argmin Phi (potential_range_bddBelow hPhi)) hS_cheb
          (u0 + gamma⁻¹ • v0)‖ ≤
        Metric.infDist (u0 + gamma⁻¹ • v0) (argmin Phi (potential_range_bddBelow hPhi)) +
          gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
    intro hpointwise
    exact projection_metric_estimate_of_pointwise hS_cheb hpointwise
  have hscalar := scalar_damped_minimizing_property hPhi sys
  have hvelocity_zero : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) :=
    hscalar.2.1
  have hdistance_limit : ∃ l : ℝ,
      Tendsto (fun t => ‖sys.u t - x‖) atTop (nhds l) :=
    scalar_distance_to_minimizer_converges hPhi sys hvelocity_integrable x hx
  obtain ⟨distanceLimit, hdistanceLimit⟩ := hdistance_limit
  let p : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2
  have hpderiv_event : ∀ᶠ t in atTop,
      deriv p t = ⟪fderiv ℝ sys.u t 1, sys.u t - x⟫_ℝ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
      (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
    have hs := (hasDerivAt_const t (1 / 2 : ℝ)).mul (hu.sub_const x).norm_sq
    convert hs.deriv using 1 <;> simp [p, real_inner_comm]
  have hpderiv_zero : Tendsto (fun t => deriv p t) atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hdistanceLimit) 1 (by norm_num)
    let M : ℝ := |distanceLimit| + 1
    have hM : ∀ᶠ t in atTop, ‖sys.u t - x‖ ≤ M := by
      filter_upwards [eventually_ge_atTop N] with t ht
      have hdist := hN t ht
      rw [Real.dist_eq] at hdist
      have hlt : ‖sys.u t - x‖ < distanceLimit + 1 := by
        linarith [abs_lt.mp hdist |>.2]
      dsimp [M]
      linarith [le_abs_self distanceLimit]
    have hprod : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖ * M) atTop (nhds 0) := by
      simpa using hvelocity_zero.norm.mul_const M
    have habs : Tendsto (fun t => |deriv p t|) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (g := fun _ : ℝ => 0) (f := fun t => |deriv p t|)
        (h := fun t => ‖fderiv ℝ sys.u t 1‖ * M)
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) hprod ?_ ?_
      · filter_upwards [hpderiv_event] with t ht
        rw [ht]
        positivity
      · filter_upwards [hpderiv_event, hM] with t ht hMt
        rw [ht]
        exact (abs_real_inner_le_norm _ _).trans (by
          gcongr)
    have habs' : Tendsto (fun t => |deriv p t|) atTop (nhds 0) := habs
    have habs_norm : Tendsto (fun t => ‖deriv p t‖) atTop (nhds 0) := by
      simpa only [Real.norm_eq_abs] using habs'
    exact tendsto_zero_iff_norm_tendsto_zero.mpr habs_norm
  have hdist_integrated := scalar_damped_distance_integrated_bound hPhi sys hgamma hvel0 hx
    hvelocity_integrable
  have hq_bound : ∀ ⦃t : ℝ⦄, 0 ≤ t →
      ∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2 ≤
        gamma⁻¹ * ((1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi)) := by
    intro t ht
    have henergy := henergy_from_zero ht
    have hpot := potential_sInf_le hPhi (sys.u t)
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by positivity
    have hqnonneg : 0 ≤ ∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2 := by
      apply intervalIntegral.integral_nonneg ht
      intro s hs
      positivity
    have hgamma' : 0 < gamma := hgamma
    have hmul : (∫ s in 0..t, ‖fderiv ℝ sys.u s 1‖ ^ 2) * gamma ≤
        (1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi) := by
      linarith
    have hdiv := (le_div_iff₀ hgamma').2 hmul
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hpointwise : ∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
      ‖uhat - z‖ ≤ ‖u0 + gamma⁻¹ • v0 - z‖ +
        gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
    intro z hz
    have hdist_integrated_z := scalar_damped_distance_integrated_bound hPhi sys hgamma hvel0 hz
      hvelocity_integrable
    obtain ⟨lz, hlz⟩ := scalar_distance_to_minimizer_converges hPhi sys hvelocity_integrable z hz
    let pz : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u t - z‖ ^ 2
    have hpz_event : ∀ᶠ t in atTop,
        deriv pz t = ⟪fderiv ℝ sys.u t 1, sys.u t - z⟫_ℝ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
        (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
      convert ((hasDerivAt_const t (1 / 2 : ℝ)).mul (hu.sub_const z).norm_sq).deriv
        using 1 <;> simp [pz, real_inner_comm]
    have hpz_zero : Tendsto (fun t => deriv pz t) atTop (nhds 0) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlz) 1 (by norm_num)
      let M : ℝ := |lz| + 1
      have hM : ∀ᶠ t in atTop, ‖sys.u t - z‖ ≤ M := by
        filter_upwards [eventually_ge_atTop N] with t ht
        have hdist := hN t ht
        rw [Real.dist_eq] at hdist
        have hlt : ‖sys.u t - z‖ < lz + 1 := by
          linarith [abs_lt.mp hdist |>.2]
        dsimp [M]
        linarith [le_abs_self lz]
      have hprod : Tendsto (fun t => ‖fderiv ℝ sys.u t 1‖ * M) atTop (nhds 0) := by
        simpa using hvelocity_zero.norm.mul_const M
      have habs : Tendsto (fun t => |deriv pz t|) atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (g := fun _ : ℝ => 0) (f := fun t => |deriv pz t|)
          (h := fun t => ‖fderiv ℝ sys.u t 1‖ * M)
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) hprod ?_ ?_
        · filter_upwards [hpz_event] with t ht
          rw [ht]
          positivity
        · filter_upwards [hpz_event, hM] with t ht hMt
          rw [ht]
          exact (abs_real_inner_le_norm _ _).trans (by gcongr)
      have habs_norm : Tendsto (fun t => ‖deriv pz t‖) atTop (nhds 0) := by
        simpa only [Real.norm_eq_abs] using habs
      exact tendsto_zero_iff_norm_tendsto_zero.mpr habs_norm
    let K : ℝ := (1 / 2 : ℝ) * ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 +
      (gamma⁻¹) ^ 2 * (Phi u0 - sInf (Set.range Phi))
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hnorm_eps : ∀ ⦃ε : ℝ⦄, 0 < ε →
        ‖uhat - z‖ ≤ Real.sqrt (2 * (K + ε)) := by
      intro ε hε
      have hevent : ∀ᶠ t in atTop, pz t ≤ K + ε := by
        have hpze := hpz_zero.eventually (Metric.ball_mem_nhds 0 (by
          exact mul_pos hgamma hε))
        filter_upwards [eventually_gt_atTop (0 : ℝ), hpze] with t ht htp
        have hi := hdist_integrated_z ht
        have hq := hq_bound (le_of_lt ht)
        have hsmall : -deriv pz t ≤ gamma * ε := by
          have habs_le : |deriv pz t| < gamma * ε := by
            simpa [Metric.mem_ball, Real.dist_eq] using htp
          exact le_trans (neg_le_abs _) (le_of_lt habs_le)
        dsimp [pz, K] at *
        have hgam : 0 < gamma := hgamma
        have hginv : gamma * gamma⁻¹ = 1 := by
          field_simp
        have hy_sq : ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 =
            ‖u0 - z‖ ^ 2 + 2 * gamma⁻¹ * ⟪v0, u0 - z⟫_ℝ +
              gamma⁻¹ ^ 2 * ‖v0‖ ^ 2 := by
          have hrew : u0 + gamma⁻¹ • v0 - z =
              (u0 - z) + gamma⁻¹ • v0 := by abel
          rw [hrew, norm_add_sq_real, real_inner_smul_right, norm_smul]
          simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hgamma)]
          rw [real_inner_comm]
          ring
        have hrewrite :
            ⟪v0, u0 - z⟫_ℝ + gamma * ((1 / 2 : ℝ) * ‖u0 - z‖ ^ 2) +
                gamma⁻¹ * ((1 / 2 : ℝ) * ‖v0‖ ^ 2 + Phi u0 - sInf (Set.range Phi)) +
                gamma * ε =
              gamma * ((1 / 2 : ℝ) * ‖u0 + gamma⁻¹ • v0 - z‖ ^ 2 +
                gamma⁻¹ ^ 2 * (Phi u0 - sInf (Set.range Phi)) + ε) := by
          rw [hy_sq]
          have hgn : gamma ≠ 0 := ne_of_gt hgamma
          field_simp [hgn]
          ring
        nlinarith [hi, hq, hsmall, hrewrite]
      have hnorm_event : ∀ᶠ t in atTop, ‖sys.u t - z‖ ≤ Real.sqrt (2 * (K + ε)) := by
        filter_upwards [hevent] with t ht
        dsimp [pz] at ht
        have hnonneg : 0 ≤ ‖sys.u t - z‖ := norm_nonneg _
        have hsqrt : 0 ≤ Real.sqrt (2 * (K + ε)) := Real.sqrt_nonneg _
        have harg : 0 ≤ 2 * (K + ε) := by
          nlinarith [hKnonneg, hε]
        apply (Real.le_sqrt hnonneg harg).2
        have hsqrt_sq : (Real.sqrt (2 * (K + ε))) ^ 2 = 2 * (K + ε) :=
          Real.sq_sqrt harg
        nlinarith [ht, hsqrt_sq]
      exact weak_norm_sub_le_of_tendsto hWeak hnorm_event
    have hsqrt_lim : Tendsto (fun ε : ℝ => Real.sqrt (2 * (K + ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt (2 * K))) := by
      have harglim : Tendsto (fun ε : ℝ => 2 * (K + ε))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * K)) := by
        have hKlim : Tendsto (fun _ : ℝ => K)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds K) := tendsto_const_nhds
        have hidlim : Tendsto (fun ε : ℝ => ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        simpa [add_comm, add_left_comm, add_assoc] using (hKlim.add hidlim).const_mul 2
      exact Real.continuous_sqrt.continuousAt.tendsto.comp harglim
    have hsqK : Real.sqrt (2 * K) ≤
        ‖u0 + gamma⁻¹ • v0 - z‖ + gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · dsimp [K]
        have hgap' : 0 ≤ Phi u0 - sInf (Set.range Phi) := hgap
        have hsqrt : 0 ≤ Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi))) := Real.sqrt_nonneg _
        have hsqroot : (Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))) ^ 2 =
            2 * (Phi u0 - sInf (Set.range Phi)) := by
          exact Real.sq_sqrt (by positivity)
        have hgamma0 : 0 ≤ gamma⁻¹ := le_of_lt (inv_pos.mpr hgamma)
        nlinarith [sq_nonneg ‖u0 + gamma⁻¹ • v0 - z‖,
          mul_nonneg (norm_nonneg (u0 + gamma⁻¹ • v0 - z)) (mul_nonneg hgamma0 hsqrt)]
    have hsq_lim := ge_of_tendsto hsqrt_lim (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hnorm_eps hε)
    exact le_trans hsq_lim hsqK
  have hfirst := hpointwise x hx
  refine ⟨hfirst, hprojection_step hpointwise, ?_⟩
  constructor
  · intro hAffine
    rcases hAffine with ⟨L, hL⟩
    let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
    let y : H := u0 + gamma⁻¹ • v0
    let p : H := projectionPoint S hS_cheb y
    let e : H := uhat - p
    let d : ℝ := Metric.infDist y S
    let c : ℝ := gamma⁻¹ * Real.sqrt (2 * (Phi u0 - sInf (Set.range Phi)))
    have hSclosed : IsClosed S := isClosed_of_isChebyshev hS_cheb
    have hLclosed : IsClosed (L : Set H) := by
      rw [← hL]
      exact hSclosed
    have hpS : p ∈ S := by
      exact projectionPoint_mem S hS_cheb y
    have hpL : p ∈ (L : Set H) := by
      rw [← hL]
      exact hpS
    have huL : uhat ∈ (L : Set H) := by
      rw [← hL]
      exact hhat
    have hLnonempty : (L : Set H).Nonempty := ⟨p, hpL⟩
    let hchebL : IsChebyshev (L : Set H) :=
      isChebyshev_of_nonempty_isClosed_convex hLnonempty hLclosed L.convex
    have hp_eq : p = projectionPoint (L : Set H) hchebL y := by
      simpa [p, S, hL] using
        (show projectionPoint S hS_cheb y = projectionPoint S hS_cheb y from rfl)
    have hchar :=
      (eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
        hLnonempty hLclosed (x := y) (p := p)).mp hp_eq
    have horth : ⟪e, y - p⟫_ℝ = 0 := by
      dsimp [e]
      simpa [e] using hchar.2 uhat huL p hpL
    have hbest : ‖y - p‖ = d := by
      have hb := (projectionPoint_isBestApproximation S hS_cheb y).2
      simpa [d, dist_eq_norm] using hb
    have hd : 0 ≤ d := by
      dsimp [d]
      exact Metric.infDist_nonneg
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    by_cases he_zero : e = 0
    · have hebound : ‖e‖ ≤ c := by rw [he_zero]; simp; exact hc
      simpa [e, p, S, y, c] using hebound
    · have he_ne : e ≠ 0 := he_zero
      have he_norm : 0 < ‖e‖ := norm_pos_iff.mpr he_ne
      have he_dir : e ∈ L.direction := by
        dsimp [e]
        simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction huL hpL
      have hunit_norm : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he_norm)]
        field_simp
      have hunit_vec : ‖e‖ • (‖e‖⁻¹ • e) = e := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt he_norm), one_smul]
      have hxr : ∀ r : ℝ, p - (r * d) • (‖e‖⁻¹ • e) ∈ S := by
        intro r
        have hscaled : -(r * d) • (‖e‖⁻¹ • e) ∈ L.direction := by
          apply L.direction.smul_mem
          apply L.direction.smul_mem
          exact he_dir
        have hvadd := AffineSubspace.vadd_mem_of_mem_direction hscaled hpL
        dsimp [S]
        rw [hL]
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hvadd
      have hnorm_y : ∀ r : ℝ, ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ =
          Real.sqrt (1 + r ^ 2) * d := by
        intro r
        have hcross : ⟪y - p, (r * d) • (‖e‖⁻¹ • e)⟫_ℝ = 0 := by
          rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
          rw [horth]
          ring
        have hsq : ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ ^ 2 =
            d ^ 2 + (r * d) ^ 2 := by
          have hrewrite : y - (p - (r * d) • (‖e‖⁻¹ • e)) =
              (y - p) + (r * d) • (‖e‖⁻¹ • e) := by abel
          rw [hrewrite, norm_add_sq_real, hcross, norm_smul, hunit_norm]
          rw [hbest]
          simp only [mul_one]
          have hnorm_sq : ‖r * d‖ ^ 2 = (r * d) ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
          rw [hnorm_sq]
          ring
        have hsqrt : 0 ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_nonneg _
        have harg : 0 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
        have hsqrt_sq := Real.sq_sqrt harg
        have hright : 0 ≤ Real.sqrt (1 + r ^ 2) * d := mul_nonneg hsqrt hd
        have hleft : 0 ≤ ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ := norm_nonneg _
        nlinarith
      have hnorm_e : ∀ r : ℝ, 0 ≤ r →
          ‖uhat - (p - (r * d) • (‖e‖⁻¹ • e))‖ = ‖e‖ + r * d := by
        intro r hr
        have hrewrite : uhat - (p - (r * d) • (‖e‖⁻¹ • e)) =
            (‖e‖ + r * d) • (‖e‖⁻¹ • e) := by
          rw [add_smul, hunit_vec]
          dsimp [e]
          abel
        rw [hrewrite, norm_smul, hunit_norm]
        have : 0 ≤ ‖e‖ + r * d := by
          positivity
        rw [Real.norm_eq_abs, abs_of_nonneg this]
        ring
      have hray : ∀ r : ℝ, 0 ≤ r →
          ‖e‖ ≤ (Real.sqrt (1 + r ^ 2) - r) * d + c := by
        intro r hr
        have hp' := hpointwise (p - (r * d) • (‖e‖⁻¹ • e))
          (by simpa [S] using hxr r)
        have hp'' : ‖uhat - (p - (r * d) • (‖e‖⁻¹ • e))‖ ≤
            ‖y - (p - (r * d) • (‖e‖⁻¹ • e))‖ + c := by
          simpa [y, c] using hp'
        rw [hnorm_e r hr, hnorm_y r] at hp''
        linarith
      have hden_tendsto : Tendsto (fun n : ℕ =>
          Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) atTop atTop := by
        apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
        nlinarith [Real.sqrt_nonneg (1 + (n : ℝ) ^ 2)]
      have hfactor : Tendsto (fun n : ℕ =>
          Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) atTop (nhds 0) := by
        have hinv := tendsto_inv_atTop_zero.comp hden_tendsto
        apply hinv.congr'
        filter_upwards with n
        have hsq := Real.sq_sqrt (show 0 ≤ 1 + (n : ℝ) ^ 2 by positivity)
        have hden : Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ) ≠ 0 := by
          nlinarith [Real.sqrt_nonneg (1 + (n : ℝ) ^ 2)]
        have hidentity :
            (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))⁻¹ =
              Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) := by
          calc
            (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ))⁻¹ =
                1 / (Real.sqrt (1 + (n : ℝ) ^ 2) + (n : ℝ)) := by rw [one_div]
            _ = Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ) := by
              apply (div_eq_iff hden).2
              nlinarith
        simpa only [Function.comp_apply] using hidentity
      have hterm : Tendsto (fun n : ℕ =>
          (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d) atTop (nhds 0) := by
        simpa only [zero_mul] using hfactor.mul_const d
      have hlim : Tendsto (fun n : ℕ =>
          (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d + c) atTop (nhds c) := by
        simpa using hterm.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
      have hev : ∀ᶠ n : ℕ in atTop,
          ‖e‖ ≤ (Real.sqrt (1 + (n : ℝ) ^ 2) - (n : ℝ)) * d + c := by
        filter_upwards [Filter.Eventually.of_forall (fun n => hray n (by positivity))] with n hn
        simpa using hn
      have hebound : ‖e‖ ≤ c := ge_of_tendsto hlim hev
      simpa [e, p, S, y, c] using hebound
  · intro hQuadratic
    rcases hQuadratic with ⟨A, hAself, hApos, hPhiA⟩
    have hquad := quadratic_scalar_damped_tendsto_weak_limit hPhi sys hhat hWeak A hPhiA
    have hgradA : ∀ q : H, gradPhi q = A q := by
      intro q
      have hqstrict := hAself.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf q
      have hqscaled := hqstrict.const_mul (1 / 2 : ℝ)
      have hqderiv : HasFDerivAt (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
          (innerSL ℝ (A q)) q := by
        have hs : HasStrictFDerivAt (fun x : H =>
            (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
            ((1 / 2 : ℝ) • (2 • (innerSL ℝ) (A q))) q := by
          simpa [ContinuousLinearMap.reApplyInnerSelf] using hqscaled
        convert hs.hasFDerivAt using 1
        ext v
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        norm_num
        ring
      have hg : HasFDerivAt (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ)
          (InnerProductSpace.toDual ℝ H (gradPhi q)) q := by
        have hfun : Phi = (fun x : H => (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ) :=
          funext hPhiA
        rw [← hfun]
        exact (sys.is_gradient q).hasFDerivAt
      have hdual := hg.unique hqderiv
      apply (InnerProductSpace.toDual ℝ H).injective
      ext y
      simpa [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
        congrArg (fun f => f y) hdual
    have hAzero : ∀ z : H, z ∈ argmin Phi (potential_range_bddBelow hPhi) → A z = 0 := by
      intro z hz
      have hmin : IsMinOn Phi Set.univ z := by
        intro y hy
        rw [show Phi z = sInf (Set.range Phi) from hz]
        exact potential_sInf_le hPhi y
      have hfderiv : fderiv ℝ Phi z = 0 :=
        (hmin.isLocalMin (by simp : Set.univ ∈ nhds z)).fderiv_eq_zero
      have hgradzero : gradPhi z = 0 := by
        have hinner : ⟪gradPhi z, gradPhi z⟫_ℝ = 0 := by
          rw [← (sys.is_gradient z).fderiv_apply, hfderiv]
          simp
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp
          (by simpa only [real_inner_self_eq_norm_sq] using hinner))
      rw [← hgradA z]
      exact hgradzero
    let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
    let y : H := u0 + gamma⁻¹ • v0
    have hSclosed : IsClosed S := isClosed_of_isChebyshev hS_cheb
    have hSconv : Convex ℝ S := by
      intro a ha b hb α β hα hβ hab
      change Phi (α • a + β • b) = sInf (Set.range Phi)
      change Phi a = sInf (Set.range Phi) at ha
      change Phi b = sInf (Set.range Phi) at hb
      have hle := hPhi.convex.2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hab
      rw [ha, hb] at hle
      apply le_antisymm
      · calc
          Phi (α • a + β • b) ≤ α * sInf (Set.range Phi) + β * sInf (Set.range Phi) := hle
          _ = sInf (Set.range Phi) := by rw [← add_mul, hab, one_mul]
      · exact potential_sInf_le hPhi _
    have horth_proj : ∀ z : H, z ∈ S →
        ⟪uhat - y, z⟫_ℝ = 0 := by
      intro z hz
      let hgfun : ℝ → ℝ := fun t =>
        ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ + gamma * ⟪sys.u t - u0, z⟫_ℝ
      have hg_deriv : ∀ ⦃t : ℝ⦄, 0 < t →
          HasDerivAt hgfun
            (⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, z⟫_ℝ +
              gamma * ⟪fderiv ℝ sys.u t 1, z⟫_ℝ) t := by
        intro t ht
        have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
          (dissipativeSystem_differentiableAt_pos sys ht).hasDerivAt
        have hv : HasDerivAt (fun s => fderiv ℝ sys.u s 1)
            (fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1) t :=
          dissipativeSystem_velocity_hasDerivAt_pos sys ht
        have h1 := (hv.sub_const v0).inner ℝ (hasDerivAt_const t z)
        have h2 := (hu.sub_const u0).inner ℝ (hasDerivAt_const t z)
        have hsum := h1.add ((hasDerivAt_const t gamma).mul h2)
        simpa [hgfun] using hsum
      have hg_zero_deriv : ∀ ⦃t : ℝ⦄, 0 < t → deriv hgfun t = 0 := by
        intro t ht
        have heq := sys.equation t (le_of_lt ht)
        have hinner := congrArg (fun w : H => ⟪w, z⟫_ℝ) heq
        have hAz := hAzero z hz
        have horth : ⟪gradPhi (sys.u t), z⟫_ℝ = 0 := by
          calc
            ⟪gradPhi (sys.u t), z⟫_ℝ = ⟪A (sys.u t), z⟫_ℝ := by rw [hgradA]
            _ = ⟪sys.u t, A z⟫_ℝ := hAself.isSymmetric _ _
            _ = 0 := by rw [hAz]; simp
        rw [(hg_deriv ht).deriv]
        have hinner' :
            ⟪fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1, z⟫_ℝ +
              gamma * ⟪fderiv ℝ sys.u t 1, z⟫_ℝ +
              ⟪gradPhi (sys.u t), z⟫_ℝ = 0 := by
          simpa [inner_add_left, inner_smul_left] using hinner
        linarith
      have hg_diff : DifferentiableOn ℝ hgfun (Set.Ioi 0) := by
        intro t ht
        exact (hg_deriv ht).differentiableAt.differentiableWithinAt
      have hg_fderiv_zero : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioi 0 →
          fderivWithin ℝ hgfun (Set.Ioi 0) t = 0 := by
        intro t ht
        rw [fderivWithin_of_isOpen isOpen_Ioi ht]
        rw [← toSpanSingleton_deriv]
        simp [hg_zero_deriv ht]
      have hg_const : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioi 0 → b ∈ Set.Ioi 0 →
          hgfun a = hgfun b := by
        intro a b ha hb
        exact (convex_Ioi (0 : ℝ)).is_const_of_fderivWithin_eq_zero
          hg_diff hg_fderiv_zero ha hb
      have hg_right : Tendsto hgfun (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hvlim : Tendsto (fun t => fderiv ℝ sys.u t 1 - v0)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : H)) := by
          simpa using hvel0.sub (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => v0) (nhdsWithin 0 (Set.Ioi 0)) (nhds v0))
        have hulim : Tendsto (fun t => sys.u t - u0)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : H)) := by
          simpa using hu0.sub (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => u0) (nhdsWithin 0 (Set.Ioi 0)) (nhds u0))
        have h1 : Tendsto (fun t : ℝ =>
            ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          simpa using Filter.Tendsto.inner (𝕜 := ℝ) hvlim (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds z))
        have h2 : Tendsto (fun t : ℝ =>
            ⟪sys.u t - u0, z⟫_ℝ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          simpa using Filter.Tendsto.inner (𝕜 := ℝ) hulim (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) (nhdsWithin 0 (Set.Ioi 0)) (nhds z))
        have hsum := h1.add ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => gamma) (nhdsWithin 0 (Set.Ioi 0)) (nhds gamma)).mul h2)
        simpa [hgfun] using hsum
      have hg_zero : ∀ t : ℝ, 0 < t → hgfun t = 0 := by
        intro t ht
        have hev : ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0), hgfun a = hgfun t := by
          filter_upwards [self_mem_nhdsWithin] with a ha
          exact hg_const ha ht
        have hlim : Tendsto (fun _ : ℝ => hgfun t)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hg_right.congr' hev
        exact tendsto_nhds_unique tendsto_const_nhds hlim
      have hconst : Tendsto hgfun atTop (nhds 0) := by
        apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)).congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        exact (hg_zero t ht).symm
      have hvweak := hvel0
      have hv_atTop : Tendsto (fun t => fderiv ℝ sys.u t 1 - v0)
          atTop (nhds (-v0)) := by
        simpa using hvelocity_zero.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => v0) atTop (nhds v0))
      have huweak : Tendsto (fun t => ⟪sys.u t - u0, z⟫_ℝ)
          atTop (nhds ⟪uhat - u0, z⟫_ℝ) := by
        have hw := (weakSpace_continuous_inner_right z).tendsto
          (toWeakSpace ℝ H uhat) |>.comp hWeak
        simpa [inner_sub_right, real_inner_comm] using hw.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => ⟪u0, z⟫_ℝ) atTop (nhds ⟪u0, z⟫_ℝ))
      have hvinner : Tendsto
          (fun t : ℝ => ⟪fderiv ℝ sys.u t 1 - v0, z⟫_ℝ)
          atTop (nhds ⟪-v0, z⟫_ℝ) := by
        exact Filter.Tendsto.inner (𝕜 := ℝ) hv_atTop
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => z) atTop (nhds z))
      have hglim := hvinner.add ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => gamma) atTop (nhds gamma)).mul huweak)
      have hglim' : Tendsto hgfun atTop
          (nhds (⟪-v0, z⟫_ℝ + gamma * ⟪uhat - u0, z⟫_ℝ)) := by
        simpa [hgfun] using hglim
      have hzero_eq := tendsto_nhds_unique hconst hglim'
      rw [sub_eq_add_neg, inner_add_left, real_inner_comm] at hzero_eq
      rw [inner_neg_right, inner_neg_left] at hzero_eq
      have hzero_eq' : gamma * (⟪uhat, z⟫_ℝ - ⟪u0, z⟫_ℝ) = ⟪v0, z⟫_ℝ := by
        have hzero_eq'' : 0 = -⟪v0, z⟫_ℝ +
            gamma * (⟪uhat, z⟫_ℝ - ⟪u0, z⟫_ℝ) := by
          simpa [real_inner_comm] using hzero_eq
        linarith [hzero_eq'']
      dsimp [y]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      field_simp [hgamma.ne']
      nlinarith [hzero_eq']
    have hproj : uhat = projectionPoint S hS_cheb y := by
      apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hS_cheb hSconv).mpr
      refine ⟨hhat, ?_⟩
      intro z hz
      have hzorth := horth_proj z hz
      have huorth := horth_proj uhat hhat
      have hz' : ⟪z, y⟫_ℝ - ⟪z, uhat⟫_ℝ = 0 := by
        have hz'' : ⟪uhat, z⟫_ℝ - ⟪z, y⟫_ℝ = 0 := by
          simpa [inner_sub_left, real_inner_comm] using hzorth
        have hcomm : ⟪uhat, z⟫_ℝ = ⟪z, uhat⟫_ℝ := real_inner_comm _ _
        linarith
      have hu' : ⟪uhat, y⟫_ℝ - ⟪uhat, uhat⟫_ℝ = 0 := by
        have hu'' : ‖uhat‖ ^ 2 - ⟪uhat, y⟫_ℝ = 0 := by
          simpa [inner_sub_left, real_inner_comm] using huorth
        nlinarith [real_inner_self_eq_norm_sq uhat]
      have hzero : ⟪z - uhat, y - uhat⟫_ℝ = 0 := by
        simp only [inner_sub_left, inner_sub_right]
        nlinarith [hz', hu']
      exact hzero.le
    simpa [hproj, S, y] using hquad
```

## Proof explanation
The proof begins by recording the right-hand initial-position limit. The cited theorem `dissipativeSystem_tendsto_initial_position_right sys` states that for the dissipative system,

$$
u(t)\to u_0 \quad\text{as }t\to 0^+.
$$

This is later used to compute the right limit of an auxiliary scalar function.

Next, `potential_sInf_le hPhi u0` gives

$$
\inf\Phi(H)\le \Phi(u_0),
$$

so

$$
\Delta=\Phi(u_0)-\inf\Phi(H)\ge 0.
$$

This nonnegativity is needed whenever the proof takes square roots such as $\sqrt{2\Delta}$.

The cited theorem `scalar_damped_minimizing_property hPhi sys` gives a conjunction of four facts: the squared velocity is integrable on $[0,\infty)$, the velocity tends to $0$ at infinity, the potential values tend to the infimum of the range of $\Phi$, and, if the minimizer set is nonempty, there is weak convergence to some minimizer. The proof uses its first component to obtain

$$
\int_0^\infty \|u'(t)\|^2\,dt<\infty,
$$

and its second component to obtain

$$
u'(t)\to 0\quad\text{as }t\to\infty.
$$

The weak convergence hypothesis `hWeak` is supplied separately.

The cited lemma `scalar_damped_energy_from_zero hPhi sys hvel0 ht` gives, for every $t\ge 0$,

$$
\left(\frac12\|u'(t)\|^2+\Phi(u(t))\right)
+\gamma\int_0^t \|u'(s)\|^2\,ds
=
\frac12\|v_0\|^2+\Phi(u_0).
$$

Using $\Phi(u(t))\ge \inf\Phi(H)$ and the kinetic term $\frac12\|u'(t)\|^2\ge 0$, this implies the bound

$$
\int_0^t \|u'(s)\|^2\,ds
\le
\gamma^{-1}\left(\frac12\|v_0\|^2+\Phi(u_0)-\inf\Phi(H)\right)
$$

for every $t\ge 0$. This is the integral estimate `hq_bound` used later to control the accumulated dissipation.

The next major step is the pointwise estimate. For a minimizer $z\in S$, the cited theorem `scalar_distance_to_minimizer_converges hPhi sys hvelocity_integrable z hz` gives that the scalar distance function

$$
t\mapsto \|u(t)-z\|
$$

has a finite limit as $t\to\infty$. For the fixed minimizer $x$, this produces a limit `distanceLimit` with

$$
\|u(t)-x\|\to \texttt{distanceLimit}.
$$

The proof defines

$$
p(t)=\frac12\|u(t)-x\|^2.
$$

Using `dissipativeSystem_differentiableAt_pos sys ht`, which says that $u$ is differentiable at every positive time $t$, the proof obtains

$$
p'(t)=\langle u'(t),u(t)-x\rangle
$$

eventually for large positive $t$. Since $u'(t)\to 0$ and $\|u(t)-x\|$ is eventually bounded by some constant $M$, Cauchy–Schwarz gives

$$
|p'(t)|\le \|u'(t)\|\,\|u(t)-x\|\le M\|u'(t)\|.
$$

Therefore $p'(t)\to 0$. This is an important auxiliary fact: the derivative of the half-squared distance to a minimizer vanishes at infinity.

A similar argument is repeated for an arbitrary minimizer $z\in S$. The cited theorem `scalar_damped_distance_integrated_bound hPhi sys hgamma hvel0 hz hvelocity_integrable` gives, for every $t>0$,

$$
\frac{d}{dt}\left(\frac12\|u(t)-z\|^2\right)
+\gamma\left(\frac12\|u(t)-z\|^2\right)
\le
\langle v_0,u_0-z\rangle
+\gamma\left(\frac12\|u_0-z\|^2\right)
+\int_0^t \|u'(s)\|^2\,ds.
$$

Let

$$
p_z(t)=\frac12\|u(t)-z\|^2.
$$

The proof proves $p_z'(t)\to 0$ by the same bounded-distance and vanishing-velocity argument as for $p$. Combining the differential inequality with the integral bound `hq_bound`, and using that $p_z'\to 0$, it shows that for every $\varepsilon>0$, eventually

$$
p_z(t)\le K+\varepsilon,
$$

where

$$
K=\frac12\|u_0+\gamma^{-1}v_0-z\|^2+\gamma^{-2}\Delta.
$$

The algebra here uses the expansion of

$$
\|u_0+\gamma^{-1}v_0-z\|^2
$$

and the identity

$$
\frac{1}{\gamma}\left(\langle v_0,u_0-z\rangle+\gamma\frac12\|u_0-z\|^2
+\int_0^t\|u'\|^2\right)
$$

to rewrite the differential inequality in the form involving $K+\varepsilon$. The tactics `rw`, `field_simp`, `ring`, and `nlinarith` are used to perform these scalar rearrangements.

From $p_z(t)\le K+\varepsilon$ eventually, the proof obtains

$$
\|u(t)-z\|\le \sqrt{2(K+\varepsilon)}
$$

eventually. The cited lemma `weak_norm_sub_le_of_tendsto hWeak hnorm_event` then applies: if $u(t)$ converges weakly to $\hat u$ and eventually $\|u(t)-z\|\le B$, then

$$
\|\hat u-z\|\le B.
$$

Thus

$$
\|\hat u-z\|\le \sqrt{2(K+\varepsilon)}
$$

for every $\varepsilon>0$. Letting $\varepsilon\to 0^+$ along the positive reals, using continuity of the square root, gives

$$
\|\hat u-z\|\le \sqrt{2K}.
$$

Finally,

$$
\sqrt{2K}
\le
\|u_0+\gamma^{-1}v_0-z\|
+\gamma^{-1}\sqrt{2\Delta}
$$

by the elementary inequality

$$
\sqrt{a^2+2b^2}\le a+b
$$

or, equivalently, by subadditivity of the square root applied to the two nonnegative summands. This proves the pointwise bound

$$
\|\hat u-z\|
\le
\|u_0+\gamma^{-1}v_0-z\|
+\gamma^{-1}\sqrt{2\Delta}
$$

for every $z\in S$. Taking $z=x$ gives the first conclusion.

For the second conclusion, the cited theorem `projection_metric_estimate_of_pointwise hS_cheb hpointwise` is applied. It says that if $S$ is Chebyshev and

$$
\|\hat u-z\|\le \|y-z\|+d
$$

for every $z\in S$, then

$$
\|\hat u-P_S(y)\|\le \operatorname{infDist}(y,S)+d.
$$

Here $y=u_0+\gamma^{-1}v_0$ and $d=\gamma^{-1}\sqrt{2\Delta}$. This is exactly the second conjunct.

The third conclusion treats the case where $S$ is an affine subspace $L$. The proof uses `isClosed_of_isChebyshev hS_cheb` to see that $S$ is closed. Since $S=L$, the affine subspace $L$ is closed. It also has a point, because $p=P_S(y)\in S=L$. The cited theorem `isChebyshev_of_nonempty_isClosed_convex` then shows that any nonempty closed convex subset of a Hilbert space is Chebyshev, so $L$ is Chebyshev as well.

Let

$$
p=P_S(y),\qquad e=\hat u-p,\qquad d=\operatorname{infDist}(y,S).
$$

The cited theorem `projectionPoint_isBestApproximation` gives that $p$ is a best approximation to $y$ in $S$, so

$$
\|y-p\|=d.
$$

The cited characterization of projections onto closed affine subspaces,
`eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace`,
says that $p$ is the projection of $y$ onto $L$ exactly when $p\in L$ and

$$
\langle w-z,y-p\rangle=0
$$

for all $w,z\in L$. Applying this with $w=\hat u$ and $z=p$, and using $\hat u,p\in L$, gives

$$
\langle e,y-p\rangle=0.
$$

Thus $e$ is orthogonal to $y-p$.

The difference of two points of an affine subspace lies in its direction, so `AffineSubspace.vsub_mem_direction` gives

$$
e\in L.\mathrm{direction}.
$$

If $e=0$, then $\|e\|\le c$ is immediate because $c\ge 0$. Otherwise, the proof uses the unit vector $e/\|e\|$ and moves from $p$ in the direction $-e$ by distance $rd$. For each $r\ge 0$, the point

$$
q_r=p-(rd)\frac{e}{\|e\|}
$$

lies in $S=L$. Orthogonality of $e$ and $y-p$ gives

$$
\|y-q_r\|=\sqrt{1+r^2}\,d,
$$

while

$$
\|\hat u-q_r\|=\|e\|+rd.
$$

The already proved pointwise estimate applied to $q_r\in S$ yields

$$
\|e\|\le (\sqrt{1+r^2}-r)d+c.
$$

Taking $r=n\in\mathbb N$ and letting $n\to\infty$, the identity

$$
\sqrt{1+n^2}-n=\frac{1}{\sqrt{1+n^2}+n}\to 0
$$

gives

$$
\|e\|\le c.
$$

This is precisely the affine-subspace conclusion.

The fourth conclusion assumes that $\Phi$ is quadratic:

$$
\Phi(q)=\frac12\langle Aq,q\rangle
$$

for a self-adjoint positive semidefinite continuous linear operator $A$. The proof first identifies the gradient. The cited Mathlib lemma accessed as `hAself.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf q` says that the derivative of $q\mapsto \langle Aq,q\rangle$ at $q$ is $2\langle Aq,\cdot\rangle$; after multiplying by $1/2$, the derivative of $\Phi$ is the continuous linear functional $v\mapsto \langle Aq,v\rangle$. The gradient relation `sys.is_gradient q` says that the Fréchet derivative of $\Phi$ at $q$ is represented by $\operatorname{gradPhi}(q)$ under the Riesz isomorphism. By uniqueness of the derivative, the proof obtains

$$
\operatorname{gradPhi}(q)=Aq
$$

for every $q\in H$.

Next, for every minimizer $z\in S$, the proof shows

$$
Az=0.
$$

Indeed, since $z$ minimizes $\Phi$, its derivative is zero at $z$. Using `sys.is_gradient z`, this means $\operatorname{gradPhi}(z)=0$. Since $\operatorname{gradPhi}(z)=Az$, we get $Az=0$.

The proof also shows that $S$ is convex. If $a,b\in S$, $\alpha,\beta\ge 0$, and $\alpha+\beta=1$, then convexity of $\Phi$, coming from `hPhi.convex`, gives

$$
\Phi(\alpha a+\beta b)\le \alpha\Phi(a)+\beta\Phi(b)=\inf\Phi(H).
$$

The reverse inequality $\inf\Phi(H)\le \Phi(\alpha a+\beta b)$ is `potential_sInf_le hPhi`. Hence equality holds, so $\alpha a+\beta b\in S$.

The key remaining point is to prove

$$
\langle \hat u-y,z\rangle=0
$$

for every $z\in S$. The proof defines

$$
g_z(t)=\langle u'(t)-v_0,z\rangle+\gamma\langle u(t)-u_0,z\rangle.
$$

Using `dissipativeSystem_differentiableAt_pos` and `dissipativeSystem_velocity_hasDerivAt_pos`, it shows for $t>0$

$$
g_z'(t)=\langle u''(t),z\rangle+\gamma\langle u'(t),z\rangle.
$$

The system equation gives

$$
u''(t)+\gamma u'(t)+\operatorname{gradPhi}(u(t))=0.
$$

Taking inner product with $z$ and using $Az=0$ together with self-adjointness gives

$$
\langle \operatorname{gradPhi}(u(t)),z\rangle
=
\langle A u(t),z\rangle
=
\langle u(t),Az\rangle
=0.
$$

Therefore $g_z'(t)=0$ for all $t>0$. Since $g_z$ has zero derivative on the interval $(0,\infty)$, which is convex, it is constant there. Its right-hand limit at $0$ is $0$: indeed $u(t)\to u_0$ and $u'(t)\to v_0$, so both inner products in the definition of $g_z(t)$ tend to $0$. Hence

$$
g_z(t)=0
$$

for all $t>0$, and therefore $g_z(t)\to 0$ as $t\to\infty$.

On the other hand, as $t\to\infty$, the velocity tends to $0$, so

$$
\langle u'(t)-v_0,z\rangle\to \langle -v_0,z\rangle.
$$

The weak convergence $u(t)\rightharpoonup \hat u$, together with the cited theorem `weakSpace_continuous_inner_right z`, implies

$$
\langle u(t)-u_0,z\rangle\to \langle \hat u-u_0,z\rangle.
$$

Thus

$$
g_z(t)\to \langle -v_0,z\rangle+\gamma\langle \hat u-u_0,z\rangle.
$$

Since $g_z(t)\to 0$, uniqueness of limits gives

$$
\langle -v_0,z\rangle+\gamma\langle \hat u-u_0,z\rangle=0.
$$

Rearranging and using $y=u_0+\gamma^{-1}v_0$ yields

$$
\langle \hat u-y,z\rangle=0.
$$

Now the proof shows that $\hat u$ is the projection of $y$ onto $S$. The cited variational characterization
`eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hS_cheb hSconv`
says that, for a Chebyshev convex set $S$, a point $p$ is the projection of $y$ onto $S$ exactly when $p\in S$ and

$$
\langle z-p,y-p\rangle\le 0
$$

for every $z\in S$. Here $p=\hat u$, and $\hat u\in S$ by `hhat`. For any $z\in S$, the previously proved orthogonality gives both

$$
\langle \hat u-y,z\rangle=0
$$

and, taking $z=\hat u$,

$$
\langle \hat u-y,\hat u\rangle=0.
$$

Therefore

$$
\langle z-\hat u,y-\hat u\rangle=0\le 0.
$$

So $\hat u=P_S(y)$.

Finally, the cited theorem `quadratic_scalar_damped_tendsto_weak_limit hPhi sys hhat hWeak A hPhiA` applies. It says that in the quadratic case, weak convergence to a minimizer $\hat u$ upgrades to strong convergence:

$$
u(t)\to \hat u.
$$

Since $\hat u=P_S(y)$, this is exactly

$$
u(t)\to P_S(y)
$$

as $t\to\infty$, which proves the fourth conclusion.

