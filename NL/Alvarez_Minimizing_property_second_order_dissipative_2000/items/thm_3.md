## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/thm_3.lean`

## Lean statement
```lean
theorem operator_damped_minimizing_property {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {Gamma : H →L[ℝ] H} {Phi : H → ℝ}
    {gradPhi : H → H} {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (hGamma : HasCoerciveDamping Gamma) (sys : OperatorDissipativeSystem Gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) ∧
    Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) ∧
    Tendsto (fun t => Phi (sys.u t)) atTop (nhds (sInf (Set.range Phi))) ∧
    ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty →
      ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi),
      Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop (nhds (toWeakSpace ℝ H uhat)))
```

## Statement explanation
Let $H$ be a complete real inner product space. Let $\Gamma:H\to H$ be a continuous linear operator, let $\Phi:H\to\mathbb R$ be a scalar potential, let $g:H\to H$, and let $u_0,v_0\in H$. The hypothesis $h_\Phi$ says that $\Phi$ satisfies the potential assumption. In the proof this is used to provide that $\Phi$ is convex, continuous, and bounded below; consequently the infimum

$$
\inf \Phi(H)=\mathrm{sInf}(\mathrm{range}\Phi)
$$

is a real number, and the set of minimizers

$$
\mathrm{argmin}\Phi=\{x\in H:\Phi(x)=\inf \Phi(H)\}
$$

is well-defined. The hypothesis $h_\Gamma$ says that $\Gamma$ has coercive damping: there exists $\gamma>0$ such that for every $x\in H$,

$$
\gamma\|x\|^2\le \langle \Gamma x,x\rangle_{\mathbb R}.
$$

The parameter `sys` is an operator dissipative system with damping $\Gamma$, potential $\Phi$, gradient $g$, and initial data $u_0,v_0$. It supplies the trajectory $u=\texttt{sys.u}:\mathbb R\to H$ of the system and, in the proof, also the self-adjointness of $\Gamma$.

The theorem defines the velocity as

$$
u'(t):=\mathrm{fderiv}_{\mathbb R}u(t)(1),
$$

so that $u'(t)\in H$ is the derivative of the trajectory at time $t$. It then asserts the following four facts.

1. The squared speed is integrable on $[0,\infty)$:

$$
\int_0^\infty \|u'(t)\|^2\,dt<\infty.
$$

2. The velocity vanishes at infinity:

$$
u'(t)\to 0\qquad (t\to\infty).
$$

3. The potential along the trajectory converges to the infimum of the potential values:

$$
\Phi(u(t))\to \inf \Phi(H)\qquad (t\to\infty).
$$

4. If the minimizer set is nonempty, then there exists a minimizer $u_\ast\in\mathrm{argmin}\Phi$ such that the trajectory converges weakly to $u_\ast$:

$$
u(t)\rightharpoonup u_\ast\qquad (t\to\infty),
$$

equivalently

$$
\texttt{toWeakSpace}(u(t))\to \texttt{toWeakSpace}(u_\ast).
$$

Thus the theorem says that the damped second-order system dissipates energy, loses its velocity, drives the potential down to its minimal value, and, when minimizers exist, converges weakly to a minimizer.

## Lean proof
```lean
by
  rcases hGamma with ⟨gamma, hgamma, hcoercive⟩
  have hvel : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    operator_velocity_sq_integrableOn_Ici_zero hPhi ⟨gamma, hgamma, hcoercive⟩ sys
  have hvelShift : IntegrableOn (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) (Set.Ici 0) :=
    operator_shifted_velocity_sq_integrableOn_Ici_zero sys hvel
  obtain ⟨velocityErrorLimit, hvelocityErrorLimit⟩ :=
    operator_shifted_causal_velocity_error_converges sys hgamma hvelShift
  obtain ⟨energyLimit, henergyLimit⟩ :=
    operator_energy_converges hPhi hgamma hcoercive sys
  let energy : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let velocityError : ℝ → ℝ := fun t => (3 / 2 : ℝ) *
    ∫ theta in 0..t, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2
  have henergy : Tendsto energy atTop (nhds energyLimit) := by
    simpa [energy] using henergyLimit
  have hvelocityError : Tendsto velocityError atTop (nhds velocityErrorLimit) := by
    simpa [velocityError] using hvelocityErrorLimit
  have henergyLower : ∀ t : ℝ, sInf (Set.range Phi) ≤ energy t := by
    intro t
    dsimp [energy]
    have hpotential := potential_sInf_le hPhi (sys.u t)
    have hkinetic : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      positivity
    linarith
  have hpotential_le_energy : ∀ t : ℝ, Phi (sys.u t) ≤ energy t := by
    intro t
    dsimp [energy]
    have hkinetic : 0 ≤ (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      positivity
    linarith
  have henergyLowerLimit : sInf (Set.range Phi) ≤ energyLimit := by
    exact ge_of_tendsto henergy (Filter.Eventually.of_forall henergyLower)
  let comparisonCoefficient : ℝ → ℝ := fun t =>
    (gamma * t - 1 + Real.exp (-gamma * t)) / gamma ^ 2
  have hcomparisonCoefficient : Tendsto comparisonCoefficient atTop atTop := by
    let lower : ℝ → ℝ := fun t => (1 / gamma) * t + (-1 / gamma ^ 2)
    have hlower : Tendsto lower atTop atTop := by
      have hlinear : Tendsto (fun t : ℝ => (1 / gamma) * t) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos (one_div_pos.mpr hgamma)).mpr tendsto_id
      exact tendsto_atTop_add_const_right atTop (-1 / gamma ^ 2) hlinear
    apply Filter.tendsto_atTop_mono _ hlower
    intro t
    have hsq : 0 < gamma ^ 2 := sq_pos_of_pos hgamma
    have hexp : 0 ≤ Real.exp (-gamma * t) := (Real.exp_pos _).le
    have hrewrite : lower t = (gamma * t - 1) / gamma ^ 2 := by
      dsimp [lower]
      field_simp [hgamma.ne']
      ring
    rw [hrewrite]
    dsimp [comparisonCoefficient]
    exact (div_le_div_iff_of_pos_right hsq).mpr (by linarith)
  refine ⟨hvel, ?_⟩
  rcases hPhi.bounded_below with ⟨m, hm⟩
  have henergyEq : energyLimit = sInf (Set.range Phi) := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < energyLimit - sInf (Set.range Phi) := by
        linarith [henergyLowerLimit]
      let delta : ℝ := (energyLimit - sInf (Set.range Phi)) / 4
      have hdelta : 0 < delta := by
        dsimp [delta]
        linarith
      rcases exists_lt_of_csInf_lt (b := sInf (Set.range Phi) + delta)
        (Set.range_nonempty Phi) (by
          dsimp [delta]
          linarith) with ⟨_, ⟨x, rfl⟩, hx⟩
      have henergyShift : Tendsto (fun T : ℝ => energy (T + 1)) atTop
          (nhds energyLimit) := by
        have hshift : Tendsto (fun T : ℝ => T + 1) atTop atTop := by
          simpa [add_comm] using
            (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
        exact henergy.comp hshift
      have hcx : ∀ᶠ T in atTop, Phi x - energy (T + 1) ≤ -delta := by
        have hev := (tendsto_order.1 henergyShift).1 (energyLimit - delta) (by
          linarith)
        filter_upwards [hev] with T hT
        have hx' : Phi x ≤ sInf (Set.range Phi) + delta := hx.le
        have hrel : energyLimit - sInf (Set.range Phi) = 4 * delta := by
          dsimp [delta]
          ring
        linarith [hx, hT, hrel]
      let q : ℝ → ℝ := fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2
      have hqIoi : IntegrableOn q (Set.Ioi 0) := by
        exact (integrableOn_Ici_iff_integrableOn_Ioi).mp hvelShift
      let Q : ℝ := ∫ s in Set.Ioi 0, q s
      have hQ : ∀ T : ℝ, 0 ≤ T → (∫ s in 0..T, q s) ≤ Q := by
        intro T hT
        have htail : 0 ≤ ∫ s in Set.Ioi T, q s := by
          exact MeasureTheory.integral_nonneg (fun s => sq_nonneg _)
        have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hqIoi hT
        linarith
      let A : H →L[ℝ] H := Gamma - gamma • ContinuousLinearMap.id ℝ H
      let phi : ℝ → ℝ := fun s =>
        (1 / 2 : ℝ) * ‖sys.u (s + 1) - x‖ ^ 2
      let rho : ℝ → ℝ := fun s =>
        (1 / 2 : ℝ) * ⟪A (sys.u (s + 1) - x), sys.u (s + 1) - x⟫_ℝ
      have hphi_deriv : ∀ T : ℝ, 0 ≤ T →
          deriv phi T = ⟪fderiv ℝ sys.u (T + 1) 1,
            sys.u (T + 1) - x⟫_ℝ := by
        intro T hT
        have hu : HasDerivAt (fun s : ℝ => sys.u (s + 1) - x)
            (fderiv ℝ sys.u (T + 1) 1) T := by
          have hcomp : HasDerivAt (fun s : ℝ => sys.u (s + 1))
              (fderiv ℝ sys.u (T + 1) 1) T := by
            have hbase := (operatorSystem_differentiableAt_pos sys (t := T + 1)
              (by linarith)).hasFDerivAt
            have hcomp' : HasDerivAt (fun s : ℝ => sys.u (s + 1))
                (fderiv ℝ sys.u (T + 1) 1) T := by
              simpa [Function.comp_def] using
                HasFDerivAt.comp_hasDerivAt T hbase
                  ((hasDerivAt_id T).add_const 1)
            exact hcomp'
          exact hcomp.sub_const x
        have hsquare := (hasDerivAt_const T (1 / 2 : ℝ)).mul (hu.norm_sq)
        convert hsquare.deriv using 1 <;> simp [phi, real_inner_comm] <;> ring
      have hrho_nonneg : ∀ T : ℝ, 0 ≤ rho T := by
        intro T
        have hA := operator_damping_remainder_nonnegative hcoercive
          (sys.u (T + 1) - x)
        have hA' : 0 ≤ ⟪A (sys.u (T + 1) - x),
            sys.u (T + 1) - x⟫_ℝ := by
          simpa [A] using hA
        dsimp [rho]
        nlinarith
      have henergy_le_one : ∀ T : ℝ, 0 ≤ T → energy (T + 1) ≤ energy 1 := by
        intro T hT
        have hE := operator_energy_antitone_pos hPhi hgamma hcoercive sys
          (a := 1) (b := T + 1) (by norm_num) (by linarith)
        simpa [energy] using hE
      let K : ℝ := (energy 1 - m) / gamma
      have hLB : ∀ T : ℝ, 0 ≤ T →
          -K ≤ deriv phi T + gamma * phi T + rho T := by
        intro T hT
        have hkin : (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (T + 1) 1‖ ^ 2 ≤
            energy 1 - m := by
          have hE := henergy_le_one T hT
          have hmT := hm (sys.u (T + 1))
          dsimp [energy] at hE ⊢
          linarith
        have hinner := real_inner_le_norm
          (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - x)
        have hinner' : -‖fderiv ℝ sys.u (T + 1) 1‖ *
            ‖sys.u (T + 1) - x‖ ≤
            ⟪fderiv ℝ sys.u (T + 1) 1, sys.u (T + 1) - x⟫_ℝ := by
          simpa [mul_comm] using
            (neg_le_of_abs_le (abs_real_inner_le_norm
              (fderiv ℝ sys.u (T + 1) 1) (sys.u (T + 1) - x)))
        have hsq : 0 ≤ (‖fderiv ℝ sys.u (T + 1) 1‖ -
            gamma * ‖sys.u (T + 1) - x‖) ^ 2 := sq_nonneg _
        have hA := hrho_nonneg T
        rw [hphi_deriv T hT]
        dsimp [K, phi] at ⊢
        rw [← neg_div]
        apply (div_le_iff₀ hgamma).2
        dsimp [rho] at hA ⊢
        nlinarith [hkin, hinner', hsq]
      let C : ℝ := deriv phi 0 + gamma * phi 0 + rho 0
      have hlarge : ∀ᶠ T in atTop,
          (K + C + (3 / 2 : ℝ) * Q + 1) / delta < T := eventually_gt_atTop _
      obtain ⟨T, hT0, hTx, hTlarge⟩ :=
        ((eventually_ge_atTop (0 : ℝ)).and (hcx.and hlarge)).exists
      have hfreeze := operator_shifted_distance_frozen_integral hPhi hgamma
        hcoercive sys (x := x) (gamma := gamma) (a := 0) (T := T)
        (by norm_num) hT0
      have hfreeze' : deriv phi T - deriv phi 0 +
          gamma * (phi T - phi 0) + rho T - rho 0 ≤
          (Phi x - energy (T + 1)) * T +
            (3 / 2 : ℝ) * (∫ s in 0..T, q s) := by
        dsimp [phi, rho, A, energy, q] at hfreeze ⊢
        linarith
      have hlower : -K - C ≤ deriv phi T - deriv phi 0 +
          gamma * (phi T - phi 0) + rho T - rho 0 := by
        have h := hLB T hT0
        dsimp [C]
        linarith
      have hupper : (Phi x - energy (T + 1)) * T +
          (3 / 2 : ℝ) * (∫ s in 0..T, q s) ≤
            -delta * T + (3 / 2 : ℝ) * Q := by
        have hq := hQ T hT0
        have hq' := mul_le_mul_of_nonneg_left hq
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        nlinarith [hTx, hq']
      have hcontr : -K - C ≤ -delta * T + (3 / 2 : ℝ) * Q :=
        le_trans hlower (le_trans hfreeze' hupper)
      have hdeltaT : K + C + (3 / 2 : ℝ) * Q + 1 < delta * T := by
        have := (div_lt_iff₀ hdelta).mp hTlarge
        linarith
      linarith
    · exact henergyLowerLimit
  have hpotential : Tendsto (fun t => Phi (sys.u t)) atTop
      (nhds (sInf (Set.range Phi))) := by
    have henergy' : Tendsto energy atTop
        (nhds (sInf (Set.range Phi))) := by
      simpa [henergyEq] using henergy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => sInf (Set.range Phi)) atTop
        (nhds (sInf (Set.range Phi)))) henergy'
    · intro t
      exact potential_sInf_le hPhi (sys.u t)
    · exact hpotential_le_energy
  have hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) := by
    exact operator_velocity_tendsto_zero_of_energy_potential_tendsto sys henergy
      (by simpa [henergyEq] using hpotential)
  refine ⟨hvel0, hpotential, ?_⟩
  intro hne
  let S : Set H := argmin Phi (potential_range_bddBelow hPhi)
  let d : H → H → ℝ := fun x z =>
    (1 / (2 * gamma : ℝ)) * ⟪Gamma (x - z), x - z⟫_ℝ
  have hd_nonneg : ∀ x z : H, 0 ≤ d x z := by
    intro x z
    have hi : 0 ≤ ⟪Gamma (x - z), x - z⟫_ℝ := by
      exact le_trans (by positivity) (hcoercive (x - z))
    exact mul_nonneg (by positivity) hi
  have hd_limit : ∀ z ∈ S, ∃ l : ℝ,
      Tendsto (fun t => d (sys.u t) z) atTop (nhds l) := by
    intro z hz
    simpa [d, S] using
      (operator_distance_to_minimizer_converges hPhi hgamma hcoercive sys hvel hvel0 z hz)
  have hcluster_time : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (sys.u (u n))) atTop (nhds (f z))) → z ∈ S := by
    intro z hz
    rcases hz with ⟨u, hu, hweak⟩
    have hphiSeq : Tendsto (fun n => Phi (sys.u (u n))) atTop
        (nhds (sInf (Set.range Phi))) := by
      simpa [Function.comp_def] using hpotential.comp hu
    have hweak' : Tendsto (fun n => toWeakSpace ℝ H (sys.u (u n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right _ z).2
      intro y
      let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) y
      have hf := hweak f
      simpa [f, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
    have hzle : Phi z ≤ sInf (Set.range Phi) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hev := (tendsto_order.1 hphiSeq).2 (sInf (Set.range Phi) + ε) (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      let v : ℕ → H := fun n => sys.u (u (n + N))
      have hv_mem : ∀ n : ℕ, v n ∈ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        intro n
        dsimp [v]
        exact le_of_lt (hN (n + N) (by omega))
      have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        exact eventually_atTop.2 ⟨b, fun n hn => le_trans hn (Nat.le_add_right n N)⟩
      have hvweak : Tendsto (fun n => toWeakSpace ℝ H (v n)) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [v, Function.comp_def] using hweak'.comp hshift
      have hclosed : IsClosed {w : H | Phi w ≤ sInf (Set.range Phi) + ε} :=
        isClosed_le hPhi.contDiff.continuous continuous_const
      have hconvex : Convex ℝ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        simpa only [Set.mem_univ, true_and] using hPhi.convex.convex_le
          (sInf (Set.range Phi) + ε)
      exact mem_of_tendsto_weakly_of_isClosed_convex hclosed hconvex hv_mem hvweak
    have hzmin : Phi z = sInf (Set.range Phi) :=
      le_antisymm hzle (potential_sInf_le hPhi z)
    simpa [S, argmin] using hzmin
  have htime_sequence : ∀ (t : ℕ → ℝ), Tendsto t atTop atTop →
      ∃ z ∈ S, Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
    intro t ht
    let x : ℕ → H := fun n => sys.u (t n)
    have hdist_seq : ∀ z ∈ S, ∃ l : ℝ,
        Tendsto (fun n => d (x n) z) atTop (nhds l) := by
      intro z hz
      rcases hd_limit z hz with ⟨l, hl⟩
      exact ⟨l, by simpa [x, Function.comp_def] using hl.comp ht⟩
    rcases hne with ⟨z0, hz0⟩
    rcases hd_limit z0 hz0 with ⟨l0, hl0⟩
    have hq0 : Tendsto (fun n => d (x n) z0) atTop (nhds l0) := by
      simpa [x, Function.comp_def] using hl0.comp ht
    have hq_bounded : Bornology.IsBounded (Set.range (fun n => d (x n) z0)) :=
      Metric.isBounded_range_of_tendsto _ hq0
    rcases isBounded_iff_forall_norm_le.mp hq_bounded with ⟨C, hC⟩
    have hbounded : Bornology.IsBounded (Set.range x) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨1 + 2 * C + ‖z0‖, ?_⟩
      rintro y ⟨n, rfl⟩
      have hqC := hC (d (x n) z0) (Set.mem_range_self n)
      have hqC' : d (x n) z0 ≤ C := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg _ _)] at hqC
        exact hqC
      have hden : 0 < 2 * gamma := by positivity
      have hinnerC : ⟪Gamma (x n - z0), x n - z0⟫_ℝ ≤ 2 * gamma * C := by
        have hqC'' : ⟪Gamma (x n - z0), x n - z0⟫_ℝ / (2 * gamma) ≤ C := by
          rw [show ⟪Gamma (x n - z0), x n - z0⟫_ℝ / (2 * gamma) =
              d (x n) z0 by
            dsimp [d]
            field_simp [hgamma.ne']
            ]
          exact hqC'
        simpa [mul_comm] using (div_le_iff₀ hden).mp hqC''
      have hnormsq : ‖x n - z0‖ ^ 2 ≤ 2 * C := by
        have hc := hcoercive (x n - z0)
        nlinarith
      have hCnonneg : 0 ≤ C := by
        have hqC0 := hC (d (x 0) z0) (Set.mem_range_self 0)
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg _ _)] at hqC0
        exact le_trans (hd_nonneg _ _) hqC0
      have hnorm : ‖x n - z0‖ ≤ 1 + 2 * C := by
        nlinarith [sq_nonneg ‖x n - z0‖, norm_nonneg (x n - z0)]
      calc
        ‖x n‖ = ‖(x n - z0) + z0‖ := by abel_nf
        _ ≤ ‖x n - z0‖ + ‖z0‖ := norm_add_le _ _
        _ ≤ 1 + 2 * C + ‖z0‖ := by linarith
    have hcluster_seq : ∀ z,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H z) → z ∈ S := by
      intro z hz
      rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφweak⟩
      apply hcluster_time z
      refine ⟨t ∘ φ, ?_, ?_⟩
      · simpa [Function.comp_def] using ht.comp hφ.tendsto_atTop
      · intro f
        exact tendsto_apply_of_tendsto_toWeakSpace hφweak f
    have hunique : ∀ y z : H,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
          (toWeakSpace ℝ H z) → y = z := by
      intro y z hy hz
      have hyS := hcluster_seq y hy
      have hzS := hcluster_seq z hz
      rcases hdist_seq y hyS with ⟨ly, hly⟩
      rcases hdist_seq z hzS with ⟨lz, hlz⟩
      have hdiff := hlz.sub hly
      have hscaled := hdiff.const_mul (2 * gamma)
      let c : ℝ := ⟪Gamma z, z⟫_ℝ - ⟪Gamma y, y⟫_ℝ
      have hrel : ∀ n : ℕ,
          2 * gamma * (d (x n) z - d (x n) y) =
            2 * ⟪Gamma (x n), y - z⟫_ℝ + c := by
        intro n
        have hsxy := sys.self_adjoint.isSymmetric (x n) (y - z)
        dsimp [d, c]
        field_simp [hgamma.ne']
        simp only [ContinuousLinearMap.map_sub, inner_sub_left, inner_sub_right]
        have hzx : ⟪Gamma z, x n⟫_ℝ = ⟪Gamma (x n), z⟫_ℝ := by
          calc
            ⟪Gamma z, x n⟫_ℝ = ⟪z, Gamma (x n)⟫_ℝ :=
              sys.self_adjoint.isSymmetric z (x n)
            _ = ⟪Gamma (x n), z⟫_ℝ := real_inner_comm _ _
        have hyx : ⟪Gamma y, x n⟫_ℝ = ⟪Gamma (x n), y⟫_ℝ := by
          calc
            ⟪Gamma y, x n⟫_ℝ = ⟪y, Gamma (x n)⟫_ℝ :=
              sys.self_adjoint.isSymmetric y (x n)
            _ = ⟪Gamma (x n), y⟫_ℝ := real_inner_comm _ _
        rw [hzx, hyx]
        ring
      have hlin : Tendsto (fun n => 2 * ⟪Gamma (x n), y - z⟫_ℝ) atTop
          (nhds (2 * gamma * (lz - ly) - c)) := by
        have htmp := hscaled.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
        apply htmp.congr'
        filter_upwards with n
        rw [hrel n]
        ring
      rcases hy with ⟨φ, hφ, hφweak⟩
      rcases hz with ⟨ψ, hψ, hψweak⟩
      let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) (Gamma (y - z))
      have hf_y : Tendsto (fun n => ⟪Gamma (x (φ n)), y - z⟫_ℝ) atTop
          (nhds (⟪Gamma y, y - z⟫_ℝ)) := by
        have hf := tendsto_apply_of_tendsto_toWeakSpace hφweak f
        have heq : ∀ v : H, f v = ⟪Gamma v, y - z⟫_ℝ := by
          intro v
          dsimp [f]
          rw [real_inner_comm]
          exact (sys.self_adjoint.isSymmetric v (y - z)).symm
        have hf' : Tendsto (fun n => f (x (φ n))) atTop
            (nhds (⟪Gamma y, y - z⟫_ℝ)) := by
          simpa [heq y] using hf
        apply hf'.congr'
        filter_upwards with n
        rw [heq]
      have hf_z : Tendsto (fun n => ⟪Gamma (x (ψ n)), y - z⟫_ℝ) atTop
          (nhds (⟪Gamma z, y - z⟫_ℝ)) := by
        have hf := tendsto_apply_of_tendsto_toWeakSpace hψweak f
        have heq : ∀ v : H, f v = ⟪Gamma v, y - z⟫_ℝ := by
          intro v
          dsimp [f]
          rw [real_inner_comm]
          exact (sys.self_adjoint.isSymmetric v (y - z)).symm
        have hf' : Tendsto (fun n => f (x (ψ n))) atTop
            (nhds (⟪Gamma z, y - z⟫_ℝ)) := by
          simpa [heq z] using hf
        apply hf'.congr'
        filter_upwards with n
        rw [heq]
      have hfy2 := hf_y.const_mul (2 : ℝ)
      have hfz2 := hf_z.const_mul (2 : ℝ)
      have hy_eq : 2 * ⟪Gamma y, y - z⟫_ℝ = 2 * gamma * (lz - ly) - c :=
        tendsto_nhds_unique hfy2 (hlin.comp hφ.tendsto_atTop)
      have hz_eq : 2 * ⟪Gamma z, y - z⟫_ℝ = 2 * gamma * (lz - ly) - c :=
        tendsto_nhds_unique hfz2 (hlin.comp hψ.tendsto_atTop)
      have hcross : ⟪Gamma y, y - z⟫_ℝ - ⟪Gamma z, y - z⟫_ℝ = 0 := by
        linarith [hy_eq, hz_eq]
      have hzero : ⟪y - z, Gamma (y - z)⟫_ℝ = 0 := by
        rw [inner_sub_left]
        calc
          ⟪y, Gamma (y - z)⟫_ℝ - ⟪z, Gamma (y - z)⟫_ℝ =
              ⟪Gamma y, y - z⟫_ℝ - ⟪Gamma z, y - z⟫_ℝ := by
                congr 1
                · exact (sys.self_adjoint.isSymmetric y (y - z)).symm
                · exact (sys.self_adjoint.isSymmetric z (y - z)).symm
          _ = 0 := hcross
      have hcoer := hcoercive (y - z)
      have hnormsq : ‖y - z‖ ^ 2 ≤ 0 := by
        rw [real_inner_comm] at hzero
        nlinarith
      have hnorm : ‖y - z‖ = 0 := by
        nlinarith [sq_nonneg ‖y - z‖, norm_nonneg (y - z)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x).2
        ⟨hbounded, hunique⟩ with ⟨z, hz⟩
    have hzcluster : IsSequentialClusterPt (fun n => toWeakSpace ℝ H (x n))
        (toWeakSpace ℝ H z) := by
      exact ⟨id, strictMono_id, by simpa using hz⟩
    exact ⟨z, hcluster_seq z hzcluster, by simpa [x] using hz⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  obtain ⟨uhat, hUhat, hUweak⟩ := htime_sequence (fun n : ℕ => (n : ℝ)) hnat
  have h_all_sequences : ∀ t : ℕ → ℝ, Tendsto t atTop atTop →
      Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H uhat)) := by
    intro t ht
    let q : ℕ → ℝ := fun n => if Even n then ((n / 2 : ℕ) : ℝ) else t (n / 2)
    have hinterleave : Tendsto q atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro R
      obtain ⟨N, hN⟩ := exists_nat_ge R
      rcases (eventually_atTop.1 (ht.eventually (eventually_ge_atTop R))) with ⟨M, hM⟩
      refine ⟨2 * max N M, ?_⟩
      intro k hk
      have hdiv : max N M ≤ k / 2 := by omega
      by_cases he : Even k
      · simp [q, he]
        exact le_trans hN (Nat.cast_le.2 (le_trans (le_max_left _ _) hdiv))
      · simp [q, he]
        exact hM _ (le_trans (le_max_right _ _) hdiv)
    have hq : Tendsto q atTop atTop := hinterleave
    obtain ⟨w, hwS, hqweak⟩ := htime_sequence q hq
    have hEven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn => by omega⟩
    have hOdd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn => by omega⟩
    have hq_even : ∀ n : ℕ, q (2 * n) = (n : ℝ) := by
      intro n
      simp only [q, if_pos (even_two_mul n)]
      norm_cast
      omega
    have hq_odd : ∀ n : ℕ, q (2 * n + 1) = t n := by
      intro n
      simp only [q, if_neg (Nat.not_even_two_mul_add_one n)]
      congr 1
      omega
    have hnat_w : Tendsto (fun n : ℕ => toWeakSpace ℝ H (sys.u (n : ℝ))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hEven using 1
      ext n
      simp [Function.comp, hq_even]
    have hzw : uhat = w :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique hUweak hnat_w)
    have ht_w : Tendsto (fun n => toWeakSpace ℝ H (sys.u (t n))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hOdd using 1
      ext n
      simp [Function.comp, hq_odd]
    simpa [hzw] using ht_w
  refine ⟨uhat, hUhat, ?_⟩
  apply (weakConvergence_iff_forall_tendsto_inner_right sys.u uhat).2
  intro y
  have hreal : Tendsto (fun t : ℝ => ⟪sys.u t, y⟫_ℝ) atTop
      (nhds (⟪uhat, y⟫_ℝ)) := by
    by_contra hg
    rw [Metric.tendsto_atTop] at hg
    push Not at hg
    rcases hg with ⟨ε, hε, hbad⟩
    choose s hs_ge hs_bad using hbad
    have hs : Tendsto (fun n : ℕ => s n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro R
      obtain ⟨N, hN⟩ := exists_nat_ge R
      refine ⟨N, fun n hn => le_trans (le_trans hN (Nat.cast_le.2 hn)) (hs_ge n)⟩
    have hseq := h_all_sequences (fun n : ℕ => s n) hs
    have hf := tendsto_apply_of_tendsto_toWeakSpace hseq
      ((InnerProductSpace.toDual ℝ H) y)
    have hseq' : Tendsto (fun n : ℕ => ⟪sys.u (s n), y⟫_ℝ) atTop
        (nhds (⟪uhat, y⟫_ℝ)) := by
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
    rw [Metric.tendsto_atTop] at hseq'
    rcases hseq' ε hε with ⟨N, hN⟩
    exact (not_lt_of_ge (hs_bad N)) (by simpa using hN N le_rfl)
  exact hreal
```

## Proof explanation
The proof begins by unpacking the coercive damping hypothesis. The tactic `rcases hGamma with ⟨gamma, hgamma, hcoercive⟩` replaces $h_\Gamma$ by a real number $\gamma>0$ and the pointwise coercivity inequality

$$
\gamma\|x\|^2\le \langle \Gamma x,x\rangle_{\mathbb R}
\qquad (x\in H).
$$

The first conjunct is obtained directly from `operator_velocity_sq_integrableOn_Ici_zero`. That result says that under the potential assumption on $\Phi$, coercive damping for $\Gamma$, and the operator system `sys`, the function

$$
t\mapsto \|u'(t)\|^2
$$

is integrable on $[0,\infty)$. Applying it with the repackaged coercive damping hypothesis proves the first part of the theorem.

Next, `operator_shifted_velocity_sq_integrableOn_Ici_zero` is applied to the previous integrability. It states that if

$$
t\mapsto \|u'(t)\|^2
$$

is integrable on $[0,\infty)$, then the shifted function

$$
s\mapsto \|u'(s+1)\|^2
$$

is also integrable on $[0,\infty)$. This is a tail-shift integrability statement and is used to prepare the causal velocity-error estimate.

The lemma `operator_shifted_causal_velocity_error_converges` is then invoked. It gives the existence of a real number $L$ such that

$$
\frac32\int_0^t\int_0^\theta
 e^{-\gamma(\theta-s)}\|u'(s+1)\|^2\,ds\,d\theta
\longrightarrow L
\qquad (t\to\infty).
$$

This is a convergence statement for an exponentially damped double integral of the shifted squared velocity. In the displayed proof this limit is recorded as `velocityErrorLimit`, although the later central energy argument does not directly reuse this particular limit again.

The lemma `operator_energy_converges` is then applied. It says that under the same hypotheses on $\Phi$, $\gamma$, and `sys`, the energy

$$
E(t)=\frac12\|u'(t)\|^2+\Phi(u(t))
$$

converges to some real number $E_\infty$. In the proof this limit is called `energyLimit` and the notation `energy` is introduced for $E(t)$.

Two elementary pointwise inequalities are then proved. First, `potential_sInf_le` gives

$$
\inf \Phi(H)\le \Phi(u(t))
$$

for every $t$. Since the kinetic term satisfies

$$
0\le \frac12\|u'(t)\|^2,
$$

one obtains

$$
\inf \Phi(H)\le E(t).
$$

Second, the same nonnegativity of the kinetic term gives

$$
\Phi(u(t))\le E(t).
$$

Since $E(t)\to E_\infty$, the inequality $\inf \Phi(H)\le E(t)$ passed to the limit yields

$$
\inf \Phi(H)\le E_\infty.
$$

The proof then introduces an auxiliary comparison coefficient

$$
C(t)=\frac{\gamma t-1+e^{-\gamma t}}{\gamma^2}
$$

and proves $C(t)\to+\infty$. This is done by comparing it with

$$
\frac{\gamma t-1}{\gamma^2}=\frac1\gamma t-\frac1{\gamma^2},
$$

which clearly tends to $+\infty$, and using

$$
\frac{\gamma t-1+e^{-\gamma t}}{\gamma^2}
\ge \frac{\gamma t-1}{\gamma^2},
$$

which follows from $e^{-\gamma t}\ge0$. This divergence estimate is auxiliary; it is not used later in the displayed proof.

The main energy argument now proves

$$
E_\infty=\inf \Phi(H).
$$

The inequality $\inf \Phi(H)\le E_\infty$ was already proved. For the reverse inequality, suppose for contradiction that $E_\infty>\inf \Phi(H)$. Put

$$
\delta=\frac{E_\infty-\inf \Phi(H)}4>0.
$$

By the definition of the infimum of a nonempty set, there exists $x\in H$ such that

$$
\Phi(x)<\inf \Phi(H)+\delta.
$$

Since $E(t)\to E_\infty$, eventually

$$
\Phi(x)-E(T+1)\le -\delta.
$$

This is the sequence of estimates recorded in `hcx`.

The proof now studies the shifted distance to the fixed point $x$. It defines

$$
q(s)=\|u'(s+1)\|^2,
$$

which is integrable on $(0,\infty)$, and sets

$$
Q=\int_{(0,\infty)} q(s)\,ds.
$$

Because the tail has nonnegative integral, for every $T\ge0$,

$$
\int_0^T q(s)\,ds\le Q.
$$

It also defines

$$
A=\Gamma-\gamma I,\qquad
\phi(s)=\frac12\|u(s+1)-x\|^2,
$$

and

$$
\rho(s)=\frac12\langle A(u(s+1)-x),u(s+1)-x\rangle_{\mathbb R}.
$$

The derivative of $\phi$ is computed using `operatorSystem_differentiableAt_pos`, which says that $u$ is differentiable at every positive time. Since $T\ge0$ implies $T+1>0$, the chain rule gives

$$
\mathrm{deriv}\phi(T)
=\langle u'(T+1),u(T+1)-x\rangle_{\mathbb R}.
$$

The lemma `operator_damping_remainder_nonnegative` says that if $\gamma\|y\|^2\le\langle \Gamma y,y\rangle_{\mathbb R}$ for all $y$, then

$$
0\le \langle(\Gamma-\gamma I)y,y\rangle_{\mathbb R}.
$$

Applying this to $y=u(T+1)-x$ gives

$$
0\le \rho(T).
$$

The energy monotonicity lemma `operator_energy_antitone_pos` is then used. It states that for $0<a\le b$,

$$
E(b)\le E(a).
$$

Taking $a=1$ and $b=T+1$ gives

$$
E(T+1)\le E(1).
$$

If $m\le\Phi(y)$ for all $y$ is the lower bound supplied by the potential assumption, then

$$
\frac12\|u'(T+1)\|^2\le E(1)-m.
$$

Setting

$$
K=\frac{E(1)-m}{\gamma},
$$

and combining this kinetic bound with Cauchy–Schwarz,

$$
\langle u'(T+1),u(T+1)-x\rangle_{\mathbb R}
\ge -\|u'(T+1)\|\|u(T+1)-x\|,
$$

and with the nonnegativity of

$$
\bigl(\|u'(T+1)\|-\gamma\|u(T+1)-x\|\bigr)^2,
$$

the proof obtains the lower bound

$$
-K\le \mathrm{deriv}\phi(T)+\gamma\phi(T)+\rho(T)
$$

for all $T\ge0$.

Let

$$
C=\mathrm{deriv}\phi(0)+\gamma\phi(0)+\rho(0).
$$

Subtracting $C$ from the previous lower bound gives

$$
-K-C\le
\mathrm{deriv}\phi(T)-\mathrm{deriv}\phi(0)
+\gamma(\phi(T)-\phi(0))+\rho(T)-\rho(0).
$$

The frozen-distance lemma `operator_shifted_distance_frozen_integral` is invoked with $a=0$ and the chosen $T$. The supplied context truncates the full statement of that lemma, but the proof uses the following consequence obtained after unfolding the definitions of $\phi,\rho,A,E,q$:

$$
\begin{aligned}
&\mathrm{deriv}\phi(T)-\mathrm{deriv}\phi(0)
+\gamma(\phi(T)-\phi(0))+\rho(T)-\rho(0)\\
&\qquad\le
(\Phi(x)-E(T+1))T
+\frac32\int_0^T q(s)\,ds.
\end{aligned}
$$

Combining this upper estimate with the eventual inequality

$$
\Phi(x)-E(T+1)\le-\delta
$$

and with

$$
\int_0^T q(s)\,ds\le Q
$$

gives

$$
-K-C\le -\delta T+\frac32 Q.
$$

But $T$ is chosen so large that

$$
K+C+\frac32 Q+1<\delta T.
$$

This is equivalent to

$$
-K-C> -\delta T+\frac32 Q+1,
$$

contradicting the previous inequality. Hence $E_\infty\le\inf \Phi(H)$, and therefore

$$
E_\infty=\inf \Phi(H).
$$

With this equality established, the convergence of the potential follows by the squeeze theorem. For every $t$,

$$
\inf \Phi(H)\le \Phi(u(t))\le E(t),
$$

and both the constant sequence $\inf \Phi(H)$ and the energy $E(t)$ tend to $\inf \Phi(H)$. The lemma `tendsto_of_tendsto_of_tendsto_of_le_of_le` formalizes this squeeze and yields

$$
\Phi(u(t))\to \inf \Phi(H).
$$

The velocity convergence is then obtained from `operator_velocity_tendsto_zero_of_energy_potential_tendsto`. That lemma says that if the total energy

$$
E(t)=\frac12\|u'(t)\|^2+\Phi(u(t))
$$

converges to a limit $m$ and the potential $\Phi(u(t))$ also converges to the same $m$, then the velocity $u'(t)$ tends to $0$. Here $m=\inf \Phi(H)$. Indeed,

$$
\frac12\|u'(t)\|^2=E(t)-\Phi(u(t))\to0,
$$

so $u'(t)\to0$.

It remains to prove the conditional weak convergence statement. The proof assumes that the minimizer set

$$
S=\mathrm{argmin}\Phi
$$

is nonempty. It defines

$$
d(x,z)=\frac1{2\gamma}\langle \Gamma(x-z),x-z\rangle_{\mathbb R}.
$$

Coercivity gives $d(x,z)\ge0$. The lemma `operator_distance_to_minimizer_converges` is applied to each $z\in S$. It states that under the previously established integrability and velocity convergence, there exists a real number $l$ such that

$$
d(u(t),z)\to l\qquad (t\to\infty).
$$

The proof then shows that any weak cluster point of a sequence of trajectory values must lie in $S$. Suppose $t_n\to\infty$ and $u(t_n)\to z$ weakly. Since $\Phi(u(t))\to\inf \Phi(H)$, composing with $t_n$ gives

$$
\Phi(u(t_n))\to\inf \Phi(H).
$$

For every $\varepsilon>0$, eventually

$$
\Phi(u(t_n))\le \inf \Phi(H)+\varepsilon.
$$

The sublevel set

$$
\{w\in H:\Phi(w)\le \inf \Phi(H)+\varepsilon\}
$$

is closed because $\Phi$ is continuous, and it is convex because $\Phi$ is convex. The lemma `mem_of_tendsto_weakly_of_isClosed_convex` says that a weak limit of a sequence in a closed convex set belongs to that set. Hence $z$ belongs to the sublevel set for every $\varepsilon>0$, so

$$
\Phi(z)\le \inf \Phi(H).
$$

On the other hand, `potential_sInf_le` gives

$$
\inf \Phi(H)\le \Phi(z).
$$

Thus $\Phi(z)=\inf \Phi(H)$, so $z\in S$.

Next the proof takes an arbitrary sequence of times $t_n\to\infty$, writes

$$
x_n=u(t_n),
$$

and proves that the sequence $x_n$ is bounded. Choose some $z_0\in S$, possible because $S\neq\emptyset$. Since $d(x_n,z_0)$ converges, its range is bounded. Coercivity then bounds $\|x_n-z_0\|^2$, and the triangle inequality bounds $\|x_n\|$. Hence the range of $x_n$ is bounded.

Any weak sequential cluster point of $x_n$ lies in $S$ by the previous paragraph. The proof then proves uniqueness of such weak sequential cluster points. Suppose $y,z\in S$ are two weak sequential cluster points. Since $d(x_n,y)$ and $d(x_n,z)$ converge, say to $l_y$ and $l_z$, one has

$$
2\gamma(d(x_n,z)-d(x_n,y))\to 2\gamma(l_z-l_y).
$$

Using the self-adjointness of $\Gamma$, the proof establishes the algebraic identity

$$
2\gamma(d(x_n,z)-d(x_n,y))
=
2\langle \Gamma x_n,y-z\rangle_{\mathbb R}
+\langle \Gamma z,z\rangle_{\mathbb R}-\langle \Gamma y,y\rangle_{\mathbb R}.
$$

Along a subsequence converging weakly to $y$, the inner-product term tends to

$$
2\langle \Gamma y,y-z\rangle_{\mathbb R},
$$

and along a subsequence converging weakly to $z$, it tends to

$$
2\langle \Gamma z,y-z\rangle_{\mathbb R}.
$$

By uniqueness of limits, these two quantities are equal, so

$$
\langle \Gamma y,y-z\rangle_{\mathbb R}
=
\langle \Gamma z,y-z\rangle_{\mathbb R}.
$$

Using self-adjointness again,

$$
\langle y-z,\Gamma(y-z)\rangle_{\mathbb R}=0.
$$

Coercivity gives

$$
\gamma\|y-z\|^2\le \langle y-z,\Gamma(y-z)\rangle_{\mathbb R}=0,
$$

hence $y=z$. Thus there is at most one weak sequential cluster point.

The lemma `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` states that for a sequence in a Hilbert space, weak convergence is equivalent to boundedness of its range together with existence of at most one weak sequential cluster point. The proof has established both, so the sequence $x_n=u(t_n)$ has a weak limit $z$, and the cluster-point argument shows $z\in S$.

Applying this to the sequence of natural times $t_n=n$ gives a point

$$
u_\ast\in S
$$

such that

$$
u(n)\rightharpoonup u_\ast
\qquad (n\to\infty).
$$

The proof then upgrades this to every sequence of real times $t_n\to\infty$. It interleaves the given sequence with the natural numbers by defining

$$
q_{2n}=n,\qquad q_{2n+1}=t_n.
$$

The sequence $q_n\to\infty$, so the previous result gives a weak limit $w\in S$ along $q_n$. The even subsequence gives

$$
u(n)\rightharpoonup w,
$$

while already $u(n)\rightharpoonup u_\ast$. Since the map `toWeakSpace` is injective and weak limits are unique, $w=u_\ast$. The odd subsequence then gives

$$
u(t_n)\rightharpoonup u_\ast.
$$

Therefore every sequence of times tending to infinity has the same weak limit $u_\ast$.

Finally, the proof converts this sequential statement into convergence in the filter sense as $t\to\infty$. The lemma `weakConvergence_iff_forall_tendsto_inner_right` says that weak convergence is equivalent to convergence of all scalar inner products:

$$
u(t)\rightharpoonup u_\ast
\iff
\forall y\in H,\quad
\langle u(t),y\rangle_{\mathbb R}\to
\langle u_\ast,y\rangle_{\mathbb R}.
$$

The proof proves the right-hand side by contradiction. If some $y$ failed to have convergent inner products, then there would exist $\varepsilon>0$ and times $s_n\to\infty$ with

$$
|\langle u(s_n),y\rangle_{\mathbb R}-\langle u_\ast,y\rangle_{\mathbb R}|\ge\varepsilon.
$$

But the all-sequences result gives $u(s_n)\rightharpoonup u_\ast$, and `tendsto_apply_of_tendsto_toWeakSpace` then gives

$$
\langle u(s_n),y\rangle_{\mathbb R}\to
\langle u_\ast,y\rangle_{\mathbb R},
$$

a contradiction. Hence all inner products converge, and the same equivalence gives

$$
u(t)\rightharpoonup u_\ast.
$$

This proves the conditional weak-convergence conclusion.

Throughout the proof, `intro` introduces a hypothesis or a pointwise variable, `rcases` and `obtain` unpack existential statements, `refine` assembles the conjunctive conclusions, `rw` and `simp`/`dsimp` unfold definitions and rewrite identities, `exact` and `simpa` apply named lemmas, `positivity` proves nonnegativity of kinetic-type terms, and `linarith` or `nlinarith` close the linear and nonlinear arithmetic inequalities that combine the estimates.

