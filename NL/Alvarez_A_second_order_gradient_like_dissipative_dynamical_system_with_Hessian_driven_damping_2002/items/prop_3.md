## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/prop_3.lean`

## Lean statement
```lean
theorem din_strong_convergence_of_even_potential {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
  (hΦ : AssumptionH H Φ) (hconvex : ConvexOn ℝ Set.univ Φ)
  (hmin : (Optimization.argminSet Φ).Nonempty)
  (hsol : IsDINTrajectory H Φ α β x)
  (hx : ContDiff ℝ 2 x)
  (hαβ : α * β ≤ 1)
  (heven : ∀ y, Φ y = Φ (-y)) :
  ∃ z, z ∈ Optimization.argminSet Φ ∧ Tendsto x atTop (nhds z)
```

## Statement explanation
The declaration is a strong convergence theorem for a second-order dissipative dynamical system in a real Hilbert space. Let $H$ be a real Hilbert space, let $\Phi:H\to\mathbb R$ be a potential, let $\alpha,\beta\in\mathbb R$, and let $x:\mathbb R\to H$ be a trajectory. The theorem assumes:

- `hΦ`: the bundled assumption `AssumptionH H Φ` on the potential. In the proof the explicitly used consequence is that $\Phi$ is twice continuously differentiable, hence also continuously differentiable.
- `hconvex`: $\Phi$ is convex on all of $H$, meaning that for all $y,z\in H$ and all $t\in[0,1]$,

  $$
  \Phi((1-t)y+tz)\le (1-t)\Phi(y)+t\Phi(z).
  $$

- `hmin`: the set of global minimizers

  $$
  \mathrm{argminSet}(\Phi)=\{z\in H\mid \forall y\in H,\ \Phi(z)\le \Phi(y)\}
  $$

  is nonempty.
- `hsol`: $x$ is an `IsDINTrajectory H Φ α β`, i.e. a trajectory of the Alvarez second-order gradient-like dissipative system with Hessian-driven damping. The proof uses from this predicate that $\alpha>0$, that $\beta>0$, and that at every positive time $t$ the trajectory satisfies the corresponding pointwise vector differential equation.
- `hx`: $x$ is twice continuously differentiable.
- `hαβ`: $\alpha\beta\le 1$.
- `heven`: $\Phi$ is even, meaning $\Phi(y)=\Phi(-y)$ for every $y\in H$.

The conclusion is that there exists a global minimizer $z\in H$ such that

$$
x(t)\to z
$$

strongly in the norm of $H$ as $t\to\infty$. Thus the theorem upgrades the weak convergence of the Alvarez trajectory to strong convergence, under the additional evenness assumption on $\Phi$ and the condition $\alpha\beta\le 1$.

The mathematical role of evenness is that it forces the origin $0$ to be a global minimizer. Indeed, convexity applied to $y$ and $-y$ with weights $1/2$ gives

$$
\Phi\left(\frac12 y+\frac12(-y)\right)
\le \frac12\Phi(y)+\frac12\Phi(-y)=\Phi(y),
$$

and the argument of $\Phi$ on the left is $0$. Hence $\Phi(0)\le \Phi(y)$ for every $y$, so $0\in\mathrm{argminSet}(\Phi)$. This fact is then used together with convex supporting hyperplane inequalities to obtain the crucial estimates that show the trajectory is Cauchy.

## Lean proof
```lean
by
  have hweak := din_weakly_converges_to_argmin Φ α β x hΦ hx hconvex hmin hsol
  rcases hweak with ⟨hdist, ⟨z, hzmin, hzweak⟩⟩
  have hzarg : z ∈ Optimization.argminSet Φ := by
    exact hzmin
  have hzero : (0 : H) ∈ Optimization.argminSet Φ := by
    intro y
    have hmid : Φ ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y)) ≤
        (1 / 2 : ℝ) • Φ y + (1 / 2 : ℝ) • Φ (-y) := by
      exact hconvex.2 (show y ∈ Set.univ by trivial) (show -y ∈ Set.univ by trivial)
        (by norm_num) (by norm_num) (by norm_num)
    have hzero_eq : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y) = (0 : H) := by
      module
    rw [hzero_eq] at hmid
    have heven' : Φ (-y) = Φ y := by simpa using (heven y).symm
    rw [heven'] at hmid
    have hmid' : Φ 0 ≤ (1 / 2 : ℝ) * Φ y + (1 / 2 : ℝ) * Φ y := by
      simpa [smul_eq_mul] using hmid
    nlinarith
  have hα : 0 < α := hsol.1
  have hβ : 0 < β := hsol.2.1
  have hκ : 0 < α * β + 1 := by positivity
  have hΦC2 : ContDiff ℝ 2 Φ := hΦ.twice_continuously_differentiable
  have hΦC1 : ContDiff ℝ 1 Φ := hΦC2.of_le (by norm_num)
  have hgradF : ∀ y, HasFDerivAt Φ (innerSL ℝ (gradient Φ y)) y := by
    intro y
    simpa [innerSL] using (hΦC1.differentiable (by norm_num) y).hasGradientAt.hasFDerivAt
  have hglobal := din_forward_internal Φ hΦ α β hα hβ (x 0) (deriv x 0)
  obtain ⟨xg, vg, accg, hxg0, hvg0, hforwardg, huniq, henergy, hvl2, hgl2,
    hphil, hres, hboundedg, hderivg⟩ := hglobal
  have heq := huniq x (by rfl) (by rfl) hsol hx
  have hxg_eq : ∀ t, 0 ≤ t → xg t = x t := fun t ht => (heq t ht).1.symm
  have hvg_eq : ∀ t, 0 ≤ t → vg t = deriv x t := fun t ht => (heq t ht).2.symm
  have hphi_x : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
    rcases hphil with ⟨l, hl⟩
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hxg_eq t ht]
  have hres_x : Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
    apply hres.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hvg_eq t ht, hxg_eq t ht]
  have hzero_dist : ∃ d : ℝ, Tendsto (fun t => ‖x t‖) atTop (nhds d) := by
    simpa using hdist 0 hzero
  rcases hzero_dist with ⟨d₀, hd₀⟩
  have hnormsq : ∃ l : ℝ, Tendsto (fun t => ‖x t‖ ^ 2) atTop (nhds l) := by
    refine ⟨d₀ ^ 2, ?_⟩
    simpa using hd₀.pow 2
  have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hd₀) 1 zero_lt_one
    let T₀ : ℝ := max T 0
    have htail : ∀ t, T₀ ≤ t → ‖x t‖ ≤ |d₀| + 1 := by
      intro t ht
      have hdist' : dist (‖x t‖) d₀ < 1 := by
        simpa [Real.dist_eq] using hT t (le_trans (le_max_left T 0) ht)
      have habs : |‖x t‖ - d₀| < 1 := by simpa [Real.dist_eq] using hdist'
      have hle : ‖x t‖ - d₀ ≤ |‖x t‖ - d₀| := le_abs_self _
      have hnormd : ‖x t‖ ≤ d₀ + 1 := by nlinarith
      exact hnormd.trans (by linarith [le_abs_self d₀])
    have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
      exact isCompact_Icc.image_of_continuousOn
        (hx.continuous.continuousOn.mono Set.Icc_subset_Ici_self)
    rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (|d₀| + 1), ?_⟩
    rintro q ⟨t, ht, rfl⟩
    by_cases hle : t ≤ T₀
    · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
    · exact (htail t (le_of_not_ge hle)).trans (le_max_right _ _)
  have hpartiii := din_global_properties_part_iii Φ hΦ α β hα hβ (x 0) (deriv x 0)
    x rfl rfl hsol hx hx_bounded
  obtain ⟨hvbound, haccbound, hgradbound, hhessbound, hvlim, hacclim, hgradlim⟩ := hpartiii
  have hgrad_x : ContDiff ℝ 1 (gradient Φ) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦC2)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hd
  have hpartii := din_global_properties_part_ii Φ hΦ α β hα hβ (x 0) (deriv x 0)
    x rfl rfl hsol hx
  have henergy_x := hpartii.1
  let v : ℝ → H := deriv x
  let g : ℝ → H := fun t => gradient Φ (x t)
  let r : ℝ → H := fun t => v t + β • g t
  have hv_at (t : ℝ) : HasDerivAt v (deriv (deriv x) t) t := by
    simpa [v] using (hx.differentiable_deriv_two t).hasDerivAt
  have hx_at (t : ℝ) : HasDerivAt x (v t) t := by
    simpa [v] using (hx.differentiable (by norm_num) t).hasDerivAt
  have hg_at (t : ℝ) : HasDerivAt g ((fderiv ℝ (gradient Φ) (x t)) (v t)) t := by
    simpa [g, Function.comp_def] using
      ((hgrad_x.differentiable (by norm_num) (x t)).hasFDerivAt.comp_hasDerivAt t
        (hx_at t))
  have hr_at (t : ℝ) : HasDerivAt r
      (deriv (deriv x) t + β • ((fderiv ℝ (gradient Φ) (x t)) (v t))) t := by
    simpa [r] using (hv_at t).add ((hg_at t).const_smul β)
  have hgrad_inner : ∀ y : H, 0 ≤ inner ℝ (gradient Φ y) y := by
    intro y
    have hs := convex_supporting_baillon_haddad Φ (gradient Φ) hconvex
      (fun w => (hΦC1.differentiable (by norm_num) w).hasGradientAt) y 0
    have hmy : Φ 0 ≤ Φ y := hzero y
    have h := (show Φ y + inner ℝ (gradient Φ y) (0 - y) ≤ Φ 0 from hs)
    rw [zero_sub, inner_neg_right] at h
    linarith
  have hsq_sqrt : (Real.sqrt (α * β)) ^ 2 = α * β := by
    exact Real.sq_sqrt (mul_nonneg hα.le hβ.le)
  have hlow_one : (1 - Real.sqrt (α * β)) ^ 2 ≤ (1 : ℝ) := by
    have hs : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
    have hsle : Real.sqrt (α * β) ≤ 1 := by
      nlinarith [hαβ, hsq_sqrt]
    nlinarith [sq_nonneg (Real.sqrt (α * β))]
  have hhigh_one : (1 : ℝ) ≤ (1 + Real.sqrt (α * β)) ^ 2 := by
    have hs : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (Real.sqrt (α * β))]
  obtain ⟨_, hEanti, _, _⟩ := henergy_x 1 hlow_one hhigh_one
  have hEineq : ∀ ⦃t T : ℝ⦄, 0 ≤ t → t ≤ T →
      Φ (x T) - Φ (x t) ≤ (1 / 2 : ℝ) * ‖r t‖ ^ 2 := by
    intro t T ht hT
    have h := hEanti (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr (ht.trans hT)) hT
    dsimp [dinForwardEnergy, r, v, g] at h ⊢
    nlinarith [sq_nonneg ‖r T‖]
  have hω_le : ∀ ⦃t T : ℝ⦄, 0 ≤ t → t ≤ T →
      -inner ℝ (g t) (x t + x T) ≤ (1 / 2 : ℝ) * ‖r t‖ ^ 2 := by
    intro t T ht hT
    have hs := convex_supporting_baillon_haddad Φ (gradient Φ) hconvex
      (fun w => (hΦC1.differentiable (by norm_num) w).hasGradientAt) (x t) (-x T)
    have he := heven (x T)
    have h := hEineq ht hT
    dsimp [g, r] at *
    rw [← he] at hs
    have hi : inner ℝ (gradient Φ (x t)) (-x T - x t) =
        -inner ℝ (gradient Φ (x t)) (x t + x T) := by
      rw [show -x T - x t = -(x t + x T) by module, inner_neg_right]
    rw [hi] at hs
    linarith
  let G : ℝ → ℝ → ℝ := fun T t => ‖x t‖ ^ 2 - ‖x T‖ ^ 2 -
    (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2
  let omega : ℝ → ℝ → ℝ := fun T t => -inner ℝ (g t) (x t + x T)
  let f : ℝ → ℝ := fun t => inner ℝ (r t) (v t)
  have hG_at (T t : ℝ) : HasDerivAt (G T)
      (inner ℝ (v t) (x t + x T)) t := by
    have h1 := (hx_at t).norm_sq
    have h2 := (hx_at t).sub_const (x T)
    have h3 := (h2.norm_sq.const_mul (1 / 2 : ℝ))
    have hh := (h1.sub (hasDerivAt_const t (‖x T‖ ^ 2))).sub h3
    convert hh using 1
    dsimp [G, v]
    rw [inner_add_right, inner_sub_left,
      real_inner_comm (deriv x t) (x t),
      real_inner_comm (deriv x t) (x T)]
    ring_nf
  have hω_at (T t : ℝ) : HasDerivAt (omega T)
      (-inner ℝ ((fderiv ℝ (gradient Φ) (x t)) (v t)) (x t + x T) -
        inner ℝ (g t) (v t)) t := by
    have hi := (hg_at t).inner ℝ ((hx_at t).add (hasDerivAt_const t (x T)))
    convert hi.neg using 1
    dsimp [omega]
    rw [inner_add_right]
    ring_nf
  have hG2_at (T t : ℝ) : HasDerivAt (deriv (G T))
      (inner ℝ (deriv (deriv x) t) (x t + x T) + ‖v t‖ ^ 2) t := by
    have hGeq : deriv (G T) = fun s => inner ℝ (v s) (x s + x T) := by
      funext s
      exact (hG_at T s).deriv
    rw [hGeq]
    have hi := (hv_at t).inner ℝ ((hx_at t).add (hasDerivAt_const t (x T)))
    convert hi using 1
    simp only [Pi.add_apply, add_zero, inner_add_right, real_inner_self_eq_norm_sq]
    ring_nf
  have hJ_at (T t : ℝ) : HasDerivAt (fun s => deriv (G T) s - β * omega T s)
      (inner ℝ (deriv (deriv x) t) (x t + x T) + ‖v t‖ ^ 2 +
        β * inner ℝ ((fderiv ℝ (gradient Φ) (x t)) (v t)) (x t + x T) +
        β * inner ℝ (g t) (v t)) t := by
    have h := (hG2_at T t).sub ((hω_at T t).const_mul β)
    (convert h using 1 ; ring)
  have hJ_ineq : ∀ ⦃T t : ℝ⦄, 0 < t → t ≤ T →
      deriv (fun s => deriv (G T) s - β * omega T s) t +
        α * (deriv (G T) t - β * omega T t) ≤
      (1 / 2 : ℝ) * ‖v t‖ ^ 2 + ‖r t‖ ^ 2 := by
    intro T t ht hT
    rw [(hJ_at T t).deriv]
    rw [(hG_at T t).deriv]
    have heq := hsol.2.2 t ht.le
    have heq' := congrArg (fun q : H => inner ℝ q (x t + x T)) heq
    dsimp [G, omega, v, g, r, f] at *
    simp only [inner_add_left, real_inner_smul_left] at heq'
    have heq0 : inner ℝ (0 : H) (x t + x T) = 0 := inner_zero_left _
    rw [heq0] at heq'
    have hω := hω_le ht.le hT
    have hcross : inner ℝ (r t) (v t) ≤
        (1 / 2 : ℝ) * ‖r t‖ ^ 2 + (1 / 2 : ℝ) * ‖v t‖ ^ 2 := by
      have hs := sq_nonneg (‖r t‖ - ‖v t‖)
      nlinarith [real_inner_le_norm (r t) (v t)]
    have hcross' : ‖v t‖ ^ 2 + β * inner ℝ (g t) (v t) ≤
        (1 / 2 : ℝ) * ‖r t‖ ^ 2 + (1 / 2 : ℝ) * ‖v t‖ ^ 2 := by
      simpa [r, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        add_comm, add_left_comm, add_assoc] using hcross
    have hc : 0 ≤ 1 - α * β := by linarith
    have hcle : 1 - α * β ≤ 1 := by nlinarith [mul_pos hα hβ]
    have hωscaled := mul_le_mul_of_nonneg_left hω hc
    have hωscaled' : (1 - α * β) * -inner ℝ (gradient Φ (x t))
        (x t + x T) ≤ (1 / 2 : ℝ) * ‖r t‖ ^ 2 := by
      calc
        _ ≤ (1 - α * β) * ((1 / 2 : ℝ) * ‖r t‖ ^ 2) := hωscaled
        _ ≤ (1 / 2 : ℝ) * ‖r t‖ ^ 2 := by
          nlinarith [sq_nonneg ‖r t‖]
    nlinarith [hcross', hωscaled', heq']
  let q : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖v t‖ ^ 2 + ‖r t‖ ^ 2
  have hvLp : MeasureTheory.MemLp v 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [v] using hpartii.2.1
  have hgLp : MeasureTheory.MemLp g 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [g] using hpartii.2.2.1
  have hrLp : MeasureTheory.MemLp r 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [r] using hvLp.add (hgLp.const_smul β)
  have hvSq : MeasureTheory.IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hvLp.aestronglyMeasurable).mp hvLp
  have hrSq : MeasureTheory.IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hrLp.aestronglyMeasurable).mp hrLp
  have hqInt : MeasureTheory.IntegrableOn q (Set.Ici (0 : ℝ)) := by
    simpa [q] using (hvSq.const_mul (1 / 2 : ℝ)).add hrSq
  have hvC1 : ContDiff ℝ 1 v := by
    have hxdata := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) x by simpa using hx)
    simpa [v] using hxdata.2.2
  have hgC1 : ContDiff ℝ 1 g := by
    simpa [g, Function.comp_def] using hgrad_x.comp (hx.of_le (by norm_num))
  have hrC1 : ContDiff ℝ 1 r := by
    simpa [r] using hvC1.add (hgC1.const_smul β)
  have hqCont : Continuous q := by
    have hvn : Continuous (fun t => ‖v t‖ ^ 2) :=
      (continuous_norm.comp hvC1.continuous).pow 2
    have hrn : Continuous (fun t => ‖r t‖ ^ 2) :=
      (continuous_norm.comp hrC1.continuous).pow 2
    simpa [q] using hvn.const_mul (1 / 2 : ℝ) |>.add hrn
  have causalConv : ∀ (gg : ℝ → ℝ) (gamma : ℝ), 0 < gamma →
      MeasureTheory.IntegrableOn gg (Set.Ici (0 : ℝ)) →
      MeasureTheory.IntegrableOn (fun t : ℝ =>
        ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |gg s|) (Set.Ici (0 : ℝ)) := by
    intro gg gamma hgamma hgg
    have hG : MeasureTheory.IntegrableOn (fun s => |gg s|) (Set.Ici (0 : ℝ)) := hgg.abs
    have hkernel : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp ((-gamma) * t))
        (Set.Ici (0 : ℝ)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_Ioi (by linarith) 0
    have hG' : MeasureTheory.IntegrableOn (fun s : ℝ => |gg s|) (Set.Ioi (0 : ℝ)) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mp hG
    have hkernel' : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp ((-gamma) * s))
        (Set.Ioi (0 : ℝ)) := (integrableOn_Ici_iff_integrableOn_Ioi).mp hkernel
    have hconv := integrable_posConvolution hG' hkernel' (ContinuousLinearMap.mul ℝ ℝ)
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    apply hconv.integrableOn.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [posConvolution]
    simp only [Set.indicator_of_mem ht]
    change (∫ s in 0..t, |gg s| * Real.exp ((-gamma) * (t - s))) = _
    simp [mul_comm]
  have hconvInt : MeasureTheory.IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-α * (theta - s)) * q s)
      (Set.Ici (0 : ℝ)) := by
    have h := causalConv q α hα hqInt
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [abs_of_nonneg (by dsimp [q]; positivity)]
  let Herror : ℝ → ℝ := fun T => ∫ theta in 1..T,
      ∫ s in 0..theta, Real.exp (-α * (theta - s)) * q s
  have hHerror : ∃ L : ℝ, Tendsto Herror atTop (nhds L) := by
    have hqIoi : MeasureTheory.IntegrableOn (fun theta : ℝ =>
        ∫ s in 0..theta, Real.exp (-α * (theta - s)) * q s) (Set.Ioi (1 : ℝ)) :=
      hconvInt.mono_set (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr (by norm_num)))
    let L : ℝ := ∫ theta in Set.Ioi (1 : ℝ),
        ∫ s in 0..theta, Real.exp (-α * (theta - s)) * q s
    refine ⟨L, ?_⟩
    simpa [Herror, L] using
      intervalIntegral_tendsto_integral_Ioi 1 hqIoi tendsto_id
  rcases hHerror with ⟨L, hHerror⟩
  have hGglobal : ∀ T : ℝ, ContDiff ℝ 2 (G T) := by
    intro T
    dsimp [G]
    exact ((hx.norm_sq ℝ).sub contDiff_const).sub
      (contDiff_const.mul ((hx.sub contDiff_const).norm_sq ℝ))
  have hGDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (G T) (Set.Ici (1 : ℝ)) := by
    intro T
    exact ((hGglobal T).of_le (by norm_num)).contDiffOn
  have hGDerivDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (deriv (G T)) (Set.Ici (1 : ℝ)) := by
    intro T
    have h := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) (G T) by simpa using hGglobal T)
    exact h.2.2.contDiffOn
  have hGDerivGlobal : ∀ T : ℝ, ContDiff ℝ 1 (deriv (G T)) := by
    intro T
    have h := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) (G T) by simpa using hGglobal T)
    exact h.2.2
  have homegaC1 : ∀ T : ℝ, ContDiff ℝ 1 (omega T) := by
    intro T
    dsimp [omega]
    exact (hgC1.inner ℝ ((hx.of_le (by norm_num)).add contDiff_const)).neg
  let J : ℝ → ℝ → ℝ := fun T t => deriv (G T) t - β * omega T t
  let K : ℝ → ℝ → ℝ := fun T t => ∫ s in 0..t, J T s
  have hJC1 : ∀ T : ℝ, ContDiff ℝ 1 (J T) := by
    intro T
    dsimp [J]
    exact (hGDerivGlobal T).sub ((homegaC1 T).const_smul β)
  have hK_at (T t : ℝ) : HasDerivAt (K T) (J T t) t := by
    dsimp [K]
    exact intervalIntegral.integral_hasDerivAt_right
      ((hJC1 T).continuous.intervalIntegrable 0 t)
      (hJC1 T).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      (hJC1 T).continuous.continuousAt
  have hKglobal : ∀ T : ℝ, ContDiff ℝ 2 (K T) := by
    intro T
    apply (contDiff_succ_iff_deriv (n := (1 : WithTop ℕ∞))).mpr
    refine ⟨fun t => (hK_at T t).differentiableAt, ?_, ?_⟩
    · intro h
      norm_num at h
    · have hderiv : deriv (K T) = J T := by
        funext t
        exact (hK_at T t).deriv
      rw [hderiv]
      exact hJC1 T
  have hKDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (K T) (Set.Ici (1 : ℝ)) := by
    intro T
    exact ((hKglobal T).of_le (by norm_num)).contDiffOn
  have hKDerivDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (deriv (K T)) (Set.Ici (1 : ℝ)) := by
    intro T
    have h := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) (K T) by simpa using hKglobal T)
    exact h.2.2.contDiffOn
  have hNestedInt : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      IntervalIntegrable (fun theta => ∫ s in (1 : ℝ)..theta,
        Real.exp (-α * (theta - s)) * q s) volume t T := by
    intro t T ht hT
    let F : ℝ → ℝ → ℝ := fun theta s =>
      Real.exp (-α * (theta - s)) * q s
    have hFcont : Continuous (Function.uncurry F) := by
      dsimp [F]
      fun_prop
    have hJcont : Continuous (fun theta : ℝ => ∫ s in (1 : ℝ)..theta, F theta s) := by
      simpa [F] using
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (a₀ := (1 : ℝ)) hFcont continuous_id)
    simpa [F] using hJcont.continuousOn.intervalIntegrable_of_Icc hT
  have hNestedLe : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (∫ theta in t..T, ∫ s in 1..theta,
        Real.exp (-α * (theta - s)) * q s) ≤ Herror T - Herror t := by
    intro t T ht hT
    have hT1 : 1 ≤ T := ht.trans hT
    have hpoint : ∀ theta ∈ Set.Icc t T,
        (∫ s in 1..theta, Real.exp (-α * (theta - s)) * q s) ≤
          ∫ s in 0..theta, Real.exp (-α * (theta - s)) * q s := by
      intro theta htheta
      let K : ℝ → ℝ := fun s => Real.exp (-α * (theta - s)) * q s
      have hKnonneg : ∀ s, 0 ≤ K s := by
        intro s
        exact mul_nonneg (Real.exp_pos _).le (by
          dsimp [q]
          positivity)
      have hKint01 : IntervalIntegrable K volume 0 1 := by
        have hKcont : Continuous K := by
          dsimp [K]
          fun_prop
        exact hKcont.continuousOn.intervalIntegrable_of_Icc (by norm_num)
      have hKint1 : IntervalIntegrable K volume 1 theta := by
        have hKcont : Continuous K := by
          dsimp [K]
          fun_prop
        exact hKcont.continuousOn.intervalIntegrable_of_Icc (le_trans ht htheta.1)
      have hadd := intervalIntegral.integral_add_adjacent_intervals hKint01 hKint1
      have hnonneg : 0 ≤ ∫ s in 0..1, K s :=
        intervalIntegral.integral_nonneg (by norm_num) (fun s hs => hKnonneg s)
      rw [← hadd]
      linarith
    have hleft := hNestedInt ht hT
    have hright := (hconvInt.mono_set (by
      rw [Set.uIcc_of_le hT]
      intro s hs
      exact le_trans (by linarith [ht]) hs.1)).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hT hleft hright
      (fun theta htheta => hpoint theta ⟨le_of_lt htheta.1, le_of_lt htheta.2⟩)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((hconvInt.mono_set (by
        rw [Set.uIcc_of_le ht]
        intro s hs
        exact le_trans (by norm_num) hs.1)).intervalIntegrable) hright
    dsimp [Herror]
    rw [show (∫ theta in 1..T, ∫ s in 0..theta,
        Real.exp (-α * (theta - s)) * q s) =
        (∫ theta in 1..t, ∫ s in 0..theta,
          Real.exp (-α * (theta - s)) * q s) +
          ∫ theta in t..T, ∫ s in 0..theta,
            Real.exp (-α * (theta - s)) * q s by exact hsplit.symm]
    linarith
  have hEndpoint : ∃ C : ℝ, 0 ≤ C ∧ ∀ T, 0 ≤ T → deriv (K T) 1 ≤ C := by
    rcases isBounded_iff_forall_norm_le.mp hx_bounded with ⟨R, hR⟩
    let R' : ℝ := max R 0
    let C : ℝ := ‖r 1‖ * (‖x 1‖ + R')
    have hR' : 0 ≤ R' := le_max_right _ _
    refine ⟨C, by positivity, ?_⟩
    intro T hT
    have hRT : ‖x T‖ ≤ R' := (hR _ ⟨T, hT, rfl⟩).trans (le_max_left _ _)
    have hi : |deriv (K T) 1| ≤ C := by
      rw [(hK_at T 1).deriv]
      dsimp [J]
      rw [(hG_at T 1).deriv]
      dsimp [omega]
      have hj : inner ℝ (v 1) (x 1 + x T) - β * -inner ℝ (g 1) (x 1 + x T) =
          inner ℝ (r 1) (x 1 + x T) := by
        dsimp [r]
        rw [inner_add_left, real_inner_smul_left]
        ring
      rw [hj]
      calc
        |inner ℝ (r 1) (x 1 + x T)| ≤ ‖r 1‖ * ‖x 1 + x T‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ ‖r 1‖ * (‖x 1‖ + ‖x T‖) := by gcongr; exact norm_add_le _ _
        _ ≤ C := by
          dsimp [C]
          gcongr
    exact (le_abs_self _).trans hi
  rcases hEndpoint with ⟨C, hCnonneg, hCtail⟩
  have hTwo : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2 ≤
        ‖x t‖ ^ 2 - ‖x T‖ ^ 2 +
          ((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
          (∫ theta in t..T, ∫ s in 1..theta,
            Real.exp (-α * (theta - s)) * q s) +
          (β / 2) * ∫ s in t..T, ‖r s‖ ^ 2 := by
    intro t T ht hT
    have hKFTC : K T T - K T t = ∫ s in t..T, J T s := by
      have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc
        ((hKDiff T).mono (by
          intro s hs
          exact ht.trans hs.1)) hT
      rw [show deriv (K T) = J T by
        funext s; exact (hK_at T s).deriv] at h
      exact h.symm
    have hGFTC : G T T - G T t = ∫ s in t..T, deriv (G T) s := by
      exact (intervalIntegral.integral_deriv_of_contDiffOn_Icc
        ((hGDiff T).mono (by
          intro s hs
          exact ht.trans hs.1)) hT).symm
    have homegaInt : IntervalIntegrable (omega T) volume t T :=
      (homegaC1 T).continuous.intervalIntegrable t T
    have hrInt : IntervalIntegrable (fun s => ‖r s‖ ^ 2) volume t T :=
      (continuous_norm.comp hrC1.continuous).pow 2 |>.intervalIntegrable t T
    have homegaBound : β * (∫ s in t..T, omega T s) ≤
        (β / 2) * ∫ s in t..T, ‖r s‖ ^ 2 := by
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hT (homegaInt.const_mul β)
        (hrInt.const_mul (β / 2))
        (fun s hs => by
          have hs0 : 0 ≤ s := by linarith [hs.1]
          have hh := hω_le hs0 (le_of_lt hs.2)
          dsimp [omega, r]
          nlinarith [hh])
      simpa only [intervalIntegral.integral_const_mul] using hmono
    have hderivRel : ∀ s ∈ Set.uIoc t T,
        deriv (G T) s = deriv (K T) s + β * omega T s := by
      intro s hs
      rw [(hK_at T s).deriv]
      dsimp [J]
      ring
    have hKInt : IntervalIntegrable (deriv (K T)) volume t T :=
      (hKDerivDiff T).continuousOn.mono (by
        intro s hs
        exact ht.trans hs.1) |>.intervalIntegrable_of_Icc hT
    have hsumInt : IntervalIntegrable (fun s => deriv (K T) s + β * omega T s) volume t T :=
      hKInt.add (homegaInt.const_mul β)
    have hrel : G T T - G T t = (K T T - K T t) +
        β * ∫ s in t..T, omega T s := by
      have hJInt : IntervalIntegrable (J T) volume t T :=
        (hJC1 T).continuous.intervalIntegrable t T
      have hsumInt' : IntervalIntegrable (fun s => J T s + β * omega T s) volume t T :=
        hJInt.add (homegaInt.const_mul β)
      calc
        G T T - G T t = ∫ s in t..T, deriv (G T) s := hGFTC
        _ = ∫ s in t..T, (J T s + β * omega T s) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with s hs
          dsimp [J]
          ring
        _ = (∫ s in t..T, J T s) + ∫ s in t..T, β * omega T s :=
          intervalIntegral.integral_add hJInt (homegaInt.const_mul β)
        _ = (K T T - K T t) + β * ∫ s in t..T, omega T s := by
          rw [hKFTC, intervalIntegral.integral_const_mul]
    have hbase := Alvarez2000.damped_two_time_integral_bound
      (g := K T) (q := q) α 1 t T (hKDiff T) (hKDerivDiff T)
      (hqCont.continuousOn.mono (Set.Icc_subset_Ici_self)) (hNestedInt ht hT)
      hα ht hT (fun s hs => by
        have hs0 : 0 < s := by linarith [hs.1]
        have hh := hJ_ineq (T := T) (t := s) hs0 (le_of_lt hs.2)
        have hhJ : deriv (J T) s + α * J T s ≤ q s := by
          simpa [J, q] using hh
        have hKderiv : deriv (deriv (K T)) s = deriv (J T) s := by
          rw [show deriv (K T) = J T by
            funext u; exact (hK_at T u).deriv]
        rw [hKderiv, show deriv (K T) s = J T s by
          exact (hK_at T s).deriv]
        exact hhJ)
    have hG_T : G T T = 0 := by simp [G]
    rw [hG_T] at hrel
    have hsum : -G T t ≤
        ((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
          (∫ theta in t..T, ∫ s in 1..theta, Real.exp (-α * (theta - s)) * q s) +
          β * ∫ s in t..T, omega T s := by
      have hrel' : -G T t = K T T - K T t + β * ∫ s in t..T, omega T s := by
        simpa using hrel
      calc
        -G T t = K T T - K T t + β * ∫ s in t..T, omega T s := hrel'
        _ ≤
            (((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
              (∫ theta in t..T, ∫ s in 1..theta,
                Real.exp (-α * (theta - s)) * q s)) +
              β * ∫ s in t..T, omega T s := by
          have hadd := add_le_add_left hbase (β * ∫ s in t..T, omega T s)
          exact hadd
    dsimp [G] at hsum ⊢
    have hsum' : (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2 ≤
        (‖x t‖ ^ 2 - ‖x T‖ ^ 2) +
          (((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
            (∫ theta in t..T, ∫ s in 1..theta,
              Real.exp (-α * (theta - s)) * q s)) +
          β * ∫ s in t..T, omega T s := by
      have hid : (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2 =
          (‖x t‖ ^ 2 - ‖x T‖ ^ 2) +
            (-(‖x t‖ ^ 2 - ‖x T‖ ^ 2 - (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2)) := by
        ring
      rw [hid]
      have hadd := add_le_add_right hsum (‖x t‖ ^ 2 - ‖x T‖ ^ 2)
      (convert hadd using 1 ; ring)
    calc
      (1 / 2 : ℝ) * ‖x t - x T‖ ^ 2 ≤
          (‖x t‖ ^ 2 - ‖x T‖ ^ 2) +
            (((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
              (∫ theta in t..T, ∫ s in 1..theta,
                Real.exp (-α * (theta - s)) * q s)) +
            β * ∫ s in t..T, omega T s := hsum'
      _ ≤ ‖x t‖ ^ 2 - ‖x T‖ ^ 2 +
            ((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
            (∫ theta in t..T, ∫ s in 1..theta,
              Real.exp (-α * (theta - s)) * q s) +
            (β / 2) * ∫ s in t..T, ‖r s‖ ^ 2 := by
        have hb := add_le_add_right homegaBound
          (‖x t‖ ^ 2 - ‖x T‖ ^ 2 +
            (((Real.exp (-α * (t - 1)) - Real.exp (-α * (T - 1))) / α) * deriv (K T) 1 +
              (∫ theta in t..T, ∫ s in 1..theta,
                Real.exp (-α * (theta - s)) * q s)))
        (convert hb using 1 ; ring_nf)
  let Rerror : ℝ → ℝ := fun T => (β / 2) * ∫ s in 1..T, ‖r s‖ ^ 2
  have hRerror : ∃ Rlim : ℝ, Tendsto Rerror atTop (nhds Rlim) := by
    have hrIoi : MeasureTheory.IntegrableOn (fun s : ℝ => ‖r s‖ ^ 2) (Set.Ioi (1 : ℝ)) :=
      hrSq.mono_set (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr (by norm_num)))
    let Rlim : ℝ := (β / 2) * ∫ s in Set.Ioi (1 : ℝ), ‖r s‖ ^ 2
    refine ⟨Rlim, ?_⟩
    simpa [Rerror, Rlim] using
      (tendsto_const_nhds.mul (intervalIntegral_tendsto_integral_Ioi 1 hrIoi tendsto_id))
  rcases hRerror with ⟨Rlim, hRerror⟩
  have hSimpleLe : ∀ {s t : ℝ}, 1 ≤ s → s ≤ t →
      (β / 2) * ∫ u in s..t, ‖r u‖ ^ 2 ≤ Rerror t - Rerror s := by
    intro s t hs hst
    have hI1 : IntervalIntegrable (fun u : ℝ => ‖r u‖ ^ 2) volume 1 s :=
      (continuous_norm.comp hrC1.continuous).pow 2 |>.intervalIntegrable 1 s
    have hIst : IntervalIntegrable (fun u : ℝ => ‖r u‖ ^ 2) volume s t :=
      (continuous_norm.comp hrC1.continuous).pow 2 |>.intervalIntegrable s t
    have hIt : IntervalIntegrable (fun u : ℝ => ‖r u‖ ^ 2) volume 1 t :=
      (continuous_norm.comp hrC1.continuous).pow 2 |>.intervalIntegrable 1 t
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hIst
    have hnonneg : 0 ≤ (β / 2) * ∫ u in 1..s, ‖r u‖ ^ 2 := by
      exact mul_nonneg (div_nonneg hβ.le (by norm_num))
        (intervalIntegral.integral_nonneg hs (fun u hu => sq_nonneg (‖r u‖)))
    dsimp [Rerror]
    rw [← hsplit]
    ring_nf
    linarith
  rcases hnormsq with ⟨lNorm, hNormsq⟩
  have hUniform : ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ s t : ℝ,
      N ≤ s → N ≤ t → dist (x s) (x t) < ε := by
    intro ε hε
    let δ : ℝ := ε ^ 2 / 16
    have hδ : 0 < δ := by dsimp [δ]; positivity
    rcases Metric.tendsto_atTop.1 hNormsq δ hδ with ⟨Nnorm, hNnorm⟩
    rcases Metric.tendsto_atTop.1 hHerror δ hδ with ⟨Nerr, hNerr⟩
    rcases Metric.tendsto_atTop.1 hRerror δ hδ with ⟨NRerr, hNRerr⟩
    have hexp0 : Tendsto (fun r : ℝ => Real.exp (-α * (r - 1))) atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hshift : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
      convert (tendsto_id.const_mul_atTop_of_neg
        (by linarith : -α < 0)).comp hshift using 1
    have hexpC : Tendsto (fun r : ℝ => (C / α) * Real.exp (-α * (r - 1))) atTop (nhds 0) := by
      simpa using hexp0.const_mul (C / α)
    rcases Metric.tendsto_atTop.1 hexpC δ hδ with ⟨Nexp, hNexp⟩
    let N : ℝ := max 1 (max Nnorm (max Nerr (max NRerr Nexp)))
    have hN1 : 1 ≤ N := le_max_left _ _
    have hNnorm_le : Nnorm ≤ N := by
      calc
        Nnorm ≤ max Nnorm (max Nerr (max NRerr Nexp)) := le_max_left _ _
        _ ≤ N := le_max_right _ _
    have hNerr_le : Nerr ≤ N := by
      calc
        Nerr ≤ max Nerr (max NRerr Nexp) := le_max_left _ _
        _ ≤ max Nnorm (max Nerr (max NRerr Nexp)) := le_max_right _ _
        _ ≤ N := le_max_right _ _
    have hNRerr_le : NRerr ≤ N := by
      calc
        NRerr ≤ max NRerr Nexp := le_max_left _ _
        _ ≤ max Nerr (max NRerr Nexp) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max NRerr Nexp)) := le_max_right _ _
        _ ≤ N := le_max_right _ _
    have hNexp_le : Nexp ≤ N := by
      calc
        Nexp ≤ max NRerr Nexp := le_max_right _ _
        _ ≤ max Nerr (max NRerr Nexp) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max NRerr Nexp)) := le_max_right _ _
        _ ≤ N := le_max_right _ _
    refine ⟨N, ?_⟩
    have hordered : ∀ {s t : ℝ}, N ≤ s → N ≤ t → s ≤ t → dist (x s) (x t) < ε := by
      intro s t hs ht hst
      have h1s : 1 ≤ s := hN1.trans hs
      have h1t : 1 ≤ t := hN1.trans ht
      have hnorm_s : |‖x s‖ ^ 2 - lNorm| < δ := by
        simpa [Real.dist_eq] using hNnorm s (hNnorm_le.trans hs)
      have hnorm_t : |‖x t‖ ^ 2 - lNorm| < δ := by
        simpa [Real.dist_eq] using hNnorm t (hNnorm_le.trans ht)
      have hnorm_diff : ‖x s‖ ^ 2 - ‖x t‖ ^ 2 < 2 * δ := by
        have htri : |‖x s‖ ^ 2 - ‖x t‖ ^ 2| ≤
            |‖x s‖ ^ 2 - lNorm| + |‖x t‖ ^ 2 - lNorm| := by
          simpa [abs_sub_comm] using
            (abs_sub_le (‖x s‖ ^ 2) lNorm (‖x t‖ ^ 2))
        linarith [le_abs_self (‖x s‖ ^ 2 - ‖x t‖ ^ 2)]
      have herr_s : |Herror s - L| < δ := by simpa [Real.dist_eq] using hNerr s (hNerr_le.trans hs)
      have herr_t : |Herror t - L| < δ := by simpa [Real.dist_eq] using hNerr t (hNerr_le.trans ht)
      have herr_diff : Herror t - Herror s < 2 * δ := by
        have htri : |Herror t - Herror s| ≤ |Herror t - L| + |Herror s - L| := by
          have h := abs_sub_le (Herror t) L (Herror s)
          rw [abs_sub_comm L (Herror s)] at h
          exact h
        linarith [le_abs_self (Herror t - Herror s)]
      have hRerr_s : |Rerror s - Rlim| < δ := by
        simpa [Real.dist_eq] using hNRerr s (hNRerr_le.trans hs)
      have hRerr_t : |Rerror t - Rlim| < δ := by
        simpa [Real.dist_eq] using hNRerr t (hNRerr_le.trans ht)
      have hRerr_diff : Rerror t - Rerror s < 2 * δ := by
        have htri : |Rerror t - Rerror s| ≤ |Rerror t - Rlim| + |Rerror s - Rlim| := by
          have h := abs_sub_le (Rerror t) Rlim (Rerror s)
          rw [abs_sub_comm Rlim (Rerror s)] at h
          exact h
        linarith [le_abs_self (Rerror t - Rerror s)]
      have hcoef_nonneg : 0 ≤
          (Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α := by
        apply div_nonneg _ (le_of_lt hα)
        apply sub_nonneg.mpr
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (le_of_lt hα) (sub_nonneg.mpr hst)]
      have hend : ((Real.exp (-α * (s - 1)) -
        Real.exp (-α * (t - 1))) / α) * deriv (K t) 1 < δ := by
        have h0t : 0 ≤ t := le_trans (by norm_num) (hN1.trans ht)
        have hle : deriv (K t) 1 ≤ C := hCtail t h0t
        have h0 : ((Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α) * deriv (K t) 1 ≤
            ((Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α) * C :=
          mul_le_mul_of_nonneg_left hle hcoef_nonneg
        have hcoefle : ((Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α) * C ≤
            (C / α) * Real.exp (-α * (s - 1)) := by
          have he : 0 ≤ Real.exp (-α * (t - 1)) := (Real.exp_pos _).le
          have hc : (Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α ≤
            Real.exp (-α * (s - 1)) / α := div_le_div_of_nonneg_right
            (sub_le_self _ he) (le_of_lt hα)
          calc
            _ ≤ (Real.exp (-α * (s - 1)) / α) * C := mul_le_mul_of_nonneg_right hc hCnonneg
            _ = _ := by ring
        exact lt_of_le_of_lt (h0.trans hcoefle) (by
          have h := hNexp s (hNexp_le.trans hs)
          have hn : 0 ≤ (C / α) * Real.exp (-α * (s - 1)) := by positivity
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hn] at h
          simpa [abs_of_nonneg hCnonneg, abs_of_pos hα] using h)
      have hnest := hNestedLe h1s hst
      have hsimple := hSimpleLe h1s hst
      have hbound : ‖x s‖ ^ 2 - ‖x t‖ ^ 2 +
          ((Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α) * deriv (K t) 1 +
          (∫ theta in s..t, ∫ u in 1..theta, Real.exp (-α * (theta - u)) * q u) +
          (β / 2) * ∫ u in s..t, ‖r u‖ ^ 2 < ε ^ 2 / 2 := by
        have hsum : ‖x s‖ ^ 2 - ‖x t‖ ^ 2 +
            ((Real.exp (-α * (s - 1)) - Real.exp (-α * (t - 1))) / α) * deriv (K t) 1 +
            (∫ theta in s..t, ∫ u in 1..theta,
              Real.exp (-α * (theta - u)) * q u) +
            (β / 2) * ∫ u in s..t, ‖r u‖ ^ 2 < 7 * δ := by
          linarith [hnorm_diff, hend, hnest, herr_diff, hsimple, hRerr_diff]
        calc
          _ < 7 * δ := hsum
          _ = 7 * (ε ^ 2 / 16) := by rfl
          _ < ε ^ 2 / 2 := by nlinarith [sq_pos_of_pos hε]
      have hsq := hTwo h1s hst
      have hsq' : (1 / 2 : ℝ) * ‖x s - x t‖ ^ 2 < ε ^ 2 / 2 := lt_of_le_of_lt hsq hbound
      have hsqnorm : ‖x s - x t‖ ^ 2 < ε ^ 2 := by linarith
      have hnorm_lt : ‖x s - x t‖ < ε := by
        simpa [abs_of_nonneg (norm_nonneg _)] using abs_lt_of_sq_lt_sq hsqnorm (le_of_lt hε)
      simpa [dist_eq_norm] using hnorm_lt
    intro s t hs ht
    rcases le_total s t with hst | hts
    · exact hordered hs ht hst
    · simpa [dist_comm] using hordered ht hs hts
  obtain ⟨w, hstrong⟩ : ∃ w : H, Tendsto x atTop (nhds w) := by
    apply cauchy_map_iff_exists_tendsto.mp
    rw [Metric.cauchy_iff]
    refine ⟨by infer_instance, ?_⟩
    intro ε hε
    rcases hUniform ε hε with ⟨N, hN⟩
    refine ⟨x '' Set.Ici N, Filter.image_mem_map (eventually_ge_atTop N), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simpa [dist_eq_norm] using hN s t hs ht
  have hstrongWeak : Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop
      (nhds (toWeakSpace ℝ H w)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto w).comp hstrong
  have hw : w = z :=
    (toWeakSpace ℝ H).injective (tendsto_nhds_unique hstrongWeak hzweak)
  subst w
  exact ⟨z, hzmin, hstrong⟩
```

## Proof explanation
The proof proceeds by first obtaining weak convergence from the cited Alvarez convergence theorem, then proving that the trajectory is actually Cauchy in norm, and finally identifying the strong limit with the weak limit.

First, the proof applies `din_weakly_converges_to_argmin` to $\Phi,\alpha,\beta,x$. The hypotheses match: `hΦ`, `hx`, `hconvex`, `hmin`, and `hsol`. That theorem states two things. First, for every minimizer $z$, the distance $\|x(t)-z\|$ converges to some real number. Second, there exists a minimizer $z$ such that $x(t)$ converges weakly to $z$, expressed through the weak-space embedding. The proof unpacks this as `hweak`, obtaining `hdist` for distances and a triple $z$, $hzmin$, $hzweak$. Thus $z\in\mathrm{argminSet}(\Phi)$ and

$$
\mathrm{toWeakSpace}(x(t))\to \mathrm{toWeakSpace}(z)
$$

as $t\to\infty$. The proof also uses the same distance-convergence statement later, for the particular minimizer $0$.

Next, the proof shows $0\in\mathrm{argminSet}(\Phi)$. For arbitrary $y$, convexity gives

$$
\Phi\left(\frac12 y+\frac12(-y)\right)
\le \frac12\Phi(y)+\frac12\Phi(-y).
$$

The left argument is $0$, and evenness gives $\Phi(-y)=\Phi(y)$. Therefore

$$
\Phi(0)\le \frac12\Phi(y)+\frac12\Phi(y)=\Phi(y).
$$

Since $y$ was arbitrary, $0$ is a global minimizer. In the Lean proof, `intro y` introduces the arbitrary $y$; `hconvex.2` supplies the convexity inequality; `module` proves the midpoint identity; `rw` rewrites the midpoint as $0$ and replaces $\Phi(-y)$ by $\Phi(y)$; `simpa [smul_eq_mul]` converts scalar multiplication of real numbers into multiplication; and `nlinarith` finishes the inequality.

The proof then extracts positivity of the damping parameters:

$$
\alpha>0,\qquad \beta>0
$$

from `hsol.1` and `hsol.2.1`. It also records that $\alpha\beta+1>0$ by `positivity`.

Regularity of $\Phi$ is then used. From `hΦ.twice_continuously_differentiable`, the proof obtains that $\Phi$ is $C^2$, and hence $C^1$. For every $y\in H$, the derivative of $\Phi$ at $y$ is the continuous linear functional

$$
v\mapsto \langle \nabla\Phi(y),v\rangle.
$$

This is the content of `hgradF`, obtained from the differentiability of $\Phi$ and the fact that a gradient gives the Frechet derivative.

The proof next applies `din_forward_internal`. This theorem constructs a forward solution $x_g,v_g,\mathrm{acc}_g$ with prescribed initial position $x(0)$ and initial velocity $x'(0)$. It also states uniqueness among $C^2$ trajectories of the same system with the same initial data, monotonicity of the forward energy for suitable parameters, $L^2$-integrability of the velocity and gradient, convergence of $\Phi(x_g(t))$, convergence of the residual $v_g+\beta\nabla\Phi(x_g)$ to $0$, and several boundedness implications. The proof uses uniqueness by applying `huniq` to the given trajectory $x$. Since $x(0)=x(0)$ and $x'(0)=x'(0)$, and since $x$ is a $C^2$ trajectory, uniqueness gives

$$
x_g(t)=x(t),\qquad v_g(t)=x'(t)
$$

for every $t\ge 0$. Consequently, the convergence of $\Phi(x_g(t))$ and of the residual for $x_g$ transfer to $x$. The proof formalizes this transfer using `filter_upwards`, because the equality holds eventually, namely for all $t\ge 0$.

The proof then shows that $x$ is bounded on $[0,\infty)$. Since $0$ is a minimizer, `hdist` gives convergence of $\|x(t)\|$ to some $d_0$. Hence $\|x(t)\|^2\to d_0^2$. Using the definition of convergence with $\epsilon=1$, for all sufficiently large $t$ one has

$$
\|x(t)\|\le |d_0|+1.
$$

On the compact interval $[0,T_0]$, the continuous image $x([0,T_0])$ is compact and therefore bounded. Combining this with the tail estimate gives that

$$
x([0,\infty))
$$

is bounded. This is `hx_bounded`.

With boundedness of $x$ in hand, the proof applies `din_global_properties_part_iii`. That theorem says that if a $C^2$ trajectory of the system has bounded position on $[0,\infty)$, then the velocity, acceleration, gradient, and Hessian along the trajectory are bounded, and moreover the velocity, acceleration, and gradient tend to $0$ as $t\to\infty$. The proof records these consequences as `hvbound`, `haccbound`, `hgradbound`, `hhessbound`, `hvlim`, `hacclim`, and `hgradlim`. The later estimates mainly use the boundedness of $x$ itself and the energy and $L^2$ properties obtained next.

The proof then applies `din_global_properties_part_ii`. This theorem gives monotonicity of the forward energy

$$
E_\ell(t)=\ell\Phi(x(t))+\frac12\|x'(t)+\beta\nabla\Phi(x(t))\|^2
$$

for $\ell$ in the interval

$$
(1-\sqrt{\alpha\beta})^2\le \ell\le (1+\sqrt{\alpha\beta})^2,
$$

as well as $L^2$-integrability of $x'$ and $\nabla\Phi(x(t))$, convergence of $\Phi(x(t))$, and convergence of the residual $x'(t)+\beta\nabla\Phi(x(t))$ to $0$.

The proof defines

$$
v(t)=x'(t),\qquad g(t)=\nabla\Phi(x(t)),\qquad r(t)=v(t)+\beta g(t).
$$

Thus $r(t)=x'(t)+\beta\nabla\Phi(x(t))$ is the residual. The derivative facts are:

$$
v'(t)=x''(t),
$$

$$
g'(t)=\nabla^2\Phi(x(t))v(t),
$$

and therefore

$$
r'(t)=x''(t)+\beta\nabla^2\Phi(x(t))v(t).
$$

These are obtained by the chain rule, using the regularity of $x$ and of $\nabla\Phi$.

The proof also uses the convex supporting inequality `convex_supporting_baillon_haddad`. For a convex function $f$ with gradient field $\nabla f$, it states that for all $z,u$,

$$
f(z)+\langle \nabla f(z),u-z\rangle\le f(u).
$$

Applying this to $\Phi$, $z=y$, and $u=0$ gives

$$
\Phi(y)+\langle \nabla\Phi(y),-y\rangle\le \Phi(0).
$$

Since $\Phi(0)\le \Phi(y)$, it follows that

$$
\langle \nabla\Phi(y),y\rangle\ge 0.
$$

This is `hgrad_inner`.

Next the proof uses the bound $\alpha\beta\le 1$ to verify that $\ell=1$ lies in the admissible energy interval. Indeed,

$$
(1-\sqrt{\alpha\beta})^2\le 1,\qquad 1\le (1+\sqrt{\alpha\beta})^2.
$$

Therefore the forward energy with $\ell=1$,

$$
E_1(t)=\Phi(x(t))+\frac12\|r(t)\|^2,
$$

is nonincreasing on $[0,\infty)$. From this monotonicity, for $0\le t\le T$,

$$
E_1(T)\le E_1(t),
$$

so

$$
\Phi(x(T))+\frac12\|r(T)\|^2
\le \Phi(x(t))+\frac12\|r(t)\|^2.
$$

Dropping the nonnegative term $\frac12\|r(T)\|^2$ gives

$$
\Phi(x(T))-\Phi(x(t))\le \frac12\|r(t)\|^2.
$$

This is `hEineq`.

A second supporting inequality is then applied, this time with $z=x(t)$ and $u=-x(T)$:

$$
\Phi(x(t))+\langle g(t),-x(T)-x(t)\rangle\le \Phi(-x(T)).
$$

Using evenness $\Phi(-x(T))=\Phi(x(T))$, this becomes

$$
\Phi(x(t))-\langle g(t),x(t)+x(T)\rangle\le \Phi(x(T)).
$$

Therefore

$$
-\langle g(t),x(t)+x(T)\rangle
\le \Phi(x(T))-\Phi(x(t)).
$$

Combining with `hEineq` yields

$$
-\langle g(t),x(t)+x(T)\rangle\le \frac12\|r(t)\|^2.
$$

This is `hω_le`.

The proof now defines functions used to encode the second-order identity:

$$
G_T(t)=\|x(t)\|^2-\|x(T)\|^2-\frac12\|x(t)-x(T)\|^2,
$$

$$
\omega_T(t)=-\langle g(t),x(t)+x(T)\rangle.
$$

The derivative computations are:

$$
G_T'(t)=\langle v(t),x(t)+x(T)\rangle,
$$

$$
\omega_T'(t)
=-\langle \nabla^2\Phi(x(t))v(t),x(t)+x(T)\rangle
-\langle g(t),v(t)\rangle.
$$

Consequently,

$$
G_T''(t)=\langle x''(t),x(t)+x(T)\rangle+\|v(t)\|^2.
$$

If

$$
J_T(t)=G_T'(t)-\beta\omega_T(t),
$$

then

$$
J_T'(t)
=\langle x''(t),x(t)+x(T)\rangle+\|v(t)\|^2
+\beta\langle \nabla^2\Phi(x(t))v(t),x(t)+x(T)\rangle
+\beta\langle g(t),v(t)\rangle.
$$

At this point the proof uses the pointwise vector equation supplied by `hsol.2.2`. After pairing that equation with $x(t)+x(T)$, the acceleration, velocity, Hessian, and gradient terms cancel. Combining this cancellation with the formula for $J_T'(t)$ and with $J_T(t)=G_T'(t)-\beta\omega_T(t)$ gives

$$
J_T'(t)+\alpha J_T(t)
\le \frac12\|v(t)\|^2+\|r(t)\|^2.
$$

The proof obtains this by rewriting the derivatives, using the differential equation, using the inequality

$$
\langle r(t),v(t)\rangle
\le \frac12\|r(t)\|^2+\frac12\|v(t)\|^2,
$$

which follows from $2\langle r,v\rangle\le \|r\|^2+\|v\|^2$, and using the facts $0\le 1-\alpha\beta\le 1$ together with `hω_le`. The resulting differential inequality is `hJ_ineq`.

The proof then defines

$$
q(t)=\frac12\|v(t)\|^2+\|r(t)\|^2.
$$

From the $L^2$-integrability statements in `din_global_properties_part_ii`, the functions $v$ and $g$ are $L^2$ on $(0,\infty)$. Hence $r=v+\beta g$ is also $L^2$, and $\|v\|^2$ and $\|r\|^2$ are integrable on $[0,\infty)$. Therefore $q$ is integrable on $[0,\infty)$. The proof also verifies that $q$ is continuous. A causal convolution argument shows that the function

$$
\theta\mapsto \int_0^\theta e^{-\alpha(\theta-s)}q(s)\,ds
$$

is integrable on $[0,\infty)$. Therefore the accumulated error

$$
H_{\mathrm{error}}(T)
=\int_1^T\int_0^\theta e^{-\alpha(\theta-s)}q(s)\,ds\,d\theta
$$

has a finite limit as $T\to\infty$. This is proved using integrability of the exponential kernel and the standard fact that interval integrals over $[1,T]$ converge to the integral over $(1,\infty)$ as $T\to\infty$.

Next the proof defines

$$
K_T(t)=\int_0^t J_T(s)\,ds.
$$

Then $K_T'(t)=J_T(t)$ and $K_T''(t)=J_T'(t)$. In particular, $K_T$ is $C^2$. The proof verifies the regularity needed to apply the cited two-time integral bound to $K_T$.

The cited `damped_two_time_integral_bound` theorem has the following content. For functions $g,q:\mathbb R\to\mathbb R$, parameters $\gamma,a,t,T$, if $g$ is $C^1$ on $[a,\infty)$, $\mathrm{deriv}g$ is $C^1$ on $[a,\infty)$, $q$ is continuous on $[a,T]$, a certain nested integral is interval-integrable, $\gamma>0$, $a\le t\le T$, and

$$
g''(s)+\gamma g'(s)\le q(s)
$$

for all $s\in(a,T)$, then

$$
g(T)-g(t)
\le
\frac{e^{-\gamma(t-a)}-e^{-\gamma(T-a)}}{\gamma}g'(a)
+
\int_t^T\int_a^\theta e^{-\gamma(\theta-s)}q(s)\,ds\,d\theta.
$$

The proof applies this with $g=K_T$, $\gamma=\alpha$, $a=1$, and the same $q$. The required differential inequality is exactly

$$
K_T''(s)+\alpha K_T'(s)=J_T'(s)+\alpha J_T(s)\le q(s),
$$

which is `hJ_ineq`. The theorem then gives an upper bound for $K_T(T)-K_T(t)$.

The proof also shows that the inner integral from $1$ to $\theta$ is no larger than the inner integral from $0$ to $\theta$, because the integrand is nonnegative. Hence

$$
\int_t^T\int_1^\theta e^{-\alpha(\theta-s)}q(s)\,ds\,d\theta
\le H_{\mathrm{error}}(T)-H_{\mathrm{error}}(t).
$$

Also,

$$
K_T'(1)=\langle r(1),x(1)+x(T)\rangle.
$$

Because $x$ is bounded on $[0,\infty)$, there is a constant $C\ge 0$ such that

$$
K_T'(1)\le C
$$

for all $T\ge 0$. This is the endpoint estimate `hEndpoint`.

Relating $G_T$ and $K_T$ through $J_T=G_T'-\beta\omega_T$, and using the pointwise bound

$$
\int_t^T \omega_T(s)\,ds\le \frac12\int_t^T\|r(s)\|^2\,ds,
$$

the proof obtains the key estimate `hTwo`: for $1\le t\le T$,

$$
\frac12\|x(t)-x(T)\|^2
\le
\|x(t)\|^2-\|x(T)\|^2
+
\frac{e^{-\alpha(t-1)}-e^{-\alpha(T-1)}}{\alpha}K_T'(1)
+
\int_t^T\int_1^\theta e^{-\alpha(\theta-s)}q(s)\,ds\,d\theta
+
\frac{\beta}{2}\int_t^T\|r(s)\|^2\,ds.
$$

Next the proof defines

$$
R_{\mathrm{error}}(T)=\frac{\beta}{2}\int_1^T\|r(s)\|^2\,ds.
$$

Since $\|r\|^2$ is integrable on $(1,\infty)$, $R_{\mathrm{error}}(T)$ has a finite limit as $T\to\infty$. Moreover, for $1\le s\le t$,

$$
\frac{\beta}{2}\int_s^t\|r(u)\|^2\,du
\le R_{\mathrm{error}}(t)-R_{\mathrm{error}}(s),
$$

because the difference contains the integral over $[s,t]$ plus the nonnegative integral over $[1,s]$.

Using these convergence facts, the proof shows that $x$ is Cauchy at infinity. Given $\epsilon>0$, it sets

$$
\delta=\frac{\epsilon^2}{16}.
$$

It chooses thresholds so that, for all sufficiently large times,

$$
\bigl|\|x(t)\|^2-l_{\mathrm{norm}}\bigr|<\delta,
$$

$$
|H_{\mathrm{error}}(t)-L|<\delta,
$$

$$
|R_{\mathrm{error}}(t)-R_{\mathrm{lim}}|<\delta,
$$

and

$$
\frac{C}{\alpha}e^{-\alpha(t-1)}<\delta.
$$

For large $s\le t$, the four variable terms in `hTwo` are bounded by $2\delta,2\delta,2\delta$, and the endpoint term by $\delta$. Hence the right-hand side is less than

$$
7\delta=\frac{7\epsilon^2}{16}<\frac{\epsilon^2}{2}.
$$

Therefore

$$
\frac12\|x(s)-x(t)\|^2<\frac{\epsilon^2}{2},
$$

so

$$
\|x(s)-x(t)\|<\epsilon.
$$

Thus $x$ is uniformly Cauchy on the tail. The symmetric case $t\le s$ is handled by commuting the distance.

Finally, since $H$ is complete, the Cauchy property gives a strong limit $w\in H$ with

$$
x(t)\to w.
$$

The continuous embedding into the weak space then yields weak convergence

$$
\mathrm{toWeakSpace}(x(t))\to \mathrm{toWeakSpace}(w).
$$

But the weak convergence theorem already gave

$$
\mathrm{toWeakSpace}(x(t))\to \mathrm{toWeakSpace}(z).
$$

Weak limits are unique and $\mathrm{toWeakSpace}$ is injective, so $w=z$. The proof substitutes $w=z$ and concludes that

$$
x(t)\to z
$$

strongly, with $z\in\mathrm{argminSet}(\Phi)$.

Throughout the Lean proof, `intro` introduces an arbitrary variable when proving a universal statement, `rw` rewrites equalities, `simp` and `simpa` simplify expressions using known definitions and lemmas, `linarith` and `nlinarith` combine linear and nonlinear inequalities, `positivity` proves positivity goals, `filter_upwards` proves eventual equality, `obtain` and `rcases` destruct existential and conjunctive hypotheses, `calc` chains inequalities, `convert` changes a goal up to definitional or algebraic equality, and `subst` replaces a variable by an equal one.

