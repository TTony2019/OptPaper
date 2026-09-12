## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/prop_2.lean`

## Lean statement
```lean
theorem din_strong_convergence_of_interior_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
    (hΦ : AssumptionH H Φ)
    (hxreg : ContDiff ℝ 2 x)
    (hconvex : ConvexOn ℝ Set.univ Φ)
    (hmin : (Optimization.argminSet Φ).Nonempty)
    (hsol : IsDINTrajectory H Φ α β x)
    (hinterior : (interior (Optimization.argminSet Φ)).Nonempty) :
    ∃ z, z ∈ Optimization.argminSet Φ ∧ Tendsto x atTop (nhds z)
```

## Statement explanation
The theorem states that a second-order dissipative dynamical system with Hessian-driven damping converges strongly to a minimizer of its potential, provided the set of minimizers has nonempty interior.

The ambient space $H$ is a real Hilbert space: a complete real inner-product space. The potential is a function $\Phi:H\to \mathbb R$, and $x:\mathbb R\to H$ is a trajectory. The parameters are real numbers $\alpha,\beta$.

The hypotheses are as follows. The assumption `hΦ : AssumptionH H Φ` is an assumption package on $\Phi$; in the proof only two consequences of it are used: $\Phi$ is twice continuously differentiable, and $\Phi$ is bounded below. The trajectory satisfies `hxreg : ContDiff ℝ 2 x`, so $x$ is $C^2$. The potential is globally convex: `hconvex : ConvexOn ℝ Set.univ Φ`. Its set of global minimizers,

$$
\mathrm{argminSet}\Phi=\{p\in H:\forall y\in H,\ \Phi(p)\le \Phi(y)\},
$$

is nonempty: `hmin : (Optimization.argminSet Φ).Nonempty`. The trajectory is a D-IN trajectory: `hsol : IsDINTrajectory H Φ α β x`. From this assumption the proof extracts the positivity conditions $0<\alpha$ and $0<\beta$, and the second-order equation

$$
x''(t)
=-\Bigl(\alpha x'(t)+\beta\,D\nabla\Phi(x(t))\,x'(t)+\nabla\Phi(x(t))\Bigr)
$$

for every $t\ge 0$. Here $\nabla\Phi$ is the Lean `gradient Φ`, the Riesz representative of the Fréchet derivative $D\Phi$, so that

$$
\langle \nabla\Phi(y),v\rangle = D\Phi(y)(v)
$$

for all $y,v\in H$. Finally, the crucial extra hypothesis is

$$
\mathrm{interior}\bigl(\mathrm{argminSet}\Phi\bigr)\neq\varnothing.
$$

Thus there is a point $z_0$ and a radius $\rho>0$ such that the whole ball $B(z_0,\rho)$ consists of global minimizers of $\Phi$.

The conclusion is that there exists a global minimizer $z$ of $\Phi$ such that

$$
x(t)\to z
$$

in the strong topology of $H$, i.e. $\|x(t)-z\|\to0$ as $t\to\infty$. The theorem therefore upgrades the weak convergence obtained from the general theory to strong convergence, under the interior-minimizer hypothesis.

## Lean proof
```lean
by
  have hΦC1 : ContDiff ℝ 1 Φ :=
    hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hxC2 : ContDiff ℝ (1 + 1) x := by simpa using hxreg
  have hxdata := contDiff_succ_iff_deriv.mp hxC2
  have hvC1 : ContDiff ℝ 1 (deriv x) := by simpa using hxdata.2.2
  have hvdata := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (0 + 1) (deriv x) by simpa using hvC1)
  have hgrad_cont : Continuous (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by
          simpa using hΦ.twice_continuously_differentiable)).2.2
    have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
      simpa [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
    exact hgradC1.continuous
  have hgradDeriv : ∀ z, HasFDerivAt (gradient Φ)
      (fderiv ℝ (gradient Φ) z) z := by
    intro z
    have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
      have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
        exact (contDiff_succ_iff_fderiv.mp
          (show ContDiff ℝ (1 + 1) Φ by
            simpa using hΦ.twice_continuously_differentiable)).2.2
      simpa [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by
          simpa using hΦ.twice_continuously_differentiable)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradCompC1 : ContDiff ℝ 1 (fun t => gradient Φ (x t)) := by
    simpa [Function.comp_def] using hgradC1.comp (hxreg.of_le (by norm_num))
  have hglobal := din_forward_internal Φ hΦ α β hsol.1 hsol.2.1 (x 0) (deriv x 0)
  rcases hglobal with
    ⟨xg, vg, accg, hxg0, hvg0, hforward, huniq, henergy, hvL2, hgL2, hphil, hres,
      hbound, hderivg⟩
  -- The distance-limit part of Theorem 5.1 gives boundedness of the whole trajectory.
  have hweak := din_weakly_converges_to_argmin Φ α β x hΦ hxreg hconvex hmin hsol
  rcases hweak with ⟨hdist, _⟩
  have hmin_copy := hmin
  obtain ⟨z_bdd, hz_bdd⟩ := hmin_copy
  rcases hdist z_bdd hz_bdd with ⟨d₀, hd₀⟩
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hd₀) 1 zero_lt_one
  let T₀ : ℝ := max T 0
  have htail : ∀ t, T₀ ≤ t → ‖x t - z_bdd‖ ≤ |d₀| + 1 := by
    intro t ht
    have hdist' : dist (‖x t - z_bdd‖) d₀ < 1 := by
      simpa [Real.dist_eq] using hT t (le_trans (le_max_left T 0) ht)
    have habs : |‖x t - z_bdd‖ - d₀| < 1 := by simpa [Real.dist_eq] using hdist'
    have hle : ‖x t - z_bdd‖ - d₀ ≤ |‖x t - z_bdd‖ - d₀| := le_abs_self _
    have hnormd : ‖x t - z_bdd‖ ≤ d₀ + 1 := by nlinarith
    exact hnormd.trans (by linarith [le_abs_self d₀])
  have hxbounded : BoundedOnNonnegative x := by
    unfold BoundedOnNonnegative
    have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
      exact isCompact_Icc.image_of_continuousOn
        (hxreg.continuous.continuousOn.mono Set.Icc_subset_Ici_self)
    rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
    refine isBounded_iff_forall_norm_le.mpr
      ⟨max R₀ (|d₀| + 1 + ‖z_bdd‖), ?_⟩
    rintro q ⟨t, ht, rfl⟩
    by_cases hle : t ≤ T₀
    · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
    · have hge : T₀ ≤ t := le_of_not_ge hle
      have htri : ‖x t‖ ≤ ‖x t - z_bdd‖ + ‖z_bdd‖ := by
        calc
          ‖x t‖ = ‖(x t - z_bdd) + z_bdd‖ := by rw [sub_add_cancel]
          _ ≤ ‖x t - z_bdd‖ + ‖z_bdd‖ := norm_add_le _ _
      have htri' : ‖x t - z_bdd‖ + ‖z_bdd‖ ≤ (|d₀| + 1) + ‖z_bdd‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (htail t hge) ‖z_bdd‖)
      exact (htri.trans htri').trans (le_max_right _ _)
  have heq := huniq x (by rfl) (by rfl) hsol hxreg
  have hxgbounded : BoundedOnNonnegative xg := by
    apply hxbounded.subset
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    exact (heq t ht).1
  rcases hbound hxgbounded with
    ⟨hgrad_bdd, hv_bdd, hacc_bdd, hhess_bdd, hvelg, hacclimg, hgradg⟩
  obtain ⟨z₀, hz₀⟩ := hinterior
  have hz₀arg : z₀ ∈ Optimization.argminSet Φ := interior_subset hz₀
  have hgrad_at (y : H) : HasGradientAt Φ (gradient Φ y) y :=
    (hΦC1.differentiable (by norm_num) y).hasGradientAt
  have hsupport : ∀ y p : H,
      Φ y + inner ℝ (gradient Φ y) (p - y) ≤ Φ p := by
    intro y p
    exact convex_supporting_baillon_haddad Φ (gradient Φ) hconvex hgrad_at y p
  have hgrad_inner : ∀ y : H, 0 ≤ inner ℝ (gradient Φ y) (y - z₀) := by
    intro y
    have hs := hsupport y z₀
    have hm := hz₀arg y
    have hinner : inner ℝ (gradient Φ y) (z₀ - y) =
        -inner ℝ (gradient Φ y) (y - z₀) := by
      rw [inner_sub_right, inner_sub_right]
      ring
    rw [hinner] at hs
    linarith
  obtain ⟨ρ, hρ, hρball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz₀)
  have hgrad_lower : ∀ y : H,
      (ρ / 2) * ‖gradient Φ y‖ ≤ inner ℝ (gradient Φ y) (y - z₀) := by
    intro y
    by_cases hy : gradient Φ y = 0
    · simp [hy]
    let z' : H := z₀ + (ρ / 2) • (‖gradient Φ y‖⁻¹ • gradient Φ y)
    have hz'ball : z' ∈ Metric.ball z₀ ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖‖gradient Φ y‖⁻¹ • gradient Φ y‖ =
          ‖gradient Φ y‖⁻¹ * ‖gradient Φ y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hy))]
      have hinv : ‖gradient Φ y‖⁻¹ * ‖gradient Φ y‖ = 1 :=
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)
      calc
        ‖z' - z₀‖ = ‖(ρ / 2) • (‖gradient Φ y‖⁻¹ • gradient Φ y)‖ := by
          dsimp [z']
          rw [add_sub_cancel_left]
        _ = (ρ / 2) * ‖‖gradient Φ y‖⁻¹ • gradient Φ y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
        _ = ρ / 2 := by rw [hnorm, hinv, mul_one]
        _ < ρ := by linarith
    have hz'arg : z' ∈ Optimization.argminSet Φ := hρball hz'ball
    have hs := hsupport y z'
    have hm := hz'arg y
    have hinner_nonneg : 0 ≤ inner ℝ (gradient Φ y) (y - z') := by
      have hinner' : inner ℝ (gradient Φ y) (z' - y) =
          -inner ℝ (gradient Φ y) (y - z') := by
        rw [inner_sub_right, inner_sub_right]
        ring
      rw [hinner'] at hs
      linarith
    have hnorm : inner ℝ (gradient Φ y)
        (‖gradient Φ y‖⁻¹ • gradient Φ y) = ‖gradient Φ y‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.mpr hy]
    have hexpand : inner ℝ (gradient Φ y) (y - z') =
        inner ℝ (gradient Φ y) (y - z₀) - (ρ / 2) * ‖gradient Φ y‖ := by
      dsimp [z']
      rw [show y - (z₀ + (ρ / 2) • (‖gradient Φ y‖⁻¹ • gradient Φ y)) =
          (y - z₀) - (ρ / 2) • (‖gradient Φ y‖⁻¹ • gradient Φ y) by module]
      rw [inner_sub_right, real_inner_smul_right, hnorm]
    rw [hexpand] at hinner_nonneg
    linarith
  let v : ℝ → H := fun t => deriv x t
  let g : ℝ → H := fun t => gradient Φ (x t)
  let r : ℝ → H := fun t => v t + β • g t
  let u : ℝ → H := fun t => x t - z₀
  let ε : ℝ := min 1 (α / (4 * (β + 1)))
  let κ : ℝ := α * β + 1
  have hε : 0 < ε := by
    dsimp [ε]
    have hβ1 : 0 < β + 1 := by linarith [hsol.2.1]
    exact lt_min (by norm_num) (div_pos hsol.1 (by positivity : 0 < 4 * (β + 1)))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεfrac : ε ≤ α / (4 * (β + 1)) := min_le_right _ _
  have hκ : 0 < κ := by
    dsimp [κ]
    nlinarith [hsol.1, hsol.2.1]
  have hcoefv : 0 ≤ α - ε - ε * β / 2 := by
    have htmp : ε * (1 + β / 2) ≤ α := by
      have h1 : 1 + β / 2 ≤ β + 1 := by linarith [hsol.2.1]
      have hmul := mul_le_mul_of_nonneg_left h1 hε.le
      have hβ1 : 0 < β + 1 := by linarith [hsol.2.1]
      have hprod : ε * (β + 1) ≤ α / 4 := by
        calc
          ε * (β + 1) ≤ (α / (4 * (β + 1))) * (β + 1) :=
            mul_le_mul_of_nonneg_right hεfrac hβ1.le
          _ = α / 4 := by field_simp [ne_of_gt hβ1]
      nlinarith
    nlinarith
  have hcoefg : 0 ≤ β * (1 - ε / 2) := by
    have : 0 ≤ 1 - ε / 2 := by linarith
    exact mul_nonneg hsol.2.1.le this
  have hgrad_at_t (t : ℝ) : HasDerivAt g
      ((fderiv ℝ (gradient Φ) (x t)) (v t)) t := by
    dsimp [g, v]
    simpa [Function.comp_def] using
      (hgradDeriv (x t)).comp_hasDerivAt t ((hxdata.1 t).hasDerivAt)
  have hr_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt r (-α • v t - g t) t := by
    have hv_at : HasDerivAt v (deriv (deriv x) t) t := by
      simpa [v] using (hvdata.1 t).hasDerivAt
    have hraw := hv_at.add ((hgrad_at_t t).const_smul β)
    have heq_t := hsol.2.2 t ht
    convert hraw using 1
    dsimp [r, v, g]
    rw [show deriv (deriv x) t =
        -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
          gradient Φ (x t)) by
          exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using heq_t)]
    simp only [neg_smul]
    module
  have hu_at (t : ℝ) : HasDerivAt u (v t) t := by
    dsimp [u, v]
    simpa using ((hxdata.1 t).hasDerivAt.sub_const z₀)
  let E : ℝ → ℝ := fun t =>
    κ * Φ (x t) + (1 / 2) * ‖r t‖ ^ 2
  have hE_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt E
      (-α * ‖v t‖ ^ 2 - β * ‖g t‖ ^ 2) t := by
    have hp := (hgrad_at (x t)).hasFDerivAt.comp_hasDerivAt t
      ((hxdata.1 t).hasDerivAt)
    have hp' : HasDerivAt (fun s => Φ (x s)) (inner ℝ (g t) (v t)) t := by
      simpa [g, v, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hp
    have hk := ((hr_at t ht).norm_sq.const_mul (1 / 2 : ℝ))
    have he := (hp'.const_smul (α * β + 1)).add hk
    have hinner : inner ℝ (v t) (g t) = inner ℝ (g t) (v t) := real_inner_comm _ _
    convert he using 1
    dsimp [E, κ, r, v, g]
    simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq]
    simp [real_inner_comm]
    ring_nf
  let haux : ℝ → ℝ := fun t =>
    E t + ε * (α / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))
  have haux_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt haux
      (-(α - ε) * ‖v t‖ ^ 2 - β * ‖g t‖ ^ 2
        - ε * inner ℝ (g t) (u t) + ε * β * inner ℝ (g t) (v t)) t := by
    have hu_sq := (hu_at t).norm_sq.const_mul (α / 2)
    have hi := (hr_at t ht).inner ℝ (hu_at t)
    have hi' := (hu_sq.add hi).const_smul ε
    have he := hE_at t ht
    have he' := he.add hi'
    change HasDerivAt (fun t =>
      E t +
        ε * (α / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))) _ _
    convert he' using 1
    simp only [smul_eq_mul]
    have hi1 : inner ℝ (-α • v t - g t) (u t) =
        -(α * inner ℝ (v t) (u t)) - inner ℝ (g t) (u t) := by
      rw [inner_sub_left, inner_smul_left]
      norm_num
    have hi2 : inner ℝ (v t + β • g t) (v t) =
        ‖v t‖ ^ 2 + β * inner ℝ (g t) (v t) := by
      rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    rw [hi1, hi2]
    rw [real_inner_comm (u t) (v t)]
    ring_nf
  have haux_deriv_nonpos : ∀ t, 0 ≤ t → deriv haux t ≤ 0 := by
    intro t ht
    rw [(haux_at t ht).deriv]
    have hyoung : ε * β * inner ℝ (g t) (v t) ≤
        ε * β / 2 * (‖g t‖ ^ 2 + ‖v t‖ ^ 2) := by
      have hs := sq_nonneg (‖g t‖ - ‖v t‖)
      have hp : 0 ≤ ε * β := mul_nonneg hε.le hsol.2.1.le
      nlinarith [real_inner_le_norm (g t) (v t)]
    have hgu : 0 ≤ inner ℝ (g t) (u t) := by
      simpa [g, u] using hgrad_inner (x t)
    nlinarith [hcoefv, hcoefg, hyoung]
  have haux_cont : ContinuousOn haux (Set.Ici 0) := by
    intro t ht
    exact (haux_at t ht).continuousAt.continuousWithinAt
  have haux_diff : DifferentiableOn ℝ haux (interior (Set.Ici 0)) := by
    intro t ht
    have ht' : t ∈ Set.Ioi (0 : ℝ) := by simpa [interior_Ici] using ht
    exact (haux_at t (le_of_lt ht')).differentiableAt.differentiableWithinAt
  have haux_anti : AntitoneOn haux (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) haux_cont haux_diff
      (fun t ht => haux_deriv_nonpos t (le_of_lt (by simpa [interior_Ici] using ht)))
  have hE_lower : ∀ t, 0 ≤ t → κ * (Classical.choose hΦ.bounded_below) +
      (1 / 2) * ‖r t‖ ^ 2 ≤ E t := by
    intro t ht
    dsimp [E]
    have hm := Classical.choose_spec hΦ.bounded_below (x t)
    exact add_le_add (mul_le_mul_of_nonneg_left hm hκ.le) le_rfl
  have haux_lower : ∀ t, 0 ≤ t → κ * (Classical.choose hΦ.bounded_below) +
      ε * α / 4 * ‖u t‖ ^ 2 ≤ haux t := by
    intro t ht
    have hcross := real_inner_le_norm (-(r t)) (u t)
    rw [inner_neg_left, norm_neg] at hcross
    have hcross' : -‖r t‖ * ‖u t‖ ≤ inner ℝ (r t) (u t) := by linarith
    have hcross_scaled := mul_le_mul_of_nonneg_left hcross' hε.le
    have hs := sq_nonneg (‖r t‖ - ε * ‖u t‖)
    have hEm := hE_lower t ht
    have hαε : 0 ≤ α - 2 * ε := by
      have hαpos : 0 < α := hsol.1
      have hεα : ε ≤ α / 4 := by
        have hβ1 : 0 < β + 1 := by linarith [hsol.2.1]
        calc
          ε ≤ α / (4 * (β + 1)) := hεfrac
          _ ≤ α / 4 := by
            exact (div_le_div_of_nonneg_left (le_of_lt hαpos) (by norm_num)
              (by linarith [hsol.2.1]))
      linarith
    have hcoef : 0 ≤ ε * (α - 2 * ε) / 4 :=
      div_nonneg (mul_nonneg hε.le hαε) (by norm_num)
    have hcoefnu := mul_nonneg hcoef (sq_nonneg ‖u t‖)
    dsimp [haux]
    nlinarith
  let q : ℝ → ℝ := fun t => haux (max t 0)
  have hqanti : Antitone q := by
    intro s t hst
    exact haux_anti (le_max_right s 0) (le_max_right t 0)
      (max_le_max_right 0 hst)
  have hq_lower : BddBelow (Set.range q) := by
    refine ⟨κ * (Classical.choose hΦ.bounded_below), ?_⟩
    rintro y ⟨t, rfl⟩
    have hnon : 0 ≤ ε * α / 4 * ‖u (max t 0)‖ ^ 2 := by
      exact mul_nonneg (div_nonneg (mul_nonneg hε.le hsol.1.le) (by norm_num))
        (sq_nonneg _)
    exact (le_add_of_nonneg_right hnon).trans
      (haux_lower (max t 0) (le_max_right t 0))
  have haux_lim : ∃ l : ℝ, Tendsto haux atTop (nhds l) := by
    refine ⟨⨅ t, q t, ?_⟩
    apply (tendsto_atTop_ciInf hqanti hq_lower).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [q, max_eq_left ht]
  have haux_deriv_int :
      MeasureTheory.IntegrableOn (deriv haux) (Set.Ioi (0 : ℝ))
        MeasureTheory.volume := by
    rcases haux_lim with ⟨laux, hlaux⟩
    apply MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
    · intro t ht
      rw [(haux_at t ht).deriv]
      exact haux_at t ht
    · intro t ht
      exact haux_deriv_nonpos t (le_of_lt ht)
    · exact hlaux
  have hscalar_nonneg : ∀ t, 0 ≤ t →
      0 ≤ ε * inner ℝ (g t) (u t) := by
    intro t ht
    exact mul_nonneg hε.le (hgrad_inner (x t))
  have hscalar_le : ∀ t, 0 ≤ t →
      ε * inner ℝ (g t) (u t) ≤ -deriv haux t := by
    intro t ht
    rw [(haux_at t ht).deriv]
    have hyoung : ε * β * inner ℝ (g t) (v t) ≤
        ε * β / 2 * (‖g t‖ ^ 2 + ‖v t‖ ^ 2) := by
      have hs := sq_nonneg (‖g t‖ - ‖v t‖)
      have hp : 0 ≤ ε * β := mul_nonneg hε.le hsol.2.1.le
      nlinarith [real_inner_le_norm (g t) (v t)]
    have hgu : 0 ≤ inner ℝ (g t) (u t) := hgrad_inner (x t)
    nlinarith [hcoefv, hcoefg, hyoung]
  have hscalar_int :
      MeasureTheory.IntegrableOn (fun t => ε * inner ℝ (g t) (u t))
        (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by
    change MeasureTheory.Integrable (fun t => ε * inner ℝ (g t) (u t))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    have hneg : MeasureTheory.Integrable (fun t => -deriv haux t)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      exact haux_deriv_int.neg
    apply hneg.mono'
    · have hxc : Continuous x := hxreg.continuous
      have hgc : Continuous (fun t => g t) := by
        simpa [g] using hgrad_cont.comp hxc
      have huc : Continuous (fun t => u t) := by
        simpa [u] using hxc.sub continuous_const
      exact (continuous_const.mul (hgc.inner huc)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : 0 ≤ t := le_of_lt ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hscalar_nonneg t ht')]
      exact hscalar_le t ht'
  have hgrad_int :
      MeasureTheory.IntegrableOn (fun t => g t) (Set.Ioi (0 : ℝ))
        MeasureTheory.volume := by
    change MeasureTheory.Integrable (fun t => g t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    have hscaled := hscalar_int.integrable.const_mul (2 / (ε * ρ))
    apply hscaled.mono'
    · have hxc : Continuous x := hxreg.continuous
      exact (hgrad_cont.comp hxc).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have hlower := hgrad_lower (x t)
      have hinner := hgrad_inner (x t)
      have hpos : 0 < ε * ρ := mul_pos hε hρ
      dsimp [g, u] at hlower hinner ⊢
      calc
        ‖gradient Φ (x t)‖ = (2 / ρ) * (ρ / 2 * ‖gradient Φ (x t)‖) := by
          field_simp [ne_of_gt hρ]
        _ ≤ (2 / ρ) * inner ℝ (gradient Φ (x t)) (x t - z₀) := by
          exact mul_le_mul_of_nonneg_left hlower (by positivity)
        _ = 2 / (ε * ρ) * (ε * inner ℝ (gradient Φ (x t)) (x t - z₀)) := by
          field_simp [ne_of_gt hε, ne_of_gt hρ]
  have hvel_lim : Tendsto (deriv x) atTop (nhds 0) := by
    apply hvelg.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq t ht).2.symm
  have hgrad_lim : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
    apply hgradg.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [heq t ht |>.1]
  let I : H := ∫ s in Set.Ioi (0 : ℝ), gradient Φ (x s)
  have hI : Tendsto (fun t : ℝ => ∫ s in (0)..t, gradient Φ (x s)) atTop (nhds I) := by
    simpa [I] using MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      hgrad_int tendsto_id
  have hintegrated : ∀ t : ℝ, 0 ≤ t →
      deriv x t + α • x t + β • gradient Φ (x t) +
          ∫ s in (0)..t, gradient Φ (x s) =
        deriv x 0 + α • x 0 + β • gradient Φ (x 0) := by
    exact din_integrated_identity Φ α β x hΦ hsol hxreg
  let c : H := deriv x 0 + α • x 0 + β • gradient Φ (x 0)
  have hα : 0 < α := hsol.1
  have hαne : α ≠ 0 := ne_of_gt hα
  have hx_repr (t : ℝ) (ht : 0 ≤ t) :
      x t = α⁻¹ • (c - deriv x t - β • gradient Φ (x t) -
        ∫ s in (0)..t, gradient Φ (x s)) := by
    have hlin : α • x t = c - deriv x t - β • gradient Φ (x t) -
        ∫ s in (0)..t, gradient Φ (x s) := by
      have ht := hintegrated t ht
      rw [show c = deriv x 0 + α • x 0 + β • gradient Φ (x 0) by rfl]
      rw [← ht]
      module
    have hscaled := congrArg (fun q : H => α⁻¹ • q) hlin
    simpa [smul_smul, hαne, sub_eq_add_neg, one_smul] using hscaled
  have hrest : Tendsto
      (fun t : ℝ => c - deriv x t - β • gradient Φ (x t) -
        ∫ s in (0)..t, gradient Φ (x s)) atTop
      (nhds (c - 0 - β • 0 - I)) := by
    have hv : Tendsto (fun t : ℝ => deriv x t) atTop (nhds (0 : H)) := hvel_lim
    have hg : Tendsto (fun t : ℝ => β • gradient Φ (x t)) atTop (nhds (β • (0 : H))) :=
      (tendsto_const_nhds.smul hgrad_lim)
    exact ((show Tendsto (fun _ : ℝ => c)
      atTop (nhds c) from tendsto_const_nhds).sub hv).sub hg |>.sub hI
  let z : H := α⁻¹ • (c - 0 - β • 0 - I)
  have hxlim : Tendsto x atTop (nhds z) := by
    have hs :=
      (show Tendsto (fun _ : ℝ => α⁻¹) atTop (nhds α⁻¹) from tendsto_const_nhds).smul hrest
    have heq : (fun t : ℝ => α⁻¹ •
        (c - deriv x t - β • gradient Φ (x t) -
          ∫ s in (0)..t, gradient Φ (x s))) =ᶠ[atTop] x := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (hx_repr t ht).symm
    simpa [z] using hs.congr' heq
  have hgrad_z : gradient Φ z = 0 := by
    have hzlim : Tendsto (fun t : ℝ => gradient Φ (x t)) atTop (nhds (gradient Φ z)) :=
      (hgrad_cont.tendsto z).comp hxlim
    exact tendsto_nhds_unique hzlim hgrad_lim
  obtain ⟨m, hm⟩ := hmin
  have hm_val : ∀ y, Φ m ≤ Φ y :=
    (Optimization.mem_argminSet_iff Φ m).mp hm
  have hz_stat : z ∈ Optimization.argminSet Φ :=
    stationary_is_argmin Φ hΦC1 hconvex hgrad_z
  have hzm : Φ z = Φ m := le_antisymm (hz_stat m) (hm_val z)
  have hz_mem : z ∈ Optimization.argminSet Φ := by
    intro y
    rw [hzm]
    exact hm_val y
  exact ⟨z, hz_mem, hxlim⟩
```

## Proof explanation
The proof first establishes the regularity needed to differentiate the gradient and the energy. From `hΦ.twice_continuously_differentiable` and `of_le`, the proof obtains that $\Phi$ is $C^1$. From `hxreg`, it gets that $x$ is $C^2$; the lemma `contDiff_succ_iff_deriv` is used to split this into differentiability of $x$ and $C^1$-regularity of $x'$, and then again to obtain differentiability of $x'$. Similarly, `contDiff_succ_iff_fderiv` is applied to the $C^2$-regularity of $\Phi$ to get $C^1$-regularity of $D\Phi$. Since `gradient Φ` is obtained by composing $D\Phi$ with the inverse Riesz isomorphism `(InnerProductSpace.toDual ℝ H).symm`, the proof concludes that $\nabla\Phi$ is $C^1$, hence continuous and differentiable. In particular, `hgradDeriv` gives

$$
\mathrm{HasFDerivAt}(\nabla\Phi,\ D\nabla\Phi(z),\ z)
$$

for every $z\in H$, and $t\mapsto \nabla\Phi(x(t))$ is $C^1$. These facts justify all later derivative computations.

Next, the proof applies `din_forward_internal` to the initial data $(x(0),x'(0))$. This theorem supplies a global forward trajectory $x_g$, its velocity $v_g$, and acceleration $a_g$, with

$$
x_g(0)=x(0),\qquad v_g(0)=x'(0),
$$

and with the same D-IN equation. It also gives uniqueness among $C^2$ D-IN trajectories with the same initial data, and a boundedness implication: if $x_g([0,\infty))$ is bounded, then $v_g$, $a_g$, $\nabla\Phi(x_g)$, and $D\nabla\Phi(x_g)$ are bounded on $[0,\infty)$, and moreover

$$
v_g(t)\to0,\qquad a_g(t)\to0,\qquad \nabla\Phi(x_g(t))\to0
$$

as $t\to\infty$. The proof only uses this boundedness implication and the uniqueness statement from `din_forward_internal`.

To prove boundedness of $x$, the proof invokes `din_weakly_converges_to_argmin`. That theorem gives two facts: for every minimizer $z$ of $\Phi$, the distance $\|x(t)-z\|$ converges to a real number $d_z$; and $x(t)$ converges weakly to some minimizer. The proof only uses the distance-convergence part. Choosing a minimizer $z_{\mathrm{bdd}}$, it gets

$$
\|x(t)-z_{\mathrm{bdd}}\|\to d_0
$$

for some $d_0\in\mathbb R$. By `Metric.tendsto_atTop.1`, for large $t$ this distance is within $1$ of $d_0$, hence

$$
\|x(t)-z_{\mathrm{bdd}}\|\le |d_0|+1
$$

for all sufficiently large $t$. On the compact interval $[0,T_0]$, the continuous image $x([0,T_0])$ is compact, hence bounded. Combining this with the tail bound and the triangle inequality

$$
\|x(t)\|\le \|x(t)-z_{\mathrm{bdd}}\|+\|z_{\mathrm{bdd}}\|
$$

shows that $x([0,\infty))$ is bounded. Thus `BoundedOnNonnegative x` holds. By the uniqueness part of `din_forward_internal`, $x(t)=x_g(t)$ for $t\ge0$, so $x_g$ is also bounded. The boundedness implication from `din_forward_internal` then yields

$$
x'(t)\to0,\qquad \nabla\Phi(x(t))\to0.
$$

The interior-minimizer hypothesis is used next. Choose $z_0$ in the interior of $\mathrm{argminSet}\Phi$. Then there is $\rho>0$ such that

$$
B(z_0,\rho)\subseteq \mathrm{argminSet}\Phi.
$$

The proof applies `convex_supporting_baillon_haddad` to the convex function $\Phi$ and its gradient. This lemma gives the supporting inequality

$$
\Phi(y)+\langle \nabla\Phi(y),p-y\rangle\le \Phi(p)
$$

for all $y,p\in H$. Taking $p=z_0$, and using that $z_0$ is a minimizer so $\Phi(z_0)\le\Phi(y)$, gives

$$
\langle \nabla\Phi(y),z_0-y\rangle\le0,
$$

hence

$$
\langle \nabla\Phi(y),y-z_0\rangle\ge0.
$$

A stronger lower bound is then obtained by taking, when $\nabla\Phi(y)\neq0$, the point

$$
z'=z_0+\frac{\rho}{2}\frac{\nabla\Phi(y)}{\|\nabla\Phi(y)\|}.
$$

Since $z'\in B(z_0,\rho)$, it is also a minimizer. Applying the supporting inequality to $p=z'$ and using $\Phi(z')\le\Phi(y)$ gives

$$
\langle \nabla\Phi(y),y-z'\rangle\ge0.
$$

Expanding $y-z'$ yields

$$
\frac{\rho}{2}\|\nabla\Phi(y)\|
\le
\langle \nabla\Phi(y),y-z_0\rangle.
$$

This inequality is the coercivity estimate that later makes the gradient integrable.

The proof then constructs a Lyapunov function. Define

$$
v(t)=x'(t),\qquad g(t)=\nabla\Phi(x(t)),\qquad r(t)=v(t)+\beta g(t),\qquad u(t)=x(t)-z_0.
$$

Choose

$$
\varepsilon=\min\left(1,\frac{\alpha}{4(\beta+1)}\right),\qquad \kappa=\alpha\beta+1.
$$

The ODE gives

$$
r'(t)=-\alpha v(t)-g(t),
$$

and of course $u'(t)=v(t)$. Define

$$
E(t)=\kappa \Phi(x(t))+\frac12\|r(t)\|^2.
$$

Using the chain rule and the symmetry of the inner product, the proof computes

$$
E'(t)=-\alpha\|v(t)\|^2-\beta\|g(t)\|^2\le0.
$$

Then define the auxiliary function

$$
H(t)=E(t)+\varepsilon\left(\frac{\alpha}{2}\|u(t)\|^2+\langle r(t),u(t)\rangle\right).
$$

Its derivative is

$$
H'(t)
=-(\alpha-\varepsilon)\|v(t)\|^2-\beta\|g(t)\|^2
-\varepsilon\langle g(t),u(t)\rangle
+\varepsilon\beta\langle g(t),v(t)\rangle.
$$

Using Young's inequality

$$
\langle g(t),v(t)\rangle
\le \frac12\bigl(\|g(t)\|^2+\|v(t)\|^2\bigr),
$$

the nonnegativity $\langle g(t),u(t)\rangle\ge0$ proved from the supporting inequality, and the coefficient estimates

$$
0\le \alpha-\varepsilon-\frac{\varepsilon\beta}{2},\qquad
0\le \beta\left(1-\frac{\varepsilon}{2}\right),
$$

the proof obtains $H'(t)\le0$ for $t\ge0$. Since $H$ is continuous on $[0,\infty)$ and differentiable on $(0,\infty)$, the lemma `antitoneOn_of_deriv_nonpos` gives that $H$ is antitone on $[0,\infty)$.

The proof next shows $H$ is bounded below. Since $\Phi$ is bounded below, there is $m\in\mathbb R$ with $m\le\Phi(y)$ for all $y$. Therefore

$$
E(t)\ge \kappa m+\frac12\|r(t)\|^2.
$$

A completing-the-square argument, using the fact that $\varepsilon$ is small enough so that $\alpha-2\varepsilon\ge0$, yields

$$
H(t)\ge \kappa m+\frac{\varepsilon\alpha}{4}\|u(t)\|^2\ge \kappa m.
$$

Thus $H$ is antitone on $[0,\infty)$ and bounded below. The proof extends it to all real $t$ by setting $q(t)=H(\max(t,0))$, shows $q$ is antitone and bounded below, and applies `tendsto_atTop_ciInf` to conclude that $H(t)$ has a finite limit as $t\to\infty$.

This finite limit is used for integrability. The theorem `integrableOn_Ioi_deriv_of_nonpos'` is applied to $H$. It says that if a function is differentiable on $(0,\infty)$, has nonpositive derivative there, and has a finite limit at infinity, then its derivative is integrable on $(0,\infty)$. Hence `deriv H` is integrable on $(0,\infty)$. Since

$$
0\le \varepsilon\langle g(t),u(t)\rangle\le -\mathrm{deriv}H(t),
$$

comparison with the integrable function $-\mathrm{deriv}H$ shows that

$$
t\mapsto \varepsilon\langle g(t),u(t)\rangle
$$

is integrable on $(0,\infty)$. Using the lower bound

$$
\frac{\rho}{2}\|g(t)\|\le \langle g(t),u(t)\rangle,
$$

one obtains

$$
\|g(t)\|\le \frac{2}{\varepsilon\rho}\,\varepsilon\langle g(t),u(t)\rangle.
$$

Therefore $g(t)=\nabla\Phi(x(t))$ is integrable on $(0,\infty)$. Thus the improper integral

$$
I=\int_0^\infty \nabla\Phi(x(s))\,ds
$$

is well-defined.

Now the proof uses `din_integrated_identity`. This lemma states that for every $t\ge0$,

$$
x'(t)+\alpha x(t)+\beta\nabla\Phi(x(t))
+\int_0^t \nabla\Phi(x(s))\,ds
=x'(0)+\alpha x(0)+\beta\nabla\Phi(x(0)).
$$

Let

$$
c=x'(0)+\alpha x(0)+\beta\nabla\Phi(x(0)).
$$

Solving the identity for $x(t)$ gives

$$
x(t)
=\alpha^{-1}\left(
c-x'(t)-\beta\nabla\Phi(x(t))
-\int_0^t \nabla\Phi(x(s))\,ds
\right).
$$

The proof already knows $x'(t)\to0$, $\nabla\Phi(x(t))\to0$, and by `intervalIntegral_tendsto_integral_Ioi`,

$$
\int_0^t \nabla\Phi(x(s))\,ds \to I.
$$

Therefore the entire right-hand side converges to

$$
z=\alpha^{-1}(c-\beta\cdot 0-I).
$$

Consequently,

$$
x(t)\to z
$$

strongly.

It remains to show that $z$ is a minimizer. Since $\nabla\Phi$ is continuous and $x(t)\to z$,

$$
\nabla\Phi(x(t))\to \nabla\Phi(z).
$$

But already $\nabla\Phi(x(t))\to0$. By uniqueness of limits,

$$
\nabla\Phi(z)=0.
$$

The lemma `stationary_is_argmin` says that if $\Phi$ is $C^1$, globally convex, and $\nabla\Phi(p)=0$, then $p\in\mathrm{argminSet}\Phi$. Hence $z$ is a global minimizer. Finally, the proof chooses a minimizer $m$ from `hmin`. Since $m$ is a minimizer, $\Phi(m)\le\Phi(y)$ for every $y$. Since $z$ is also a minimizer, $\Phi(z)\le\Phi(m)$. Thus $\Phi(z)=\Phi(m)$, and therefore $\Phi(z)\le\Phi(y)$ for every $y$. This confirms that $z\in\mathrm{argminSet}\Phi$ and completes the proof.

In Lean, commands such as `intro` introduce local variables or hypotheses; `rw` rewrites goals using definitions and equalities such as the derivative formulas; `simp` and `simpa` unfold definitions like `gradient`, `BoundedOnNonnegative`, and composition; `exact` applies a cited theorem or a previously proved fact; `linarith` and `nlinarith` discharge the scalar inequalities coming from Young's inequality and the coefficient estimates; and `ring_nf` and `module` prove algebraic identities in $\mathbb R$ and in the vector space $H$.

