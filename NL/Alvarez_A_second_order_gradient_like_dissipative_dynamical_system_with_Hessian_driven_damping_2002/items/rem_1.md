## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/rem_1.lean`

## Lean statement
```lean
theorem quadratic_potential_limit_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (A : H →L[ℝ] H)
    (α β : ℝ) (x : ℝ → H) (hΦ : AssumptionH H Φ)
    (hquadratic : ∀ u, Φ u = (1 / 2 : ℝ) * ⟪A u, u⟫_ℝ)
    (hselfadjoint : ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ)
    (hpositive : ∀ u, 0 ≤ ⟪A u, u⟫_ℝ)
    (hsol : IsDINTrajectory H Φ α β x) (hx : ContDiff ℝ 2 x)
    (hαβ : α * β ≤ 1) :
    Optimization.argminSet Φ = (A.ker : Set H) ∧
      ∃ p, p ∈ A.ker ∧
        ‖x 0 + (α⁻¹ : ℝ) • deriv x 0 - p‖ =
          Metric.infDist (x 0 + (α⁻¹ : ℝ) • deriv x 0) (A.ker : Set H) ∧
        Tendsto x atTop (nhds p)
```

## Statement explanation
The declaration is set in a real Hilbert space $H$. It concerns a potential $\Phi : H \to \mathbb{R}$, a continuous linear operator $A : H \to H$, real parameters $\alpha,\beta$, and a trajectory $x : \mathbb{R} \to H$. The hypotheses are:

- $\Phi$ satisfies the standing regularity hypothesis `AssumptionH H Φ`; its exact content is not unfolded in this proof.
- $\Phi$ is the quadratic potential

$$
\Phi(u)=\frac12\langle Au,u\rangle
$$

  for every $u\in H$.
- $A$ is self-adjoint:

$$
\langle Au,v\rangle=\langle u,Av\rangle
$$

  for all $u,v\in H$.
- $A$ is positive semidefinite:

$$
0\le \langle Au,u\rangle
$$

  for every $u\in H$.
- $x$ is a trajectory of the second-order dissipative gradient-like system encoded by `IsDINTrajectory H Φ α β x`. The proof uses from this hypothesis that $\alpha\gt 0$, that $\beta\gt 0$, and that the associated differential equation holds at nonnegative times.
- $x$ is twice continuously differentiable, $x\in C^2$.
- The parameters satisfy

$$
\alpha\beta\le 1.
$$

The conclusion has two parts. First,

$$
\mathrm{argminSet}\Phi=\ker A,
$$

where $\mathrm{argminSet}\Phi$ is the set of global minimizers of $\Phi$, i.e.

```math
\mathrm{argminSet}\Phi=\{u\in H:\forall y\in H,\ \Phi(u)\le \Phi(y)\}.
```

Second, there exists $p\in\ker A$ such that

```math
\left\|x(0)+\alpha^{-1}\dot x(0)-p\right\|
=\mathrm{infDist}\!\left(x(0)+\alpha^{-1}\dot x(0),\ker A\right),
```

and

$$
x(t)\to p\quad\text{as }t\to\infty.
$$

Thus the quadratic potential has exactly the kernel of $A$ as its minimizer set, and every trajectory satisfying the stated DIn hypotheses converges to a point of that kernel. Moreover, the limit point $p$ is a nearest point, hence the metric projection, of the initial shifted vector

$$
q=x(0)+\alpha^{-1}\dot x(0)
$$

onto the closed convex set $\ker A$.

## Lean proof
```lean
by
  have hargmin : Optimization.argminSet Φ = (A.ker : Set H) := by
    ext u
    constructor
    · intro hu
      have hΦu : Φ u ≤ Φ 0 := hu 0
      have hΦ0 : Φ 0 = 0 := by simp [hquadratic]
      have hqu : ⟪A u, u⟫_ℝ = 0 := by
        have hnonneg : 0 ≤ ⟪A u, u⟫_ℝ := hpositive u
        rw [hquadratic, hΦ0] at hΦu
        nlinarith
      exact (quadratic_form_zero_iff_mem_ker A hselfadjoint hpositive u).mp hqu
    · intro hu v
      rw [hquadratic, hquadratic]
      have hzero : A u = 0 := by exact hu
      simpa [hzero] using mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (hpositive v)
  have hconvex : ConvexOn ℝ Set.univ Φ :=
    quadratic_potential_convex Φ A hquadratic hselfadjoint hpositive
  have hmin : (Optimization.argminSet Φ).Nonempty := by
    rw [hargmin]
    exact ⟨0, by simp⟩
  obtain ⟨p, hpmin, hxp⟩ :=
    din_strong_convergence_of_even_potential Φ α β x hΦ hconvex hmin hsol hx hαβ
      (by intro u; rw [hquadratic, hquadratic]; simp)
  have hpker : p ∈ A.ker := by
    have hpmin' : p ∈ (A.ker : Set H) := by simpa [hargmin] using hpmin
    exact hpmin'
  let q : H := x 0 + (α⁻¹ : ℝ) • deriv x 0
  let K : Set H := (A.ker : Set H)
  have hKnonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    simp [K]
  have hKclosed : IsClosed K := by
    simpa [K] using (A.isClosed_ker : IsClosed (A.ker : Set H))
  have hKconvex : Convex ℝ K := by
    simpa [K] using (A.ker.convex : Convex ℝ (A.ker : Set H))
  let hCheb := isChebyshev_of_nonempty_isClosed_convex hKnonempty hKclosed hKconvex
  refine ⟨hargmin, p, hpker, ?_, hxp⟩
  have horth : ∀ z ∈ K, ⟪q - p, z⟫_ℝ = 0 := by
    intro z hz
    have hgrad_eq : gradient Φ = A :=
      quadratic_gradient_eq Φ A hΦ hquadratic hselfadjoint
    have hhess_eq : ∀ u, fderiv ℝ (gradient Φ) u = A := by
      intro u
      rw [hgrad_eq]
      exact A.hasFDerivAt.fderiv
    have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
      obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hxp) 1 zero_lt_one
      let T₀ : ℝ := max T 0
      have htail : ∀ t, T₀ ≤ t → ‖x t‖ ≤ ‖p‖ + 1 := by
        intro t ht
        have hdist' : dist (x t) p < 1 :=
          hT t (le_trans (le_max_left T 0) ht)
        have hsub : ‖x t - p‖ < 1 := by
          simpa [dist_eq_norm] using hdist'
        calc
          ‖x t‖ = ‖(x t - p) + p‖ := by congr 1; module
          _ ≤ ‖x t - p‖ + ‖p‖ := norm_add_le _ _
          _ ≤ 1 + ‖p‖ := by linarith
          _ = ‖p‖ + 1 := by ring
      have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
        exact isCompact_Icc.image_of_continuousOn
          (hx.continuous.continuousOn.mono Set.Icc_subset_Ici_self)
      rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
      refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (‖p‖ + 1), ?_⟩
      rintro y ⟨t, ht, rfl⟩
      by_cases hle : t ≤ T₀
      · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
      · exact (htail t (le_of_not_ge hle)).trans (le_max_right _ _)
    have hpartiii := din_global_properties_part_iii Φ hΦ α β hsol.1 hsol.2.1
      (x 0) (deriv x 0) x rfl rfl hsol hx hx_bounded
    obtain ⟨_, _, _, _, hvlim, _, _⟩ := hpartiii
    let f : ℝ → ℝ := fun t => ⟪deriv x t + α • x t, z⟫_ℝ
    have hx_at (t : ℝ) : HasDerivAt x (deriv x t) t :=
      (hx.differentiable (by norm_num) t).hasDerivAt
    have hv_at (t : ℝ) : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
      (hx.differentiable_deriv_two t).hasDerivAt
    have hu_at (t : ℝ) : HasDerivAt (fun s => deriv x s + α • x s)
        (deriv (deriv x) t + α • deriv x t) t := by
      exact (hv_at t).add ((hx_at t).const_smul α)
    have hzero_deriv (t : ℝ) (ht : 0 ≤ t) :
        deriv (fun s => ⟪deriv x s + α • x s, z⟫_ℝ) t = 0 := by
      have heq := hsol.2.2 t ht
      rw [hhess_eq (x t), hgrad_eq] at heq
      have hz' : A z = 0 := by
        change A z = 0 at hz
        exact hz
      have hAv : ⟪A (deriv x t), z⟫_ℝ = 0 := by
        rw [hselfadjoint]
        simp [hz']
      have hAx : ⟪A (x t), z⟫_ℝ = 0 := by
        rw [hselfadjoint]
        simp [hz']
      have hode_inner :
          ⟪deriv (deriv x) t + α • deriv x t, z⟫_ℝ = 0 := by
        have heq' := congrArg (fun v : H => ⟪v, z⟫_ℝ) heq
        simpa [inner_add_left, inner_smul_left, hAv, hAx] using heq'
      have hf' := (hu_at t).inner ℝ (hasDerivAt_const t z)
      rw [hf'.deriv]
      simp only [inner_zero_right, hode_inner, add_zero]
    have hf_diff : DifferentiableOn ℝ f (Set.Ici (0 : ℝ)) := by
      intro t ht
      have hf_at := (hu_at t).inner ℝ (hasDerivAt_const t z)
      simpa [f] using hf_at.differentiableAt.differentiableWithinAt
    have hf_fderiv : ∀ t ∈ Set.Ici (0 : ℝ),
        fderivWithin ℝ f (Set.Ici (0 : ℝ)) t = 0 := by
      intro t ht
      have hf_at : HasDerivAt f 0 t := by
        have hf_raw := (hu_at t).inner ℝ (hasDerivAt_const t z)
        have hder0 := hzero_deriv t ht
        rw [hf_raw.deriv] at hder0
        have hinner :
            ⟪deriv (deriv x) t + α • deriv x t, z⟫_ℝ = 0 := by
          simpa [inner_zero_right] using hder0
        convert hf_raw using 1;
          simp [inner_zero_right, hinner]
      have hfw :=
        ((hf_at.hasDerivWithinAt (s := Set.Ici (0 : ℝ))).hasFDerivWithinAt).fderivWithin
          (uniqueDiffOn_Ici 0 t ht)
      simpa using hfw
    have hf_const : ∀ t ∈ Set.Ici (0 : ℝ), f t = f 0 := by
      intro t ht
      exact (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero hf_diff hf_fderiv
        ht (Set.mem_Ici.mpr (le_refl 0))
    have hflim : Tendsto f atTop (nhds (⟪(0 : H) + α • p, z⟫_ℝ)) := by
      have hsum : Tendsto (fun t => deriv x t + α • x t) atTop
          (nhds ((0 : H) + α • p)) := hvlim.add (hxp.const_smul α)
      simpa [f] using hsum.inner (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) atTop (nhds z))
    have hflim0 : Tendsto f atTop (nhds (f 0)) := by
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hf_const t (Set.mem_Ici.mpr ht)
    have hfeq : f 0 = ⟪(0 : H) + α • p, z⟫_ℝ :=
      tendsto_nhds_unique hflim0 hflim
    have hfeq' : ⟪deriv x 0, z⟫_ℝ + α * ⟪x 0, z⟫_ℝ =
        α * ⟪p, z⟫_ℝ := by
      simpa [f, inner_add_left, real_inner_smul_left] using hfeq
    have hzorth : α * ⟪q - p, z⟫_ℝ = 0 := by
      dsimp [q]
      rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      field_simp [ne_of_gt hsol.1]
      nlinarith [hfeq']
    exact (mul_eq_zero.mp hzorth).resolve_left (ne_of_gt hsol.1)
  have hp_proj : p = projectionPoint K hCheb q := by
    refine (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hCheb hKconvex).mpr ?_
    refine ⟨by simpa [K] using hpker, ?_⟩
    intro z hz
    have hzorth := horth z hz
    have hporth : ⟪q - p, p⟫_ℝ = 0 := by
      have := horth p (by simpa [K] using hpker)
      exact this
    have hpterm : ⟪p, q - p⟫_ℝ = 0 := by
      simpa [real_inner_comm] using hporth
    have hzorth' : ⟪z, q - p⟫_ℝ = 0 := by
      simpa [real_inner_comm] using hzorth
    have : ⟪z - p, q - p⟫_ℝ = 0 := by
      rw [inner_sub_left]
      rw [hzorth', hpterm]
      ring
    exact le_of_eq this
  calc
    ‖q - p‖ = dist q p := by simp [dist_eq_norm]
    _ = dist q (projectionPoint K hCheb q) := by rw [← hp_proj]
    _ = Metric.infDist q K := (projectionPoint_isBestApproximation K hCheb q).2
    _ = Metric.infDist (x 0 + (α⁻¹ : ℝ) • deriv x 0) (A.ker : Set H) := by simp [q, K]
```

## Proof explanation
The proof first establishes the equality $\mathrm{argminSet}\Phi=\ker A$. It uses `ext u`, the extensionality principle for sets, to reduce the equality to proving, for an arbitrary $u\in H$, that $u\in\mathrm{argminSet}\Phi$ if and only if $u\in\ker A$.

For the forward direction, assume $u\in\mathrm{argminSet}\Phi$. Then by definition of the argmin set, $\Phi(u)\le \Phi(y)$ for every $y$, in particular for $y=0$, so $\Phi(u)\le\Phi(0)$. Using the quadratic formula and the fact that $A0=0$, the value at $0$ is

$$
\Phi(0)=\frac12\langle A0,0\rangle=0.
$$

Hence

$$
\frac12\langle Au,u\rangle=\Phi(u)\le 0.
$$

On the other hand, positivity of $A$ gives $0\le \langle Au,u\rangle$. Therefore $\langle Au,u\rangle=0$. The lemma `quadratic_form_zero_iff_mem_ker` says exactly that, for a self-adjoint positive operator $A$, one has

$$
\langle Au,u\rangle=0 \iff u\in\ker A.
$$

Applying it with the hypotheses `hselfadjoint` and `hpositive` gives $u\in\ker A$. The tactic `nlinarith` is used to combine the inequalities and the identity $\Phi(u)=\frac12\langle Au,u\rangle$ to force $\langle Au,u\rangle=0$.

For the reverse direction, assume $u\in\ker A$, so $Au=0$. To show that $u$ minimizes $\Phi$, fix any $v\in H$. Rewriting by the quadratic formula gives

$$
\Phi(u)=\frac12\langle Au,u\rangle=0
$$

and

$$
\Phi(v)=\frac12\langle Av,v\rangle.
$$

Since $A$ is positive, $\langle Av,v\rangle\ge 0$, and since $\frac12\ge 0$, we get $\Phi(v)\ge 0=\Phi(u)$. Thus $u\in\mathrm{argminSet}\Phi$. The proof uses `mul_nonneg` for the product $\frac12\langle Av,v\rangle\ge 0$ and `norm_num` to verify $\frac12\ge0$.

Next, the proof uses `quadratic_potential_convex`. That result states that if $\Phi(u)=\frac12\langle Au,u\rangle$, $A$ is self-adjoint, and $A$ is positive, then $\Phi$ is convex on all of $H$. Concretely, this means that for all $u,v\in H$ and $0\lt \lambda\lt 1$,

$$
\Phi(\lambda u+(1-\lambda)v)
\le
\lambda\Phi(u)+(1-\lambda)\Phi(v).
$$

This convexity is one of the hypotheses needed for the convergence theorem.

The proof then shows that $\mathrm{argminSet}\Phi$ is nonempty. Since it has already proved $\mathrm{argminSet}\Phi=\ker A$, and $0\in\ker A$, the element $0$ belongs to the argmin set. This supplies the hypothesis `hmin` required by the strong convergence theorem.

The convergence theorem `din_strong_convergence_of_even_potential` is then applied. Its mathematical content is: if $\Phi$ satisfies the standing assumptions, is convex on $H$, has a nonempty argmin set, $x$ is a DIn trajectory for $\Phi,\alpha,\beta$, $x\in C^2$, $\alpha\beta\le1$, and $\Phi$ is even, i.e.

$$
\Phi(y)=\Phi(-y)
$$

for every $y$, then there exists $z\in\mathrm{argminSet}\Phi$ such that

$$
x(t)\to z\quad\text{as }t\to\infty.
$$

Here evenness follows from the quadratic formula:

$$
\Phi(-u)=\frac12\langle A(-u),-u\rangle
=\frac12\langle Au,u\rangle
=\Phi(u).
$$

The proof supplies this explicitly by rewriting with `hquadratic` and simplifying. The theorem yields a point $p\in\mathrm{argminSet}\Phi$ and the convergence $x(t)\to p$. Since $\mathrm{argminSet}\Phi=\ker A$, the proof converts $p\in\mathrm{argminSet}\Phi$ into $p\in\ker A$.

The rest of the proof identifies this limit $p$ as the metric projection of

$$
q=x(0)+\alpha^{-1}\dot x(0)
$$

onto the kernel $K=\ker A$. First it records that $K$ is nonempty, because $0\in K$, that $K$ is closed, because the kernel of a continuous linear map is closed, and that $K$ is convex, because the kernel of a linear map is convex. The theorem `isChebyshev_of_nonempty_isClosed_convex` then shows that every nonempty closed convex subset of a Hilbert space is Chebyshev, meaning that every point of $H$ has a unique nearest point in the set. Therefore the projection point `projectionPoint K hCheb q` is available.

The key step is to prove that for every $z\in K$,

$$
\langle q-p,z\rangle=0.
$$

This says that $q-p$ is orthogonal to the entire kernel $K$. To prove it, the proof first uses `quadratic_gradient_eq`. That lemma states that if $\Phi(u)=\frac12\langle Au,u\rangle$, $A$ is self-adjoint, and $\Phi$ satisfies the standing assumptions, then the gradient of $\Phi$ is exactly $A$:

$$
\nabla\Phi=A.
$$

Consequently the Hessian of $\Phi$ is also $A$, since the derivative of the continuous linear map $A$ is $A$ itself:

$$
\mathrm{fderiv}_{\mathbb R}(\nabla\Phi)(u)=A
$$

for every $u$.

The proof then establishes that $x$ is bounded on $[0,\infty)$. Since $x(t)\to p$, there is $T$ such that

$$
\mathrm{dist}(x(t),p)<1
$$

for all $t\ge T$. Let $T_0=\max(T,0)$. For $t\ge T_0$, the triangle inequality gives

```math
\|x(t)\|\le \|p\|+1.
```

On the compact interval $[0,T_0]$, the continuous image $x([0,T_0])$ is compact, hence bounded. Combining the bounded initial segment with the bounded tail gives that the whole set $x([0,\infty))$ is bounded. This is needed to apply `din_global_properties_part_iii`.

The theorem `din_global_properties_part_iii` states that if $x$ is a DIn trajectory for positive $\alpha,\beta$, is $C^2$, and has bounded position on $[0,\infty)$, then the velocity, acceleration, gradient $\nabla\Phi(x(t))$, and derivative \mathrm{fderiv}_{\mathbb R}(\nabla\Phi)(x(t)) are bounded, and moreover

$$
\dot x(t)\to0,\qquad
\ddot x(t)\to0,\qquad
\nabla\Phi(x(t))\to0
$$

as $t\to\infty$. The proof uses this theorem to obtain in particular

$$
\dot x(t)\to0.
$$

Now fix $z\in K$ and define

$$
f(t)=\langle \dot x(t)+\alpha x(t),z\rangle.
$$

The proof shows that $f$ is constant on $[0,\infty)$. For $t\ge0$, the differential equation component `hsol.2.2 t ht` is used. After replacing $\nabla\Phi$ by $A$ and the Hessian of $\Phi$ by $A$, the DIn equation contains terms involving $A\dot x(t)$ and $A x(t)$. Since $z\in\ker A$ and $A$ is self-adjoint,

$$
\langle A\dot x(t),z\rangle
=\langle \dot x(t),Az\rangle
=0,
$$

and

$$
\langle A x(t),z\rangle
=\langle x(t),Az\rangle
=0.
$$

Therefore, taking the inner product of the DIn equation with $z$, those terms vanish and one obtains

$$
\langle \ddot x(t)+\alpha\dot x(t),z\rangle=0.
$$

But this is precisely the derivative of $f$, because the derivative of $\dot x+\alpha x$ is $\ddot x+\alpha\dot x$ and $z$ is constant. Thus $f'(t)=0$ for every $t\ge0$. Since $[0,\infty)$ is convex and the derivative of $f$ within this interval is everywhere zero, the mean-value/convexity fact `convex_Ici ... .is_const_of_fderivWithin_eq_zero` implies

$$
f(t)=f(0)
$$

for every $t\ge0$.

On the other hand, since $\dot x(t)\to0$ and $x(t)\to p$, we have

$$
\dot x(t)+\alpha x(t)\to 0+\alpha p.
$$

Taking inner products with the fixed vector $z$ gives

$$
f(t)\to \langle 0+\alpha p,z\rangle.
$$

But since $f(t)=f(0)$ for all sufficiently large $t$, also $f(t)\to f(0)$. By uniqueness of limits,

$$
f(0)=\langle 0+\alpha p,z\rangle.
$$

Unfolding $f(0)$,

$$
\langle \dot x(0),z\rangle+\alpha\langle x(0),z\rangle
=\alpha\langle p,z\rangle.
$$

Rearranging and using $q=x(0)+\alpha^{-1}\dot x(0)$ gives

$$
\alpha\langle q-p,z\rangle=0.
$$

Because $\alpha\gt 0$, this implies

$$
\langle q-p,z\rangle=0.
$$

Thus $q-p$ is orthogonal to every $z\in K$.

The proof now applies the variational characterization of the metric projection, `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos`. For a Chebyshev convex set $K$, this theorem says that

$$
r=\mathrm{projectionPoint} K h_{\mathrm{Cheb}} q
$$

if and only if $r\in K$ and

$$
\langle z-r,q-r\rangle\le0
$$

for every $z\in K$. The proof has $p\in K$. From $\langle q-p,z\rangle=0$ for every $z\in K$, it follows in particular with $z=p$ that $\langle q-p,p\rangle=0$. By symmetry of the real inner product, $\langle p,q-p\rangle=0$, and also $\langle z,q-p\rangle=0$. Therefore

$$
\langle z-p,q-p\rangle
=\langle z,q-p\rangle-\langle p,q-p\rangle
=0\le0.
$$

So $p$ satisfies the projection variational inequality. Hence

$$
p=\mathrm{projectionPoint} K h_{\mathrm{Cheb}} q.
$$

Finally, `projectionPoint_isBestApproximation` states that the chosen projection point is a best approximation, so

$$
\mathrm{dist}(q,\mathrm{projectionPoint} K h_{\mathrm{Cheb}} q)
=\mathrm{infDist}(q,K).
$$

Using $p=\mathrm{projectionPoint} K h_{\mathrm{Cheb}} q$, the proof obtains

```math
\|q-p\|
=\mathrm{dist}(q,p)
=\mathrm{dist}(q,\mathrm{projectionPoint} K h_{\mathrm{Cheb}} q)
=\mathrm{infDist}(q,K).
```

Substituting $q=x(0)+\alpha^{-1}\dot x(0)$ and $K=\ker A$ gives exactly the claimed equality

```math
\left\|x(0)+\alpha^{-1}\dot x(0)-p\right\|
=\mathrm{infDist}\!\left(x(0)+\alpha^{-1}\dot x(0),\ker A\right).
```

Together with the earlier equality $\mathrm{argminSet}\Phi=\ker A$, the inclusion $p\in\ker A$, and the convergence $x(t)\to p$, this completes the proof.

