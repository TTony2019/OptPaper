## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/cor_4.lean`

## Lean statement
```lean
theorem cor_4 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (xbar : M → H) (u₀ v₀ : M → H)
    (β γ : ℝ) (δ : M → ℝ) (r T : ℝ)
    (hβγ : β * γ > 1) (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 0 < r) (hT : 0 < T)
    (hdiff : ∀ μ ∈ V, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ ∈ V, ∀ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ ∈ V, IsStronglyConvex (φ μ) (δ μ))
    (hDIN : ∀ μ, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (hball : ∀ μ ∈ V, ∀ T' > 0, ∀ᵐ t ∂ MeasureTheory.volume,
      t ∈ Set.Icc (0 : ℝ) T' → ‖x μ t‖ ≤ r)
    (hbdd : ∀ μ ∈ V, ∀ μ' ∈ V,
      BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖gradφ μ u - gradφ μ' u‖})
    (hcrit : ∀ μ ∈ V, gradφ μ (xbar μ) = 0) :
    (∀ μ ∈ V, ∀ μ' ∈ V, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (-cmax * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          β * cmax⁻¹ * (1 - Real.exp (-cmax * t)) * def_6 r hr (gradφ μ) (gradφ μ')) ∧
    (∀ μ ∈ V, Tendsto (x μ) atTop (nhds (xbar μ)) ∧ xbar μ ∈ Optimization.argminSet (φ μ)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ‖xbar μ - xbar μ'‖ ≤ β * cmax⁻¹ * def_6 r hr (gradφ μ) (gradφ μ'))
```

## Statement explanation
The theorem `cor_4` is a quantitative stability, convergence, and minimizer-separation result for a family of damped inertial Newton trajectories indexed by $\mu\in V\subseteq M$. The space $H$ is a complete real inner product space, and $M$ is a normed additive commutative group. For each index $\mu$, $\varphi_\mu=\varphi(\mu,\cdot):H\to\mathbb R$ is the potential, $\mathrm{grad}\varphi_\mu$ is its gradient, and `hessφ` represents the Fréchet derivative of the gradient, i.e. the Hessian. The path $x_\mu:\mathbb R\to H$ is the position trajectory, $dx_\mu$ is its velocity, and $ddx_\mu$ is its acceleration. The initial data are $u_0(\mu)$ and $v_0(\mu)$, while $\bar x_\mu$ is the candidate critical point/limit. The parameters $\beta,\gamma$ are the DIN parameters, $\delta_\mu$ is a strong-convexity modulus, $r\gt 0$ is a ball radius, and $T\gt 0$ is a time horizon.

The hypotheses say: $\beta\gt 0$, $\gamma\gt 0$, $1\lt \beta\gamma$, $r\gt 0$, $T\gt 0$; on $V$, each $\varphi_\mu$ is differentiable, has gradient $\mathrm{grad}\varphi_\mu$, and is strongly convex with modulus $\delta_\mu$. For every $\mu$, the triple $(x_\mu,dx_\mu,ddx_\mu)$ satisfies the damped inertial Newton system with initial data $(u_0(\mu),v_0(\mu))$. In the proof, the concretely used consequences are that $x_\mu$ and $dx_\mu$ are locally absolutely continuous, that the initial conditions hold, and that almost everywhere

```math
ddx_\mu+\gamma\,dx_\mu+\beta\,\mathrm{hess}\varphi_\mu(x_\mu)(dx_\mu)+\mathrm{grad}\varphi_\mu(x_\mu)=0.
```

The hypotheses `hderiv` and `hddx` state that almost everywhere on $[0,\infty)$, $x_\mu$ has derivative $dx_\mu$ and $dx_\mu$ has derivative $ddx_\mu$. The hypothesis `hhess` says that at each $q\in H$, the map $\mathrm{grad}\varphi_\mu$ is Fréchet differentiable at $q$ with derivative represented by $\mathrm{hess}\varphi_\mu(q)$. The hypothesis `hlip` says that each gradient field is Lipschitz on the compact trajectory image $x_\mu([0,T'])$. The hypothesis `hball` says that, for $\mu\in V$, almost every $t\in[0,T']$ satisfies $`\|x_\mu(t)\|\le r`$. The hypothesis `hbdd` says that for $\mu,\mu'\in V$, the set of discrepancies

```math
\{\|\mathrm{grad}\varphi_\mu(u)-\mathrm{grad}\varphi_{\mu'}(u)\|:\|u\|\le r\}
```

is bounded above. Finally, `hcrit` says $\mathrm{grad}\varphi_\mu(\bar x_\mu)=0$. The differentiability hypothesis `hdiff` is stated but is not invoked directly in the displayed proof.

Two auxiliary quantities appear throughout. First, for functions $A,B:H\to H$,

```math
D_r(A,B)=\texttt{def\_6 r hr A B}
=\sup\{\|A u-Bu\|:\|u\|\le r\}.
```

Second,

$$
\rho_\mu=\mathrm{energyRate}\beta\gamma(\delta_\mu)
=\frac{(\beta\delta_\mu+\gamma)-\sqrt{(\beta\delta_\mu+\gamma)^2-4\delta_\mu}}2.
$$

The initial auxiliary coordinate is

```math
z_{0,\mu}=\mathrm{dinAuxInitial}\mathrm{grad}\varphi\,\beta\,\gamma\,u_0\,v_0\,\mu
=-\left(\sqrt{(\gamma-1/\beta)(1/\beta)}\right)^{-1}
\left(v_0(\mu)+\beta\mathrm{grad}\varphi_\mu(u_0(\mu))+(\gamma-1/\beta)u_0(\mu)\right).
```

The DIN gradient field is

```math
F_\mu(p)=\left(
\beta\mathrm{grad}\varphi_\mu(p_1)
+\sqrt{\gamma-1/\beta}\left(\sqrt{\gamma-1/\beta}\,p_1+\sqrt{1/\beta}\,p_2\right),
\sqrt{1/\beta}\left(\sqrt{\gamma-1/\beta}\,p_1+\sqrt{1/\beta}\,p_2\right)
\right).
```

The conclusion is a conjunction of three statements. First, for all $\mu,\mu'\in V$, with

$$
c_{\mu,\mu'}=\max(\rho_\mu,\rho_{\mu'}),
$$

almost every real $t$ satisfying $t\in[0,T]$ obeys

```math
\|x_\mu(t)-x_{\mu'}(t)\|
\le e^{-c_{\mu,\mu'}t}
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|z_{0,\mu}-z_{0,\mu'}\|^2}
+\beta\,c_{\mu,\mu'}^{-1}
\left(1-e^{-c_{\mu,\mu'}t}\right)
D_r(\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

Second, for every $\mu\in V$, the trajectory $x_\mu(t)$ converges to $\bar x_\mu$ as $t\to\infty$, and $\bar x_\mu$ is a minimizer of $\varphi_\mu$. Third, for all $\mu,\mu'\in V$,

```math
\|\bar x_\mu-\bar x_{\mu'}\|
\le \beta\,c_{\mu,\mu'}^{-1}
D_r(\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

Thus the result bounds the distance between two trajectories by an exponentially decaying term depending on initial data plus a term proportional to the uniform discrepancy between the two gradient fields, and it bounds the asymptotic minimizer gap by the same discrepancy.

## Lean proof
```lean
by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  -- Pointwise, oriented estimate on the whole half-line: the discrepancy of the
  -- two gradient fields is bounded by `β D_r` along the ball-constrained trajectory.
  have key (a b : M) (ha : a ∈ V) (hb : b ∈ V) : ∀ t, 0 ≤ t →
      ‖x a t - x b t‖ ≤ Real.exp (-(energyRate β γ (δ b)) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        (energyRate β γ (δ b))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ b)) * t)) *
          (β * def_6 r hr (gradφ a) (gradφ b)) := by
    intro t ht
    have hT : 0 < t + 1 := by linarith
    refine din_oriented_comparison gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) a b
      hlift (fun p q => energyStrong_of_strongConvex (μ := b) hβ hβγ (hstrong b hb) (hgrad b hb) p q)
      (energyRate_pos hβ hγ (hstrong b hb).1 hβγ) (β * def_6 r hr (gradφ a) (gradφ b))
      (mul_nonneg hβ.le (def_6_nonneg r hr (gradφ a) (gradφ b))) (t + 1) hT ?_
      t ht (by linarith)
    filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
      (hball a ha (t + 1) hT)] with s hs
    have hfst : (DINGradientField gradφ β γ a (hlift.X a s)).1 -
        (DINGradientField gradφ β γ b (hlift.X a s)).1 =
        β • (gradφ a (hlift.X a s).1 - gradφ b (hlift.X a s).1) := by
      dsimp [DINGradientField]
      module
    have hsnd : (DINGradientField gradφ β γ a (hlift.X a s)).2 -
        (DINGradientField gradφ β γ b (hlift.X a s)).2 = 0 := by
      dsimp [DINGradientField]
      simp
    rw [hfst, hsnd, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), norm_smul,
      Real.norm_of_nonneg hβ.le]
    have hxr : ‖(hlift.X a s).1‖ ≤ r := by
      simpa [hlift.fst_eq a s] using hs
    exact mul_le_mul_of_nonneg_left (le_def_6 hr (hbdd a ha b hb) hxr) hβ.le
  -- The symmetric `max` form, valid for every `t ≥ 0`.
  have hbound (a b : M) (ha : a ∈ V) (hb : b ∈ V) : ∀ t, 0 ≤ t →
      ‖x a t - x b t‖ ≤
        Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
          Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
            dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
        β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
          (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
            def_6 r hr (gradφ a) (gradφ b) := by
    by_cases hc : energyRate β γ (δ a) ≤ energyRate β γ (δ b)
    · intro t ht
      calc ‖x a t - x b t‖ ≤ Real.exp (-(energyRate β γ (δ b)) * t) *
            Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
              dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
          (energyRate β γ (δ b))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ b)) * t)) *
            (β * def_6 r hr (gradφ a) (gradφ b)) := key a b ha hb t ht
        _ = Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
              Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
                dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
            β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
              (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
                def_6 r hr (gradφ a) (gradφ b) := by
          rw [max_eq_right hc]
          ring
    · have hc' : energyRate β γ (δ b) ≤ energyRate β γ (δ a) := le_of_not_ge hc
      intro t ht
      calc ‖x a t - x b t‖ = ‖x b t - x a t‖ := by rw [norm_sub_rev]
        _ ≤ Real.exp (-(energyRate β γ (δ a)) * t) *
              Real.sqrt (‖u₀ b - u₀ a‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ b -
                dinAuxInitial gradφ β γ u₀ v₀ a‖ ^ 2) +
            (energyRate β γ (δ a))⁻¹ * (1 - Real.exp (-(energyRate β γ (δ a)) * t)) *
              (β * def_6 r hr (gradφ b) (gradφ a)) := key b a hb ha t ht
        _ = Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t) *
              Real.sqrt (‖u₀ a - u₀ b‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ a -
                dinAuxInitial gradφ β γ u₀ v₀ b‖ ^ 2) +
            β * (max (energyRate β γ (δ a)) (energyRate β γ (δ b)))⁻¹ *
              (1 - Real.exp (-(max (energyRate β γ (δ a)) (energyRate β γ (δ b))) * t)) *
                def_6 r hr (gradφ a) (gradφ b) := by
          rw [max_eq_left hc', norm_sub_rev (u₀ b) (u₀ a),
            norm_sub_rev (dinAuxInitial gradφ β γ u₀ v₀ b) (dinAuxInitial gradφ β γ u₀ v₀ a),
            def_6_comm r hr (gradφ b) (gradφ a)]
          ring
  refine ⟨?_, ?_, ?_⟩
  · -- the D_r estimate on [0,T]
    intro μ hμ μ' hμ'
    dsimp only
    exact Filter.Eventually.of_forall fun t ht => hbound μ μ' hμ hμ' t ht.1
  · intro μ hμ
    exact ⟨din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
        (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ hμ) (hgrad μ hμ) p q) hβ
        (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ) (hcrit μ hμ),
      mem_argminSet_of_grad_eq_zero (hstrong μ hμ) (hgrad μ hμ) (hcrit μ hμ)⟩
  · -- minimizer gap: let t → ∞ in the estimate
    intro μ hμ μ' hμ'
    dsimp only
    have hpt := hbound μ μ' hμ hμ'
    have hconv : Tendsto (fun t : ℝ => ‖x μ t - x μ' t‖) atTop (nhds ‖xbar μ - xbar μ'‖) :=
      (((din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
          (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ hμ) (hgrad μ hμ) p q) hβ
          (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ) (hcrit μ hμ)).sub
        (din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
          (fun p q => energyStrong_of_strongConvex (μ := μ') hβ hβγ (hstrong μ' hμ') (hgrad μ' hμ') p q) hβ
          (energyRate_pos hβ hγ (hstrong μ' hμ').1 hβγ) (hcrit μ' hμ')))).norm
    have hlim : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
            Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
          β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
              def_6 r hr (gradφ μ) (gradφ μ')) atTop
        (nhds (β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
          def_6 r hr (gradφ μ) (gradφ μ'))) := by
      have hc : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) :=
        lt_max_of_lt_left (energyRate_pos hβ hγ (hstrong μ hμ).1 hβγ)
      have hexp : Tendsto (fun t : ℝ =>
          Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      have h1 : Tendsto (fun t : ℝ =>
          Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t)) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2)) atTop (nhds 0) := by
        simpa using hexp.mul tendsto_const_nhds
      have h2 : Tendsto (fun t : ℝ =>
          β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) *
            def_6 r hr (gradφ μ) (gradφ μ')) atTop
          (nhds (β * (max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')))⁻¹ * (1 - 0) *
            def_6 r hr (gradφ μ) (gradφ μ'))) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)).mul tendsto_const_nhds)
      simpa using h1.add h2
    refine le_of_tendsto_of_tendsto hconv hlim ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hpt t ht
```

## Proof explanation
The proof begins by constructing a lifted first-order trajectory. The first `have` invokes `dinGradientLift_of_DIN` with the DIN data, $\beta\gt 0$, $1\lt \beta\gamma$, the differential inclusions for $x_\mu$ and $dx_\mu$, the Hessian representation, and the local Lipschitz property of the gradients. This theorem produces

```math
\texttt{hlift}:\mathrm{DINGradientLift}\mathrm{grad}\varphi\,x\,u_0\,v_0\,\beta\,\gamma.
```

Concretely, the lift is a product-valued path $X_\mu(t)=(x_\mu(t),z_\mu(t))$, where the first component is $x_\mu$ and the second is the auxiliary DIN coordinate. The proof of `dinGradientLift_of_DIN` verifies the initial condition, local absolute continuity, and the first-order equation

$$
\dot X_\mu(t)=-F_\mu(X_\mu(t)).
$$

In the main proof, `hlift` is used to apply the comparison and convergence theorems, and `hlift.X a s` denotes the lifted trajectory of index $a$ evaluated at $s$, whose first component is $x_a(s)$.

The proof then establishes the oriented estimate `key`. Fix $a,b\in V$. For $t\ge0$, the proof writes $T=t+1$, so $T\gt 0$ by `linarith`, and applies `din_oriented_comparison` with $c(\mu)=\rho_\mu$, indices $a,b$, and the discrepancy bound

```math
D=\beta\,D_r(\mathrm{grad}\varphi_a,\mathrm{grad}\varphi_b).
```

The strong monotonicity hypothesis required by `din_oriented_comparison` at parameter $b$ is supplied by `energyStrong_of_strongConvex`. That theorem says: if $\varphi_b$ is strongly convex with modulus $\delta_b$, if $\mathrm{grad}\varphi_b$ is its gradient, and if $\beta\gt 0$, $1\lt \beta\gamma$, then for all $p,q\in H\times H$,

```math
\rho_b\left(\|p_1-q_1\|^2+\|p_2-q_2\|^2\right)
\le
\left\langle F_b(p)_1-F_b(q)_1,\ p_1-q_1\right\rangle
+\left\langle F_b(p)_2-F_b(q)_2,\ p_2-q_2\right\rangle.
```

The positivity $\rho_b\gt 0$ is supplied by `energyRate_pos`, using $\beta\gt 0$, $\gamma\gt 0$, $1\lt \beta\gamma$, and $0\lt \delta_b$, which is the first component of the strong-convexity hypothesis. The nonnegativity of $D$ is proved from `def_6_nonneg`, i.e. $D_r(A,B)\ge0$, multiplied by $\beta\ge0$.

The remaining hypothesis of `din_oriented_comparison` is the almost-everywhere bound on the difference of the DIN gradient fields along $X_a$. The proof proves this by using `hball` for the index $a$ and interval $[0,t+1]$. The measure-theoretic rewrite with `MeasureTheory.ae_restrict_iff' measurableSet_Icc` converts the almost-everywhere statement on $[0,\infty)$ into an almost-everywhere statement on the restricted interval $[0,t+1]$: for almost every $s\in[0,t+1]$, $`\|x_a(s)\|\le r`$. Since the first component of$X_a(s)$is$x_a(s)$, this gives$`\|(X_a(s))_1\|\le r`$. The proof then computes the difference of the two DIN gradient fields at the same point$p$:

$$
F_a(p)_1-F_b(p)_1
=\beta\left(\mathrm{grad}\varphi_a(p_1)-\mathrm{grad}\varphi_b(p_1)\right),
\qquad
F_a(p)_2-F_b(p)_2=0.
$$

The first identity is the linear `module` calculation: the terms involving $\sqrt{\gamma-1/\beta}$ and $\sqrt{1/\beta}$ cancel, leaving only the $\beta\mathrm{grad}\varphi$ contribution. The second identity is immediate because the second component of $F_\mu$ does not depend on $\mathrm{grad}\varphi_\mu$. Therefore

```math
\sqrt{\|F_a(p)_1-F_b(p)_1\|^2+\|F_a(p)_2-F_b(p)_2\|^2}
=\beta\|\mathrm{grad}\varphi_a(p_1)-\mathrm{grad}\varphi_b(p_1)\|,
```

using `norm_smul` and $`\|\beta z\|=\beta\|z\|`$because$\beta>0$. Now `le_def_6` applies: since the discrepancy set for $\mathrm{grad}\varphi_a$ and $\mathrm{grad}\varphi_b$ is bounded above by `hbdd a ha b hb`, and since $`\|p_1\|\le r`$, it gives

```math
\|\mathrm{grad}\varphi_a(p_1)-\mathrm{grad}\varphi_b(p_1)\|
\le D_r(\mathrm{grad}\varphi_a,\mathrm{grad}\varphi_b).
```

Multiplying by $\beta\ge0$ yields the required bound by $D$. Hence `din_oriented_comparison` gives, for every $t\ge0$,

```math
\|x_a(t)-x_b(t)\|
\le e^{-\rho_b t}
\sqrt{\|u_0(a)-u_0(b)\|^2+\|z_{0,a}-z_{0,b}\|^2}
+\rho_b^{-1}(1-e^{-\rho_b t})
\beta D_r(\mathrm{grad}\varphi_a,\mathrm{grad}\varphi_b).
```

This is the lemma `key`.

Next the proof symmetrizes this estimate into `hbound`, replacing $\rho_b$ by

$$
c_{a,b}=\max(\rho_a,\rho_b).
$$

Two cases are separated by `by_cases`. If $\rho_a\le\rho_b$, then $c_{a,b}=\rho_b$, and the oriented estimate `key a b` already has the correct exponential rate; `rw [max_eq_right hc]` and `ring` normalize the algebraic form. If $\rho_b\le\rho_a$, the proof first uses $`\|x_a(t)-x_b(t)\|=\|x_b(t)-x_a(t)\|`$, then applies `key b a`. After swapping $a$ and $b$, it uses symmetry of norms for the initial terms, and `def_6_comm`, which states

$$
D_r(A,B)=D_r(B,A),
$$

to replace $D_r(\mathrm{grad}\varphi_b,\mathrm{grad}\varphi_a)$ by $D_r(\mathrm{grad}\varphi_a,\mathrm{grad}\varphi_b)$. Since now $c_{a,b}=\rho_a$, `ring` again puts the expression into the desired form. Thus for all $t\ge0$,

```math
\|x_a(t)-x_b(t)\|
\le e^{-c_{a,b}t}
\sqrt{\|u_0(a)-u_0(b)\|^2+\|z_{0,a}-z_{0,b}\|^2}
+\beta c_{a,b}^{-1}(1-e^{-c_{a,b}t})
D_r(\mathrm{grad}\varphi_a,\mathrm{grad}\varphi_b).
```

The final triple conjunction is now proved. For the first conjunct, fix $\mu,\mu'\in V$. The proof uses `Filter.Eventually.of_forall` to upgrade the pointwise estimate `hbound` to an almost-everywhere statement. If $t\in[0,T]$, then $t\ge0$, so `hbound` applies. Thus the first estimate holds; in fact the proof establishes it for every $t\ge0$, which is stronger than the stated almost-everywhere implication on $[0,T]$.

For the second conjunct, fix $\mu\in V$. The proof invokes `din_tendsto_to_critical` with $c(\mu)=\rho_\mu$, the lift `hlift`, strong monotonicity of $F_\mu$ supplied by `energyStrong_of_strongConvex`, $\beta\gt 0$, positivity of $\rho_\mu$ from `energyRate_pos`, and the critical-point hypothesis $\mathrm{grad}\varphi_\mu(\bar x_\mu)=0$. Its conclusion is

$$
x_\mu(t)\to \bar x_\mu\quad\text{as }t\to\infty.
$$

Then it invokes `mem_argminSet_of_grad_eq_zero`. That theorem says: if $\varphi_\mu$ is strongly convex, $\mathrm{grad}\varphi_\mu$ is its gradient, and $\mathrm{grad}\varphi_\mu(\bar x_\mu)=0$, then $\bar x_\mu$ belongs to the argmin set of $\varphi_\mu$. Thus $\bar x_\mu$ is a minimizer. The two conclusions are paired into the required conjunction.

For the third conjunct, fix $\mu,\mu'\in V$, and let

$$
c=\max(\rho_\mu,\rho_{\mu'}).
$$

The pointwise estimate `hbound` gives, for every $t\ge0$,

```math
\|x_\mu(t)-x_{\mu'}(t)\|
\le
E(t)
```

where

```math
E(t)=
e^{-ct}
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|z_{0,\mu}-z_{0,\mu'}\|^2}
+\beta c^{-1}(1-e^{-ct})
D_r(\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
```

The proof then lets $t\to\infty$. First, `din_tendsto_to_critical` for $\mu$ and $\mu'$ gives $x_\mu(t)\to\bar x_\mu$ and $x_{\mu'}(t)\to\bar x_{\mu'}$. By continuity of subtraction and of the norm, the scalar function

```math
t\mapsto \|x_\mu(t)-x_{\mu'}(t)\|
```

converges to $`\|\bar x_\mu-\bar x_{\mu'}\|`$. This is `hconv`.

Second, the right-hand side $E(t)$ converges to

$$
\beta c^{-1}D_r(\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}).
$$

The proof shows $c\gt 0$ using `lt_max_of_lt_left` and `energyRate_pos`. Since $c\gt 0$, the map $t\mapsto ct$ tends to $+\infty$, so

$$
e^{-ct}\to0
$$

by `Real.tendsto_exp_neg_atTop_nhds_zero` composed with `tendsto_id.const_mul_atTop hc`. Therefore the first term of $E(t)$, which is a constant times $e^{-ct}$, tends to $0$. The second term tends to $\beta c^{-1}(1-0)D_r$, because $e^{-ct}\to0$ and all other factors are constant. Adding these limits gives the limit of $E(t)$. This is `hlim`.

Finally, the proof applies `le_of_tendsto_of_tendsto`: if two scalar functions converge to limits $L$ and $R$, and one is eventually at most the other, then $L\le R$. The eventual inequality is supplied by `hbound`, which holds for all $t\ge0$, hence eventually in $t$. Therefore

```math
\|\bar x_\mu-\bar x_{\mu'}\|
\le
\beta c^{-1}
D_r(\mathrm{grad}\varphi_\mu,\mathrm{grad}\varphi_{\mu'}),
```

which is exactly the third conjunct.

