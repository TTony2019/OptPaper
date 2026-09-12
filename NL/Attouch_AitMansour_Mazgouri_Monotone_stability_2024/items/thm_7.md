## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_7.lean`

## Lean statement
```lean
theorem thm_7 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (xbar : M → H)
    (β γ : ℝ) (δ : M → ℝ) (cmin k₁ γ₁ : ℝ) (μbar : M)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hcmin_pos : 0 < cmin) (hcmin : ∀ μ : M, cmin ≤ energyRate β γ (δ μ))
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ : M,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ : M,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hcrit : ∀ μ : M, gradφ μ (xbar μ) = 0)
    (hlyap : ∀ ε > 0, ∃ η > 0,
      ‖u₀ μbar - xbar μbar‖ < η ∧ ‖v₀ μbar‖ < η ∧
      ∀ z₀ w₀ : H, ‖z₀ - xbar μbar‖ < η → ‖w₀‖ < η →
        ∀ z dz ddz : ℝ → H,
          DIN (φ μbar) (gradφ μbar) (hessφ μbar) γ β z₀ w₀ z dz ddz →
          (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt z (dz t) t) →
          ∀ t ≥ 0, ‖z t - xbar μbar‖ < ε)
    (hconv_init : Tendsto (fun μ : M => (u₀ μ, dinAuxInitial gradφ β γ u₀ v₀ μ))
      (nhds μbar) (nhds (u₀ μbar, dinAuxInitial gradφ β γ u₀ v₀ μbar))) :
    (∀ ε > 0, ∃ δ > 0, ∀ μ : M, dist μ μbar < δ → ‖u₀ μ - xbar μbar‖ < δ →
      ∀ t ≥ 0, ‖x μ t - xbar μbar‖ < ε) ∧
    ((∀ μ : M, u₀ μ = u₀ μbar ∧ v₀ μ = v₀ μbar) →
      ∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ)) ∧
        ‖xbar μ - xbar μbar‖ ≤ (β * k₁ / cmin) * dist μ μbar ^ γ₁)
```

## Statement explanation
The theorem `thm_7` concerns a parameterized family of trajectories satisfying a DIN-type second-order equation and gives two stability conclusions: uniform local Lyapunov stability near a base parameter, and asymptotic convergence plus Hölder dependence of the limiting critical points.

The ambient types are $H$ and $M$. Here $H$ is a real inner product space and is complete, while $M$ is a normed additive commutative group. The parameter variable lives in $M$, and the state variable lives in $H$.

The data are:

- $\phi : M \to H \to \mathbb R$, a family of functions $\phi_\mu : H \to \mathbb R$.
- $\mathrm{grad}\phi : M \to H \to H$, where $\mathrm{grad}\phi(\mu,q)$ is intended to be the gradient of $\phi_\mu$ at $q$.
- $\mathrm{hess}\phi : M \to H \to H \to H$, where $\mathrm{hess}\phi(\mu,q)(v)$ is intended to be the Hessian action of $\phi_\mu$ at $q$ on $v$.
- $x,dx,ddx : M \to \mathbb R \to H$, representing for each parameter $\mu$ the trajectory, its first derivative, and its second derivative.
- $u_0,v_0 : M \to H$, the initial position and initial velocity for each $\mu$.
- $\bar x : M \to H$, a family of candidate critical points.
- $\beta,\gamma \in \mathbb R$, parameters in the DIN equation.
- $\delta : M \to \mathbb R$, the strong convexity modulus of $\phi_\mu$.
- $c_{\min},k_1,\gamma_1 \in \mathbb R$, constants controlling a lower bound on the decay rate, the Hölder constant of the parameter dependence of the gradient, and the Hölder exponent.
- $\bar\mu \in M$, the base parameter.

The assumptions are:

- $\beta\gamma\gt 1$, $\beta\gt 0$, and $\gamma\gt 0$.
- $c_{\min}\gt 0$, and for every $\mu$,

$$
c_{\min} \le \mathrm{energyRate}(\beta,\gamma,\delta(\mu)).
$$

Here

$$
\mathrm{energyRate}(\beta,\gamma,\delta)
=\frac{(\beta\delta+\gamma)-\sqrt{(\beta\delta+\gamma)^2-4\delta}}{2}.
$$

- For every $\mu$, $\phi_\mu$ is differentiable on $H$.
- For every $\mu$ and every $q\in H$, $\mathrm{grad}\phi(\mu,q)$ is a gradient of $\phi_\mu$ at $q$.
- For every $\mu$, $\phi_\mu$ is strongly convex with modulus $\delta(\mu)$.
- $k_1\gt 0$, $0\lt \gamma_1$, and $\gamma_1\le 1$.
- For every $\mu$, the triple $(x(\mu),dx(\mu),ddx(\mu))$ satisfies the DIN system

$$
\mathrm{DIN}(\phi_\mu,\mathrm{grad}\phi_\mu,
 \mathrm{hess}\phi_\mu,\gamma,\beta,
 u_0(\mu),v_0(\mu),x(\mu),dx(\mu),ddx(\mu)).
$$

As used in the proof, this packages the initial conditions

$$
x(\mu,0)=u_0(\mu),\qquad dx(\mu,0)=v_0(\mu),
$$

absolute continuity on compact intervals, and almost everywhere the second-order equation

```math
ddx(\mu,t)+\gamma\,dx(\mu,t)
+\beta\,\mathrm{hess}\phi_\mu(x(\mu,t))(dx(\mu,t))
+\mathrm{grad}\phi_\mu(x(\mu,t))=0.
```

- For every $\mu$, almost every $t\in[0,\infty)$,

$$
\mathrm{HasDerivAt}(x(\mu),dx(\mu,t),t),
$$

and almost every $t\in[0,\infty)$,

$$
\mathrm{HasDerivAt}(dx(\mu),ddx(\mu,t),t).
$$

- For every $\mu$ and every $q\in H$, there exists a continuous linear map $L:H\to H$ such that $L$ is the Fréchet derivative of $\mathrm{grad}\phi_\mu$ at $q$, and for every $v$,

$$
L(v)=\mathrm{hess}\phi_\mu(q)(v).
$$

Thus $\mathrm{hess}\phi_\mu(q)$ is the derivative of the gradient map.
- For every $\mu$ and every $T'\gt 0$, the map $\mathrm{grad}\phi_\mu$ is Lipschitz on the image $x(\mu)([0,T'])$.
- For every $x_0\in H$ and all $\mu,\mu'\in M$,

```math
\|\mathrm{grad}\phi_\mu(x_0)-\mathrm{grad}\phi_{\mu'}(x_0)\|
\le k_1\,\|\mu-\mu'\|^{\gamma_1}.
```

So the gradient depends Hölder continuously on the parameter.
- For every $\mu$,

$$
\mathrm{grad}\phi_\mu(\bar x(\mu))=0.
$$

Thus each $\bar x(\mu)$ is a critical point.
- The Lyapunov hypothesis `hlyap` says: for every $\varepsilon\gt 0$ there exists $\eta\gt 0$ such that

```math
\|u_0(\bar\mu)-\bar x(\bar\mu)\|<\eta,\qquad \|v_0(\bar\mu)\|<\eta,
```

and for every $z_0,w_0\in H$ satisfying

```math
\|z_0-\bar x(\bar\mu)\|<\eta,\qquad \|w_0\|<\eta,
```

and every DIN trajectory $z,dz,ddz$ for the base parameter $\bar\mu$, if $z$ has derivative $dz$ almost everywhere on $[0,\infty)$, then for every $t\ge 0$,

```math
\|z(t)-\bar x(\bar\mu)\|<\varepsilon.
```

This is a local Lyapunov stability assumption at the base parameter.
- The initial-continuity hypothesis `hconv_init` says that the lifted initial data map

$$
\mu\mapsto
\bigl(u_0(\mu),\mathrm{dinAuxInitial}(\mathrm{grad}\phi,\beta,\gamma,u_0,v_0,\mu)\bigr)
$$

is continuous at $\bar\mu$. Here

```math
\mathrm{dinAuxInitial}(\mathrm{grad}\phi,\beta,\gamma,u_0,v_0,\mu)
=-\left(\sqrt{(\gamma-1/\beta)(1/\beta)}\right)^{-1}
\bigl(v_0(\mu)+\beta\,\mathrm{grad}\phi_\mu(u_0(\mu))
+(\gamma-1/\beta)u_0(\mu)\bigr).
```

The conclusion is a conjunction of two statements.

First, for every $\varepsilon\gt 0$ there exists $\delta\gt 0$ such that for every $\mu\in M$, if

```math
\mathrm{dist}(\mu,\bar\mu)<\delta
\quad\text{and}\quad
\|u_0(\mu)-\bar x(\bar\mu)\|<\delta,
```

then for every $t\ge 0$,

```math
\|x(\mu,t)-\bar x(\bar\mu)\|<\varepsilon.
```

So trajectories with nearby parameters and nearby initial positions remain uniformly close to the base critical point. In the proof, the second smallness condition on $u_0(\mu)$ is actually not used.

Second, if the initial data are independent of $\mu$, in the sense that for every $\mu$,

$$
u_0(\mu)=u_0(\bar\mu),\qquad v_0(\mu)=v_0(\bar\mu),
$$

then for every $\mu$,

$$
\mathrm{Tendsto}(x(\mu),\mathrm{atTop},\mathrm{nhds}(\bar x(\mu))),
$$

meaning

$$
x(\mu,t)\to \bar x(\mu)\qquad (t\to\infty),
$$

and in addition

```math
\|\bar x(\mu)-\bar x(\bar\mu)\|
\le
\frac{\beta k_1}{c_{\min}}\,\mathrm{dist}(\mu,\bar\mu)^{\gamma_1}.
```

Thus the limiting critical point depends Hölder continuously on the parameter with exponent $\gamma_1$.

## Lean proof
```lean
by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  constructor
  · -- (i) Lyapunov uniform μ̄-stability, by the paper's argument
    intro ε hε
    obtain ⟨η, hη_pos, hbase_u, hbase_v, htraj⟩ := hlyap (ε / 3) (by positivity)
    have hε₁ : 0 < ε / (3 * Real.sqrt 2) := by positivity
    have hev : ∀ᶠ μ in nhds μbar,
        dist (u₀ μ, dinAuxInitial gradφ β γ u₀ v₀ μ)
          (u₀ μbar, dinAuxInitial gradφ β γ u₀ v₀ μbar) < ε / (3 * Real.sqrt 2) :=
      (Metric.tendsto_nhds.mp hconv_init) _ hε₁
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hev
    -- stability radius enforcing the Hölder term of (17) to be < ε/3
    set δrate : ℝ := min 1 (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) with hδrate_def
    have hr_pos : 0 < ((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hδrate_pos : 0 < δrate := lt_min one_pos hr_pos
    have hrate : (β * k₁ / cmin) * δrate ^ γ₁ ≤ ε / 3 := by
      have hle : δrate ≤ ((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁) := min_le_right _ _
      have hpow : δrate ^ γ₁ ≤ (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) ^ γ₁ :=
        Real.rpow_le_rpow hδrate_pos.le hle hγ₁_pos.le
      have hval : (((ε * cmin) / (3 * β * k₁)) ^ (1 / γ₁)) ^ γ₁ = (ε * cmin) / (3 * β * k₁) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (ε * cmin) / (3 * β * k₁))]
        rw [one_div_mul_cancel hγ₁_pos.ne', Real.rpow_one]
      calc (β * k₁ / cmin) * δrate ^ γ₁ ≤ (β * k₁ / cmin) * ((ε * cmin) / (3 * β * k₁)) := by
            rw [← hval]
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ε / 3 := by
            field_simp [hcmin_pos.ne', hk₁.ne', hβ.ne']
    refine ⟨min (min δ₁ η) δrate, lt_min (lt_min hδ₁_pos hη_pos) hδrate_pos, ?_⟩
    intro μ hμ _ t ht
    have hμ₁ : dist μ μbar < δ₁ :=
      lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hμη : dist μ μbar < η :=
      lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hμrate : dist μ μbar < δrate := lt_of_lt_of_le hμ (min_le_right _ _)
    -- the μ̄-trajectory stays within ε/3 of x̄
    have href : ‖x μbar t - xbar μbar‖ < ε / 3 :=
      htraj (u₀ μbar) (v₀ μbar) hbase_u hbase_v (x μbar) (dx μbar) (ddx μbar)
        (hDIN μbar) (hderiv μbar) t ht
    -- the (transformed) initial data of the two trajectories are ε/3-close
    have hinit : Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
          ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) < ε / 3 := by
      have hdist := hδ₁ (show dist μ μbar < δ₁ from hμ₁)
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hdist
      set m : ℝ := max ‖u₀ μ - u₀ μbar‖
        ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ with hm_def
      have hm_nonneg : 0 ≤ m :=
        le_trans (norm_nonneg _) (le_max_left _ _)
      have hsqrt : Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) ≤
          Real.sqrt 2 * m := by
        rw [← Real.sqrt_sq hm_nonneg, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        apply Real.sqrt_le_sqrt
        rw [hm_def]
        nlinarith [le_max_left ‖u₀ μ - u₀ μbar‖
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖,
          le_max_right ‖u₀ μ - u₀ μbar‖
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖,
          norm_nonneg (u₀ μ - u₀ μbar),
          norm_nonneg (dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar)]
      have hm : m < ε / (3 * Real.sqrt 2) := hdist
      have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      calc Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 +
            ‖dinAuxInitial gradφ β γ u₀ v₀ μ - dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2)
          ≤ Real.sqrt 2 * m := hsqrt
        _ < Real.sqrt 2 * (ε / (3 * Real.sqrt 2)) := by
            exact mul_lt_mul_of_pos_left hm hsqrt2
        _ = ε / 3 := by
            field_simp
    -- Theorem 6.1's estimate, with the exponential terms bounded by 1
    have hexp_le : Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h1 : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar)) :=
        lt_of_lt_of_le hcmin_pos (le_trans (hcmin μ) (le_max_left _ _))
      nlinarith
    have hone : 1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) ≤ 1 := by
      linarith [Real.exp_nonneg (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)]
    have hrpow : 0 ≤ ‖μ - μbar‖ ^ γ₁ := Real.rpow_nonneg (norm_nonneg _) _
    have hest := thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ
      hdiff hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μbar t ht
    have hterm1 : Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) *
        Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) ≤
        Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) :=
      mul_le_of_le_one_left (Real.sqrt_nonneg _) hexp_le
    have hterm2 : (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
            ‖μ - μbar‖ ^ γ₁ ≤
        (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := by
      have h1 : (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) ≤
          (β * k₁ / cmin) * 1 :=
        mul_le_mul
          (div_le_div_of_nonneg_left (by positivity) hcmin_pos (le_trans (hcmin μ) (le_max_left _ _)))
          hone (sub_nonneg.mpr hexp_le) (div_nonneg (by positivity) hcmin_pos.le)
      calc (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
            ‖μ - μbar‖ ^ γ₁
          ≤ (β * k₁ / cmin) * 1 * ‖μ - μbar‖ ^ γ₁ := mul_le_mul_of_nonneg_right h1 hrpow
        _ = (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := by ring
    have hfirst : ‖x μ t - x μbar t‖ < ε / 3 + ε / 3 := by
      have h2 : (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ ≤ (β * k₁ / cmin) * δrate ^ γ₁ :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _)
            (show ‖μ - μbar‖ ≤ δrate by rw [← dist_eq_norm]; exact hμrate.le) hγ₁_pos.le)
          (by positivity)
      calc ‖x μ t - x μbar t‖ ≤
            Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t) *
              Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
                dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) +
          (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) *
            (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * t)) *
              ‖μ - μbar‖ ^ γ₁ := hest
        _ ≤ Real.sqrt (‖u₀ μ - u₀ μbar‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
              dinAuxInitial gradφ β γ u₀ v₀ μbar‖ ^ 2) +
            (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ := add_le_add hterm1 hterm2
        _ < ε / 3 + ε / 3 := by
            linarith [hinit, h2, hrate]
    have htri : ‖x μ t - xbar μbar‖ ≤
        ‖x μ t - x μbar t‖ + ‖x μbar t - xbar μbar‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x μ t) (x μbar t) (xbar μbar)
    have hsum := add_lt_add hfirst href
    linarith
  · -- (ii) asymptotic μ̄-stability in the corrected form
    intro _ μ
    refine ⟨din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
      (fun p q => energyStrong_of_strongConvex hβ hβγ (hstrong μ) (hgrad μ) p q) hβ
      (energyRate_pos hβ hγ (hstrong μ).1 hβγ) (hcrit μ), ?_⟩
    have hgap := (thm_6 φ gradφ hessφ x dx ddx u₀ v₀ xbar β γ δ k₁ γ₁ hβγ hβ hγ hdiff
      hgrad hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 hcrit).2.2 μ μbar
    have hcoef : β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar)) ≤ β * k₁ / cmin :=
      div_le_div_of_nonneg_left (by positivity) hcmin_pos (le_trans (hcmin μ) (le_max_left _ _))
    calc ‖xbar μ - xbar μbar‖ ≤
          (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μbar))) * ‖μ - μbar‖ ^ γ₁ := hgap
      _ ≤ (β * k₁ / cmin) * ‖μ - μbar‖ ^ γ₁ :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (β * k₁ / cmin) * dist μ μbar ^ γ₁ := by rw [dist_eq_norm]
```

## Proof explanation
The proof begins by constructing the lifted first-order formulation. It calls `dinGradientLift_of_DIN` with the hypotheses $\beta\gt 0$, $\beta\gamma\gt 1$, the DIN assumptions for all $\mu$, the almost everywhere derivative assumptions, the Hessian assumption, and the local Lipschitz assumption. The result is

$$
\mathrm{DINGradientLift}(\mathrm{grad}\phi,x,u_0,v_0,\beta,\gamma).
$$

The mathematical content is that the second-order DIN trajectory $x(\mu)$ can be paired with an auxiliary coordinate

$$
z(\mu,t)
=\mathrm{dinAux}(\mathrm{grad}\phi,\beta,\gamma,x,dx,\mu,t)
$$

so that the pair $(x(\mu,t),z(\mu,t))$ solves a first-order gradient flow with field

$$
\mathrm{DINGradientField}(\mathrm{grad}\phi,\beta,\gamma,\mu).
$$

The initial value of this lifted pair is

$$
(u_0(\mu),\mathrm{dinAuxInitial}(\mathrm{grad}\phi,\beta,\gamma,u_0,v_0,\mu)).
$$

The proof of `dinGradientLift_of_DIN` verifies three things: the lifted initial condition, absolute continuity on compact intervals, and the first-order differential equation almost everywhere. The assumptions $\beta\gt 0$ and $\beta\gamma\gt 1$ ensure $\gamma-1/\beta\gt 0$ and $1/\beta\gt 0$, so the square roots appearing in the auxiliary coordinate are real and positive.

Then `constructor` splits the conclusion into the two main parts.

For the first part, the proof fixes $\varepsilon\gt 0$. It applies the Lyapunov hypothesis `hlyap` with $\varepsilon/3$. This produces an $\eta\gt 0$, smallness of the base initial data,

```math
\|u_0(\bar\mu)-\bar x(\bar\mu)\|<\eta,\qquad
\|v_0(\bar\mu)\|<\eta,
```

and the trajectory bound

```math
\|x(\bar\mu,t)-\bar x(\bar\mu)\|<\varepsilon/3
```

for every $t\ge 0$, applied to the base DIN trajectory.

Next, the proof uses `hconv_init`, the continuity at $\bar\mu$ of the lifted initial data. The Tendsto statement is converted, via the metric characterization of convergence in a neighborhood filter, into the existence of a radius $\delta_1\gt 0$ such that if

$$
\mathrm{dist}(\mu,\bar\mu)<\delta_1,
$$

then

```math
\mathrm{dist}\!\left(
(u_0(\mu),\mathrm{dinAuxInitial}(\ldots,\mu)),
(u_0(\bar\mu),\mathrm{dinAuxInitial}(\ldots,\bar\mu))
\right)
<
\frac{\varepsilon}{3\sqrt2}.
```

This controls the difference of the lifted initial data for $\mu$ and $\bar\mu$.

The proof then defines

$$
\delta_{\mathrm{rate}}
=\min\left(1,
\left(\frac{\varepsilon c_{\min}}{3\beta k_1}\right)^{1/\gamma_1}
\right).
$$

Its purpose is to make the parameter-perturbation term smaller than $\varepsilon/3$. Since $\gamma_1\gt 0$, the real-power monotonicity and the identity

$$
\left(a^{1/\gamma_1}\right)^{\gamma_1}=a
$$

give

```math
\frac{\beta k_1}{c_{\min}}\,\delta_{\mathrm{rate}}^{\gamma_1}
\le
\frac{\varepsilon}{3}.
```

The positivity of $\delta_{\mathrm{rate}}$ follows from $c_{\min}\gt 0$, $k_1\gt 0$, $\beta\gt 0$, and $\varepsilon\gt 0$.

The final stability radius is chosen as

$$
\delta=\min(\min(\delta_1,\eta),\delta_{\mathrm{rate}}).
$$

Now fix $\mu$ with $\mathrm{dist}(\mu,\bar\mu)\lt \delta$, and fix $t\ge 0$. The proof obtains

$$
\mathrm{dist}(\mu,\bar\mu)<\delta_1,\qquad
\mathrm{dist}(\mu,\bar\mu)<\eta,\qquad
\mathrm{dist}(\mu,\bar\mu)<\delta_{\mathrm{rate}}.
$$

The base trajectory bound gives

```math
\|x(\bar\mu,t)-\bar x(\bar\mu)\|<\varepsilon/3.
```

The initial lifted distance is then controlled. From the choice of $\delta_1$,

```math
\mathrm{dist}\!\left(
(u_0(\mu),\mathrm{dinAuxInitial}(\ldots,\mu)),
(u_0(\bar\mu),\mathrm{dinAuxInitial}(\ldots,\bar\mu))
\right)
<
\frac{\varepsilon}{3\sqrt2}.
```

The product distance is rewritten using the product metric and the norm. If

```math
m=
\max\left(
\|u_0(\mu)-u_0(\bar\mu)\|,
\|\mathrm{dinAuxInitial}(\ldots,\mu)
-\mathrm{dinAuxInitial}(\ldots,\bar\mu)\|
\right),
```

then

```math
\sqrt{
\|u_0(\mu)-u_0(\bar\mu)\|^2
+\|\mathrm{dinAuxInitial}(\ldots,\mu)
-\mathrm{dinAuxInitial}(\ldots,\bar\mu)\|^2
}
\le
\sqrt2\,m.
```

Since $m\lt \varepsilon/(3\sqrt2)$, this yields

```math
\sqrt{
\|u_0(\mu)-u_0(\bar\mu)\|^2
+\|\mathrm{dinAuxInitial}(\ldots,\mu)
-\mathrm{dinAuxInitial}(\ldots,\bar\mu)\|^2
}
<
\frac{\varepsilon}{3}.
```

The proof then applies `thm_5_estimate_all` to the two parameters $\mu$ and $\bar\mu$. The exact consequence used is the estimate

```math
\begin{aligned}
\|x(\mu,t)-x(\bar\mu,t)\|
&\le
e^{-M t}
\sqrt{
\|u_0(\mu)-u_0(\bar\mu)\|^2
+\|z_0(\mu)-z_0(\bar\mu)\|^2
}\\
&\quad
+\frac{\beta k_1}{M}
\left(1-e^{-M t}\right)
\|\mu-\bar\mu\|^{\gamma_1},
\end{aligned}
```

where

$$
M=
\max\left(
\mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
\mathrm{energyRate}(\beta,\gamma,\delta(\bar\mu))
\right),
$$

and

$$
z_0(\mu)=
\mathrm{dinAuxInitial}(\mathrm{grad}\phi,\beta,\gamma,u_0,v_0,\mu).
$$

This estimate is the quantitative stability comparison between the two DIN trajectories.

The proof bounds the first term using $e^{-Mt}\le 1$, which follows because $M\gt 0$ and $t\ge 0$. Hence the exponential factor is at most $1$, and the first term is at most the initial lifted distance, already shown to be $\lt \varepsilon/3$.

For the second term, the proof uses the lower bound on the decay rates. Since

$$
c_{\min}\le \mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
$$

and $M$ is the maximum of this quantity and the corresponding quantity for $\bar\mu$, we have $c_{\min}\le M$. Therefore

$$
\frac{\beta k_1}{M}\le \frac{\beta k_1}{c_{\min}}.
$$

Also $0\le 1-e^{-Mt}\le 1$. Thus the second term is at most

```math
\frac{\beta k_1}{c_{\min}}\|\mu-\bar\mu\|^{\gamma_1}.
```

Since $\mathrm{dist}(\mu,\bar\mu)\lt \delta_{\mathrm{rate}}$, monotonicity of the real power gives

```math
\|\mu-\bar\mu\|^{\gamma_1}
<
\delta_{\mathrm{rate}}^{\gamma_1},
```

and the choice of $\delta_{\mathrm{rate}}$ gives

```math
\frac{\beta k_1}{c_{\min}}\|\mu-\bar\mu\|^{\gamma_1}
<
\frac{\varepsilon}{3}.
```

Combining the two bounds yields

```math
\|x(\mu,t)-x(\bar\mu,t)\|
<
\frac{\varepsilon}{3}+\frac{\varepsilon}{3}.
```

Finally the triangle inequality gives

```math
\|x(\mu,t)-\bar x(\bar\mu)\|
\le
\|x(\mu,t)-x(\bar\mu,t)\|
+\|x(\bar\mu,t)-\bar x(\bar\mu)\|.
```

The first summand is $\lt 2\varepsilon/3$, and the second is $\lt \varepsilon/3$, so the total is $\lt \varepsilon$. This proves the first conclusion. The tactic `linarith` is used here to combine these linear inequalities.

For the second part, the proof ignores the hypothesis that the initial data are independent of $\mu$, because the argument below proves the convergence assertion for each $\mu$ directly. For a fixed $\mu$, the proof applies `din_tendsto_to_critical` with the decay rate

$$
c(\mu)=\mathrm{energyRate}(\beta,\gamma,\delta(\mu)).
$$

The required strong monotonicity of the lifted field is supplied by `energyStrong_of_strongConvex`. That result uses strong convexity of $\phi_\mu$ with modulus $\delta(\mu)$ and the gradient hypothesis to prove that the lifted field

$$
F_\mu=\mathrm{DINGradientField}(\mathrm{grad}\phi,\beta,\gamma,\mu)
$$

satisfies, for all $p,q\in H\times H$,

```math
\mathrm{energyRate}(\beta,\gamma,\delta(\mu))
\left(
\|p_1-q_1\|^2+\|p_2-q_2\|^2
\right)
\le
\left\langle F_\mu(p)_1-F_\mu(q)_1,p_1-q_1\right\rangle
+\left\langle F_\mu(p)_2-F_\mu(q)_2,p_2-q_2\right\rangle.
```

This is exactly the strong monotonicity needed by `din_tendsto_to_critical`. The positivity of the constant is supplied by `energyRate_pos`, using $\beta\gt 0$, $\gamma\gt 0$, $\delta(\mu)\gt 0$, and $\beta\gamma\gt 1$. The critical-point condition is `hcrit μ`,

$$
\mathrm{grad}\phi_\mu(\bar x(\mu))=0.
$$

Thus `din_tendsto_to_critical` gives

$$
x(\mu,t)\to \bar x(\mu)\qquad (t\to\infty).
$$

Finally, the proof needs the estimate comparing $\bar x(\mu)$ and $\bar x(\bar\mu)$. It invokes `thm_6`, whose conclusion includes, among other facts, the Hölder estimate

```math
\|\bar x(\mu)-\bar x(\mu')\|
\le
\frac{\beta k_1}{
\max\left(
\mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
\mathrm{energyRate}(\beta,\gamma,\delta(\mu'))
\right)}
\|\mu-\mu'\|^{\gamma_1}.
```

Applying the third conjunct of `thm_6` to $\mu$ and $\bar\mu$ gives

```math
\|\bar x(\mu)-\bar x(\bar\mu)\|
\le
\frac{\beta k_1}{
\max\left(
\mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
\mathrm{energyRate}(\beta,\gamma,\delta(\bar\mu))
\right)}
\|\mu-\bar\mu\|^{\gamma_1}.
```

Since

$$
c_{\min}\le \mathrm{energyRate}(\beta,\gamma,\delta(\mu))
\le
\max\left(
\mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
\mathrm{energyRate}(\beta,\gamma,\delta(\bar\mu))
\right),
$$

the denominator is at least $c_{\min}$, so

$$
\frac{\beta k_1}{
\max\left(
\mathrm{energyRate}(\beta,\gamma,\delta(\mu)),
\mathrm{energyRate}(\beta,\gamma,\delta(\bar\mu))
\right)}
\le
\frac{\beta k_1}{c_{\min}}.
$$

Multiplying by the nonnegative factor $`\|\mu-\bar\mu\|^{\gamma_1}`$ yields

```math
\|\bar x(\mu)-\bar x(\bar\mu)\|
\le
\frac{\beta k_1}{c_{\min}}
\|\mu-\bar\mu\|^{\gamma_1}.
```

The final rewrite uses $`\mathrm{dist}(\mu,\bar\mu)=\|\mu-\bar\mu\|`$, giving the stated estimate with$\mathrm{dist}(\mu,\bar\mu)^{\gamma_1}$.

