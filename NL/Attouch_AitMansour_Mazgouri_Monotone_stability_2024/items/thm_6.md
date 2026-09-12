## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_6.lean`

## Lean statement
```lean
theorem thm_6 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (xbar : M → H)
    (β γ : ℝ) (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hcrit : ∀ μ : M, gradφ μ (xbar μ) = 0) :
    (∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ))) ∧
    (∀ μ : M, xbar μ ∈ Optimization.argminSet (φ μ)) ∧
    (∀ μ μ' : M, let cmax := max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))
      ‖xbar μ - xbar μ'‖ ≤ (β * k₁ / cmax) * ‖μ - μ'‖ ^ γ₁)
```

## Statement explanation
The declaration `thm_6` is a parameter-stability theorem for a family of DIN gradient systems. Let $H$ be a real Hilbert space and let $M$ be a normed additive commutative group, used as the parameter space. The data consist of a family of functions

$$
\varphi_\mu:H\to\mathbb R,\qquad \mu\in M,
$$

with gradient field

$$
\mathrm{grad}\varphi_\mu:H\to H,
$$

and Hessian action

$$
\mathrm{hess}\varphi_\mu:H\to H\to H.
$$

For each parameter $\mu$, the functions

$$
x_\mu,\ dx_\mu,\ ddx_\mu:\mathbb R\to H
$$

are the position, velocity, and acceleration of a DIN trajectory. The functions $u_0,v_0:M\to H$ give the initial position and velocity, and $\bar x:M\to H$ is a parameter-dependent candidate critical point.

The real parameters are $\beta,\gamma,\delta(\mu),k_1,\gamma_1$. The assumptions are $\beta>0$, $\gamma>0$, $\beta\gamma>1$, $k_1>0$, $0<\gamma_1\le 1$. The function $\delta:M\to\mathbb R$ is the strong-convexity modulus: each $\varphi_\mu$ is assumed strongly convex with modulus $\delta(\mu)$. The strong-convexity hypothesis also supplies the positivity $\delta(\mu)>0$, which is used later. The hypotheses `hdiff` and `hgrad` say that each $\varphi_\mu$ is differentiable and that $\mathrm{grad}\varphi_\mu(q)$ is its gradient at $q$. The hypothesis `hhess` says that $\mathrm{hess}\varphi_\mu(q)$ is the Fréchet derivative of $\mathrm{grad}\varphi_\mu$ at $q$, acting on vectors. The hypothesis `hlip` says that for each $\mu$ and each positive time horizon $T'$, the gradient $\mathrm{grad}\varphi_\mu$ is Lipschitz on the image of $x_\mu$ over the compact interval between $0$ and $T'$.

The central dynamical assumption is

$$
\text{`hDIN`}:\quad \forall \mu,\ \mathrm{DIN}(\varphi_\mu,\mathrm{grad}\varphi_\mu,\mathrm{hess}\varphi_\mu,\gamma,\beta,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu).
$$

This packages the second-order DIN system for the family. In the proof it is used through the initial conditions $x_\mu(0)=u_0(\mu)$, $dx_\mu(0)=v_0(\mu)$, local absolute continuity, and the almost-everywhere ordinary differential equation

$$
ddx_\mu(t)+\gamma\,dx_\mu(t)+\beta\,\mathrm{hess}\varphi_\mu(x_\mu(t))(dx_\mu(t))
+\mathrm{grad}\varphi_\mu(x_\mu(t))=0.
$$

The derivative hypotheses `hderiv` and `hddx` say that $x_\mu$ and $dx_\mu$ have derivatives $dx_\mu(t)$ and $ddx_\mu(t)$ almost everywhere with respect to Lebesgue measure restricted to $[0,\infty)$.

The parameter-regularity hypothesis is

$$
\forall x_\ast\in H,\ \forall \mu,\mu'\in M,\qquad
\|\mathrm{grad}\varphi_\mu(x_\ast)-\mathrm{grad}\varphi_{\mu'}(x_\ast)\|
\le k_1\,\|\mu-\mu'\|^{\gamma_1}.
$$

Thus the gradient depends Hölder continuously on the parameter, with exponent $\gamma_1\in(0,1]$. Finally,

$$
\forall \mu,\qquad \mathrm{grad}\varphi_\mu(\bar x_\mu)=0,
$$

so each $\bar x_\mu$ is a critical point of $\varphi_\mu$.

The conclusion is a conjunction of three statements. First, for every $\mu$,

$$
x_\mu(t)\to \bar x_\mu\qquad \text{as }t\to+\infty.
$$

Second, for every $\mu$,

$$
\bar x_\mu\in \mathrm{argminSet}(\varphi_\mu),
$$

so $\bar x_\mu$ is a global minimizer of $\varphi_\mu$. Third, for every $\mu,\mu'\in M$, if

$$
r_\mu=\mathrm{energyRate}\beta\gamma\delta(\mu),\qquad
r_{\mu'}=\mathrm{energyRate}\beta\gamma\delta(\mu'),
$$

and $c_{\max}=\max(r_\mu,r_{\mu'})$, then

$$
\|\bar x_\mu-\bar x_{\mu'}\|
\le
\frac{\beta k_1}{c_{\max}}\,\|\mu-\mu'\|^{\gamma_1}.
$$

Here

$$
\mathrm{energyRate}\beta\gamma\delta
=\frac{(\beta\delta+\gamma)-\sqrt{(\beta\delta+\gamma)^2-4\delta}}{2}.
$$

Thus the theorem asserts convergence to the critical points, identifies those critical points as global minimizers, and gives a Hölder/Lipschitz stability estimate for the minimizers as functions of the parameter.

## Lean proof
```lean
by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  have hconv : ∀ μ : M, Tendsto (x μ) atTop (nhds (xbar μ)) := fun μ =>
    din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ)) hlift
      (fun p q => energyStrong_of_strongConvex hβ hβγ (hstrong μ) (hgrad μ) p q)
      hβ (energyRate_pos hβ hγ (hstrong μ).1 hβγ) (hcrit μ)
  refine ⟨hconv, fun μ => mem_argminSet_of_grad_eq_zero (hstrong μ) (hgrad μ) (hcrit μ), ?_⟩
  intro μ μ'
  dsimp only
  have hpt : ∀ t, 0 ≤ t → ‖x μ t - x μ' t‖ ≤
      Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
            ‖μ - μ'‖ ^ γ₁ := fun t ht =>
    thm_5_estimate_all φ gradφ hessφ x dx ddx u₀ v₀ β γ δ k₁ γ₁ hβγ hβ hγ hdiff hgrad
      hstrong hk₁ hγ₁_pos hγ₁_le hDIN hderiv hddx hhess hlip h9 μ μ' t ht
  have hlim2 : Tendsto (fun t : ℝ =>
      Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t) *
          Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
            dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2) +
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) * t)) *
            ‖μ - μ'‖ ^ γ₁) atTop
      (nhds ((β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
        ‖μ - μ'‖ ^ γ₁)) := by
    have hc : 0 < max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) :=
      lt_max_of_lt_left (energyRate_pos hβ hγ (hstrong μ).1 hβγ)
    have hexp : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
    have h1 : Tendsto (fun t : ℝ =>
        Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t)) *
        Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖dinAuxInitial gradφ β γ u₀ v₀ μ -
          dinAuxInitial gradφ β γ u₀ v₀ μ'‖ ^ 2)) atTop (nhds 0) := by
      simpa using hexp.mul tendsto_const_nhds
    have h2 : Tendsto (fun t : ℝ =>
        (β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
        (1 - Real.exp (-(max (energyRate β γ (δ μ)) (energyRate β γ (δ μ')) * t))) *
          ‖μ - μ'‖ ^ γ₁) atTop
        (nhds ((β * k₁ / max (energyRate β γ (δ μ)) (energyRate β γ (δ μ'))) *
          (1 - 0) * ‖μ - μ'‖ ^ γ₁)) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)).mul tendsto_const_nhds)
    simpa using h1.add h2
  refine le_of_tendsto_of_tendsto ((hconv μ).sub (hconv μ')).norm hlim2 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hpt t ht
```

## Proof explanation
The proof begins by converting the second-order DIN system into the first-order lifted gradient system used by the convergence theorem. The command

$$
\text{`have hlift`}
$$

invokes `dinGradientLift_of_DIN`. The hypotheses supplied to that result are $\beta>0$, $1<\beta\gamma$, the DIN equations `hDIN`, the almost-everywhere derivative facts `hderiv` and `hddx`, the Hessian compatibility `hhess`, and the local Lipschitz property `hlip`. Its conclusion is

$$
\mathrm{DINGradientLift}\mathrm{grad}\varphi\ x\ u_0\ v_0\ \beta\ \gamma.
$$

Mathematically, this is the change-of-variables lemma: it constructs an auxiliary coordinate and shows that the pair consisting of $x_\mu(t)$ and that auxiliary coordinate is a solution of the first-order gradient system associated with the DIN field. The auxiliary initial value is

$$
\mathrm{dinAuxInitial}\mathrm{grad}\varphi\beta\gamma u_0v_0\mu
=-\left(\sqrt{(\gamma-\tfrac1\beta)\tfrac1\beta}\right)^{-1}
\left(
v_0(\mu)+\beta\mathrm{grad}\varphi_\mu(u_0(\mu))
+(\gamma-\tfrac1\beta)u_0(\mu)
\right).
$$

Inside the cited change-of-variables proof, `linarith` is used to deduce $1/\beta<\gamma$, hence $\gamma-1/\beta>0$, from $1<\beta\gamma$ and $\beta>0$; `positivity` proves $0<1/\beta$; `rw` and `simp` verify the initial condition and algebraic identities; and `module` finishes linear-algebraic manipulations. In the current proof, the only role of this step is to produce the hypothesis `hlift` required by the convergence theorem.

Next the proof establishes the first conclusion, convergence of each trajectory. The command

$$
\text{`have hconv : }\forall \mu,\ x_\mu(t)\to\bar x_\mu
$$

applies `din_tendsto_to_critical` for each fixed $\mu$. The inputs to `din_tendsto_to_critical` are the lifted trajectory `hlift`, a strong-monotonicity estimate for the lifted field, $\beta>0$, positivity of the strong-monotonicity constant, and the critical-point equation $\mathrm{grad}\varphi_\mu(\bar x_\mu)=0$. The strong-monotonicity estimate is supplied by

$$
\text{`energyStrong\_of\_strongConvex`}
$$

with $c(\mu)=\mathrm{energyRate}\beta\gamma\delta(\mu)$. That lemma uses the strong convexity of $\varphi_\mu$ with modulus $\delta(\mu)$ and the gradient hypothesis to prove that the lifted field $F_\mu=\mathrm{DINGradientField}\mathrm{grad}\varphi\beta\gamma\mu$ satisfies

$$
\mathrm{energyRate}\beta\gamma\delta(\mu)
\bigl(\|p_1-q_1\|^2+\|p_2-q_2\|^2\bigr)
\le
\langle F_\mu(p)_1-F_\mu(q)_1,\ p_1-q_1\rangle
+\langle F_\mu(p)_2-F_\mu(q)_2,\ p_2-q_2\rangle
$$

for all $p,q\in H\times H$. This is exactly the strong-monotonicity hypothesis required by `din_tendsto_to_critical`. The positivity requirement $0<\mathrm{energyRate}\beta\gamma\delta(\mu)$ is supplied by `energyRate_pos`, using $\beta>0$, $\gamma>0$, the positivity of $\delta(\mu)$ coming from strong convexity, and $\beta\gamma>1$. The critical-point hypothesis is exactly `hcrit μ`. Therefore `din_tendsto_to_critical` yields

$$
x_\mu(t)\to \bar x_\mu\qquad\text{as }t\to+\infty.
$$

This proves the first conjunct of the theorem.

The second conclusion is proved immediately after the convergence claim. The `refine` command splits the conjunction into its three parts, supplying `hconv` for the first part and

$$
\mu\mapsto
\text{`mem\_argminSet\_of\_grad\_eq\_zero`}(\text{`hstrong μ`},\text{`hgrad μ`},\text{`hcrit μ`})
$$

for the second part. The cited lemma `mem_argminSet_of_grad_eq_zero` says that if $f:H\to\mathbb R$ is strongly convex with modulus $\delta$, if $g$ is a gradient field for $f$, and if $g(\bar x)=0$, then $\bar x\in\mathrm{argminSet}(f)$. Specialized here to $f=\varphi_\mu$, $g=\mathrm{grad}\varphi_\mu$, and $\bar x=\bar x_\mu$, it uses `hstrong μ` for strong convexity, `hgrad μ` for the gradient property, and `hcrit μ` for the vanishing gradient. The mathematical content is that a strongly convex function cannot have a critical point that is not a global minimizer; hence $\bar x_\mu$ belongs to the global minimizer set of $\varphi_\mu$. This proves the second conjunct.

For the third conjunct, the proof introduces arbitrary parameters with `intro μ μ'` and uses `dsimp only` to unfold the local `let cmax` abbreviation in the goal. Thus the goal becomes

$$
\|\bar x_\mu-\bar x_{\mu'}\|
\le
\frac{\beta k_1}{\max(r_\mu,r_{\mu'})}
\|\mu-\mu'\|^{\gamma_1},
$$

where $r_\mu=\mathrm{energyRate}\beta\gamma\delta(\mu)$ and $r_{\mu'}=\mathrm{energyRate}\beta\gamma\delta(\mu')$.

The estimate for finite times is then obtained from `thm_5_estimate_all`. The proof defines `hpt` as the statement that for every $t\ge0$,

$$
\begin{aligned}
\|x_\mu(t)-x_{\mu'}(t)\|
&\le
\exp\!\left(-\max(r_\mu,r_{\mu'})\,t\right)
\sqrt{
\|u_0(\mu)-u_0(\mu')\|^2
+\|\mathrm{dinAuxInitial}\dots\mu
-\mathrm{dinAuxInitial}\dots\mu'\|^2
}\\
&\qquad
+\frac{\beta k_1}{\max(r_\mu,r_{\mu'})}
\left(1-\exp\!\left(-\max(r_\mu,r_{\mu'})\,t\right)\right)
\|\mu-\mu'\|^{\gamma_1}.
\end{aligned}
$$

The cited result `thm_5_estimate_all` is a Gronwall-type stability estimate for two DIN trajectories with parameters $\mu$ and $\mu'$. It uses the same regularity hypotheses as the theorem, together with the Hölder parameter-gradient assumption `h9`, and yields the displayed bound. The first term measures the initial distance in the lifted coordinates, involving both $u_0$ and the auxiliary initial value `dinAuxInitial`. The second term measures the influence of changing the parameter, with coefficient $\beta k_1/c_{\max}$ and factor $1-e^{-c_{\max}t}$.

The proof then shows that the right-hand side tends to the desired bound. It sets

$$
c_{\max}=\max(r_\mu,r_{\mu'}).
$$

The auxiliary claim `hc` proves $c_{\max}>0$: `energyRate_pos` gives $r_\mu>0$, and `lt_max_of_lt_left` then gives $0<\max(r_\mu,r_{\mu'})$. The claim `hexp` proves

$$
\exp(-c_{\max}t)\to0\qquad\text{as }t\to+\infty.
$$

This uses `Real.tendsto_exp_neg_atTop_nhds_zero`, the fact $\exp(-s)\to0$ as $s\to+\infty$, composed with $t\mapsto c_{\max}t$, which tends to $+\infty$ because $c_{\max}>0$. The claim `h1` shows that the first term tends to $0$, since it is $\exp(-c_{\max}t)$ times a constant. The claim `h2` shows that the second term tends to

$$
\frac{\beta k_1}{c_{\max}}\|\mu-\mu'\|^{\gamma_1},
$$

because $1-\exp(-c_{\max}t)\to1-0=1$ and the other factors are constant. The command `simpa using h1.add h2` combines these two limits and simplifies the sum to the stated limit `hlim2`.

Finally, the proof passes the finite-time inequality to the limit. The expression

$$
((hconv μ).sub (hconv μ')).norm
$$

uses the convergence $x_\mu(t)\to\bar x_\mu$ and $x_{\mu'}(t)\to\bar x_{\mu'}$ to conclude

$$
\|x_\mu(t)-x_{\mu'}(t)\|\to\|\bar x_\mu-\bar x_{\mu'}\|.
$$

The lemma `le_of_tendsto_of_tendsto` states that if one sequence tends to $A$, another tends to $B$, and the first is eventually at most the second, then $A\le B$. Here the first sequence is $\|x_\mu(t)-x_{\mu'}(t)\|$ and the second is the right-hand side from `hlim2`. The eventual inequality is supplied by `filter_upwards` with `eventually_ge_atTop (0 : ℝ)`: for all sufficiently large $t$, one has $t\ge0$, and for such $t$ the pointwise estimate `hpt t ht` holds. Therefore taking the limit gives

$$
\|\bar x_\mu-\bar x_{\mu'}\|
\le
\frac{\beta k_1}{\max(r_\mu,r_{\mu'})}
\|\mu-\mu'\|^{\gamma_1}.
$$

This proves the third conjunct and completes the theorem.

