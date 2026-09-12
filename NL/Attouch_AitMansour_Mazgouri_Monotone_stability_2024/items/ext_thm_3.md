## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_3.lean`

## Lean statement
```lean
theorem ext_thm_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M]
    (φ : M → H → ℝ) (gradφ : M → H → H) (hessφ : M → H → H → H) (γ β : ℝ)
    (δ : M → ℝ) (k₁ γ₁ : ℝ)
    (hβγ : β * γ > 1) (hβ : 0 < β) (hγ : 0 < γ)
    (hdiff : ∀ μ : M, Differentiable ℝ (φ μ))
    (hgrad : ∀ μ q, HasGradientAt (φ μ) (gradφ μ q) q)
    (hstrong : ∀ μ : M, IsStronglyConvex (φ μ) (δ μ))
    (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1)
    (h9 : ∀ x_ : H, ∀ μ μ' : M, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H)
    (hDIN : ∀ μ : M, DIN (φ μ) (gradφ μ) (hessφ μ) γ β (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hderiv : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (x μ) (dx μ t) t)
    (hddx : ∀ μ,
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 0)), HasDerivAt (dx μ) (ddx μ t) t)
    (hhess : ∀ μ q, ∃ L : H →L[ℝ] H,
      HasFDerivAt (gradφ μ) L q ∧ ∀ v, L v = hessφ μ q v)
    (hlip : ∀ μ T', 0 < T' → ∃ K : NNReal,
      LipschitzOnWith K (gradφ μ) (x μ '' Set.uIcc 0 T'))
    (hargmin : ∀ μ : M, (Optimization.argminSet (φ μ)).Nonempty) :
    ∀ μ : M, ∃ z ∈ Optimization.argminSet (φ μ), Tendsto (x μ) atTop (nhds z)
```

## Statement explanation
The theorem `ext_thm_3` is a convergence result for a parametrized family of DIN flows. The ambient state space $H$ is a real Hilbert space: it is a complete real inner product space. The parameter space $M$ is a normed additive group. For each parameter $\mu\in M$, the data describe an energy function $\phi_\mu:H\to\mathbb R$, a candidate gradient $\operatorname{grad}\phi_\mu:H\to H$, and a candidate Hessian action $\operatorname{hess}\phi_\mu:H\to H\to H$, together with constants $\beta,\gamma\in\mathbb R$ and a strong convexity modulus $\delta(\mu)$.

The hypotheses are the following. First, $0<\beta$, $0<\gamma$, and $\beta\gamma>1$. For every $\mu$, the function $\phi_\mu$ is differentiable, and $\operatorname{grad}\phi_\mu(q)$ is a gradient of $\phi_\mu$ at each $q\in H$. Also, $\phi_\mu$ is strongly convex with modulus $\delta(\mu)$. The constants $k_1,\gamma_1$ satisfy $k_1>0$ and $0<\gamma_1\le 1$, and the hypothesis `h9` says that the gradient depends Hölder-continuously on the parameter: for every $x\in H$ and every $\mu,\mu'\in M$,

$$
\|\operatorname{grad}\phi_\mu(x)-\operatorname{grad}\phi_{\mu'}(x)\|
\le k_1\|\mu-\mu'\|^{\gamma_1}.
$$

For each $\mu$, the curves

$$
x_\mu:\mathbb R\to H,\qquad dx_\mu:\mathbb R\to H,\qquad ddx_\mu:\mathbb R\to H
$$

are part of a DIN system with initial data $u_0(\mu),v_0(\mu)$, parameters $\gamma,\beta$, energy $\phi_\mu$, gradient $\operatorname{grad}\phi_\mu$, and Hessian action $\operatorname{hess}\phi_\mu$. The derivative hypotheses say that, almost everywhere with respect to Lebesgue measure restricted to $[0,\infty)$,

$$
x_\mu'(t)=dx_\mu(t),\qquad dx_\mu'(t)=ddx_\mu(t).
$$

The Hessian hypothesis says that for each $\mu$ and $q$, there is a continuous linear map $L:H\to H$ such that $L$ is the Fréchet derivative of $\operatorname{grad}\phi_\mu$ at $q$, and $Lv=\operatorname{hess}\phi_\mu(q)(v)$ for every $v\in H$. The Lipschitz hypothesis says that for each $\mu$ and each $T'>0$, the map $\operatorname{grad}\phi_\mu$ is Lipschitz on the image $x_\mu([0,T'])$. Finally, `hargmin` says that for every $\mu$, the set of global minimizers of $\phi_\mu$ is nonempty.

The conclusion is: for every parameter $\mu\in M$, there exists a point $z\in H$ belonging to the argmin set of $\phi_\mu$ such that $x_\mu(t)$ converges to $z$ as $t\to\infty$. In ordinary language, along every parametrized DIN trajectory, the primal trajectory eventually converges to some minimizer of the corresponding energy.

## Lean proof
```lean
by
  have hlift : DINGradientLift gradφ x u₀ v₀ β γ :=
    dinGradientLift_of_DIN φ gradφ hessφ x dx ddx u₀ v₀ β γ hβ hβγ hDIN hderiv hddx hhess hlip
  intro μ
  obtain ⟨z, hz⟩ := hargmin μ
  refine ⟨z, hz, din_tendsto_to_critical gradφ x u₀ v₀ β γ (fun μ => energyRate β γ (δ μ))
    hlift (fun p q => energyStrong_of_strongConvex (μ := μ) hβ hβγ (hstrong μ) (hgrad μ) p q) hβ
    (energyRate_pos hβ hγ (hstrong μ).1 hβγ)
    (grad_eq_zero_of_mem_argminSet (hgrad μ) hz)⟩
```

## Proof explanation
The proof first constructs the first-order gradient lift required by the convergence theorem. It applies `dinGradientLift_of_DIN`. That lemma takes the Hamiltonian data $\phi,\operatorname{grad}\phi,\operatorname{hess}\phi$, the curves $x,dx,ddx$, the initial data $u_0,v_0$, and the constants $\beta,\gamma$. Its hypotheses are exactly the positivity $0<\beta$, the inequality $1<\beta\gamma$ (the same as $\beta\gamma>1$), the DIN property for every $\mu$, the almost-everywhere derivative relations for $x_\mu$ and $dx_\mu$, the Fréchet derivative/Hessian relation, and the local Lipschitz condition on $\operatorname{grad}\phi_\mu$ along $x_\mu([0,T'])$. Under these assumptions it returns

$$
\texttt{DINGradientLift}\ \operatorname{grad}\phi\ x\ u_0\ v_0\ \beta\ \gamma.
$$

The content of that construction is that a lifted curve $t\mapsto (x_\mu(t), \operatorname{dinAux}_\mu(t))$ is built, where the second component is an auxiliary combination involving $dx_\mu$, $\operatorname{grad}\phi_\mu(x_\mu)$, and $x_\mu$. The lemma verifies the initial condition at time $0$, absolute continuity on each interval $[0,T]$, and the first-order flow equation

$$
\frac{d}{dt}\bigl(x_\mu(t),\operatorname{dinAux}_\mu(t)\bigr)
=
-\operatorname{DINGradientField}\operatorname{grad}\phi\,\beta\,\gamma\,\mu
\bigl(x_\mu(t),\operatorname{dinAux}_\mu(t)\bigr)
$$

for almost every $t$ in $[0,T]$. Thus the second-order DIN system is repackaged into the first-order gradient system to which `din_tendsto_to_critical` applies.

Next, the proof introduces an arbitrary parameter $\mu$ using `intro μ`. The goal is then to prove the existential statement for this fixed $\mu$. The command

$$
\texttt{obtain }\langle z,hz\rangle := \texttt{hargmin }\mu
$$

uses the hypothesis that the argmin set of $\phi_\mu$ is nonempty to choose a point $z\in H$ with $z\in\operatorname{argminSet}(\phi_\mu)$. Thus $z$ is a global minimizer of $\phi_\mu$.

The command `refine ⟨z, hz, ?_⟩` then supplies this $z$ and its membership in the argmin set as the first two parts of the existential conclusion. It remains to prove that $x_\mu(t)$ tends to $z$ as $t\to\infty$. This is done by applying `din_tendsto_to_critical`.

The theorem `din_tendsto_to_critical` says that if $\texttt{DINGradientLift}\ \operatorname{grad}\phi\ x\ u_0\ v_0\ \beta\ \gamma$ holds, if the associated field $\operatorname{DINGradientField}\operatorname{grad}\phi\,\beta\,\gamma\,\mu$ is strongly monotone with constant $c(\mu)$, if $\beta>0$, if $c(\mu)>0$, and if $\operatorname{grad}\phi_\mu(z)=0$, then

$$
x_\mu(t)\to z\quad\text{as }t\to\infty.
$$

Here the constant function is chosen to be

$$
c(\mu)=\operatorname{energyRate}(\beta,\gamma,\delta(\mu)),
$$

where

$$
\operatorname{energyRate}(\beta,\gamma,\delta)
=
\frac{\beta\delta+\gamma-\sqrt{(\beta\delta+\gamma)^2-4\delta}}{2}.
$$

The strong monotonicity hypothesis supplied to `din_tendsto_to_critical` is proved by

$$
\texttt{fun }p\ q\mapsto
\texttt{energyStrong\_of\_strongConvex }(\mu:=\mu)\ h\beta\ h\beta\gamma
\ (hstrong\ \mu)\ (hgrad\ \mu)\ p\ q.
$$

The cited result `energyStrong_of_strongConvex` states that if $0<\beta$, if $1<\beta\gamma$, if $\phi_\mu$ is strongly convex with modulus $\delta(\mu)$, and if $\operatorname{grad}\phi_\mu$ is a gradient field for $\phi_\mu$, then for all $p,q\in H\times H$,

$$
\operatorname{energyRate}(\beta,\gamma,\delta(\mu))
\bigl(\|p_1-q_1\|^2+\|p_2-q_2\|^2\bigr)
\le
\bigl\langle F_\mu(p)_1-F_\mu(q)_1,\ p_1-q_1\bigr\rangle
+
\bigl\langle F_\mu(p)_2-F_\mu(q)_2,\ p_2-q_2\bigr\rangle,
$$

where $F_\mu=\operatorname{DINGradientField}\operatorname{grad}\phi\,\beta\,\gamma\,\mu$. This is exactly the required strong monotonicity estimate for the lifted field.

The positivity $c(\mu)>0$ is obtained from

$$
\texttt{energyRate\_pos }h\beta\ h\gamma\ (hstrong\ \mu).1\ h\beta\gamma.
$$

The lemma `energyRate_pos` says that if $\beta>0$, $\gamma>0$, $\delta>0$, and $\beta\gamma>1$, then $\operatorname{energyRate}(\beta,\gamma,\delta)>0$. The term $(hstrong\ \mu).1$ is the positivity part of the strong convexity hypothesis for $\phi_\mu$, giving $\delta(\mu)>0$. Hence $c(\mu)=\operatorname{energyRate}(\beta,\gamma,\delta(\mu))$ is positive.

Finally, the critical point condition is supplied by

$$
\texttt{grad\_eq\_zero\_of\_mem\_argminSet }(hgrad\ \mu)\ hz.
$$

That lemma says that if $g$ is a gradient field of a function $f$ everywhere, meaning $g(q)$ is a gradient of $f$ at every $q$, and if $z$ belongs to the argmin set of $f$, then $g(z)=0$. Applied with $f=\phi_\mu$, $g=\operatorname{grad}\phi_\mu$, and $z$ the minimizer obtained above, it gives

$$
\operatorname{grad}\phi_\mu(z)=0.
$$

This is precisely the critical-point hypothesis needed by `din_tendsto_to_critical`.

Putting these pieces together, `din_tendsto_to_critical` yields

$$
\texttt{Tendsto }(x\ \mu)\ \texttt{atTop}\ (\texttt{nhds }z),
$$

that is, $x_\mu(t)\to z$ as $t\to\infty$. Since $z$ was chosen in the argmin set, this completes the existential conclusion for the arbitrary fixed $\mu$, and hence for every $\mu\in M$. The hypotheses `hdiff`, `hk₁`, `hγ₁_pos`, `hγ₁_le`, and `h9` appear in the statement but are not invoked in this particular proof; the proof uses `hβ`, `hγ`, `hβγ`, `hgrad`, `hstrong`, `hDIN`, `hderiv`, `hddx`, `hhess`, `hlip`, and `hargmin`. No `rw`, `simp`, `exact`, or `linarith` tactic occurs in this proof; it is a direct composition of the cited results.

