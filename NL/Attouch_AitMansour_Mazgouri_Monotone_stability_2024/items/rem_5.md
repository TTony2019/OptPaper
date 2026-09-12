## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/rem_5.lean`

## Lean statement
```lean
theorem rem_5 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ) ∧
        (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt (x μ) (dx μ t) t) ∧
        ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt (dx μ) (ddx μ t) t)
    (θ₁ θ₂ : ℝ) (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hγT : γ * T + T ^ 2 / α < 1) :
    (∀ μ ∈ V, ∀ μ' ∈ V,
      pathSupNorm T (fun t => x μ t - x μ' t) ≤
        α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂))
```

## Statement explanation
The declaration `rem_5` is a stability theorem for a parameterized family of second-order evolution equations. The state space is $H$, a complete real inner product space, hence a real Hilbert space, and the parameter space is $M$, a normed additive commutative group. A parameter set $V \subseteq M$ is fixed. The map

$$
A : M \to H \to H
$$

associates to each parameter $\mu$ a state-dependent vector field $A_\mu : H \to H$, written $A_\mu(u)=A(\mu,u)$. The functions

$$
x,dx,ddx : M \to \mathbb R \to H
$$

assign to each parameter $\mu$ a trajectory $t\mapsto x_\mu(t)$, its first derivative data $t\mapsto dx_\mu(t)$, and its second derivative data $t\mapsto ddx_\mu(t)$. The initial data are $u_0,v_0 : M \to H$. The real parameters $\alpha,\gamma,T$ satisfy $0\lt \alpha$ and $0\lt T$.

The hypotheses are as follows.

- `hcoco`: for every $\mu\in V$, the map $A_\mu$ is $\alpha$-cocoercive on the whole space $H$, represented in Lean as cocoercivity on `Set.univ`.
- `hsol`: for every $\mu\in V$, three things hold. First, the tuple $(A_\mu,\gamma,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu)$ satisfies the abstract solution condition named `ext_def_2`. Second, for almost every $t$ with respect to Lebesgue measure on $\mathbb R$, if $0\le t$, then $x_\mu$ is differentiable at $t$ with derivative $dx_\mu(t)$. Third, for almost every $t$, if $0\le t$, then $dx_\mu$ is differentiable at $t$ with derivative $ddx_\mu(t)$. Thus the hypotheses include an a.e. classical differentiability condition in addition to the abstract solution condition.
- `hC₂`: $0\lt \theta_1$, $0\lt \theta_2$, $\theta_2\le 1$, and for every $u\in H$ and all $\mu,\mu'\in V$,

```math
\|A_\mu(u)-A_{\mu'}(u)\|\le \theta_1\|\mu-\mu'\|^{\theta_2}.
```

This is a uniform Hölder continuity condition in the parameter $\mu$.
- `hγT`: $\gamma T+T^2/\alpha\lt 1$. Since $\alpha\gt 0$, this implies

$$
\alpha-\alpha\gamma T-T^2
=\alpha\left(1-\gamma T-\frac{T^2}{\alpha}\right)>0.
$$

The conclusion is that for all $\mu,\mu'\in V$,

```math
\mathrm{pathSupNorm}_T\bigl(t\mapsto x_\mu(t)-x_{\mu'}(t)\bigr)
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\left(
\|u_0(\mu)-u_0(\mu')\|
+T\|v_0(\mu)-v_0(\mu')\|
+T^2\theta_1\|\mu-\mu'\|^{\theta_2}
\right).
```

Here `pathSupNorm T` is the path-supremum norm appearing in the statement. The inequality says that the maximal difference between two solution paths is controlled by the differences in initial position, initial velocity, and parameter value, with the stability constant $\alpha/(\alpha-\alpha\gamma T-T^2)$. The additional a.e. derivative assumptions in `hsol` are stronger than needed for this estimate.

## Lean proof
```lean
thm_8 V A x dx ddx u₀ v₀ α γ T hα hT hcoco (fun μ hμ => (hsol μ hμ).1) θ₁ θ₂ hC₂ hγT
```

## Proof explanation
The proof is a direct term-mode application of `thm_8`. There are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`; the entire proof is the application of the previously established theorem to the current data.

The cited theorem `thm_8` has exactly the same typeclass assumptions on $H$ and $M$, the same set $V$, the same maps $A,x,dx,ddx,u_0,v_0$, the same constants $\alpha,\gamma,T,\theta_1,\theta_2$, and the same hypotheses $0\lt \alpha$, $0\lt T$, `hcoco`, `hC₂`, and $\gamma T+T^2/\alpha\lt 1$. Its solution hypothesis is weaker than the one in `rem_5`: it only requires

```math
\forall \mu\in V,\quad \text{the abstract condition } ext\_def\_2
```

for $(A_\mu,\gamma,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu)$. It does not require the two almost-everywhere differentiability clauses. Under these assumptions, `thm_8` proves precisely the same quantified inequality as the conclusion of `rem_5`.

The only step needed to invoke `thm_8` is to produce its weaker solution hypothesis from the stronger hypothesis `hsol`. For each $\mu\in V$, the value `hsol μ hμ` is a conjunction whose first component is exactly the condition `ext_def_2` with the appropriate arguments. The projection `(hsol μ hμ).1` extracts that first component. Therefore the anonymous function sending $\mu$ and a proof of $\mu\in V$ to the first conjunct of `hsol μ hμ` has the required type

```math
\forall \mu\in V,\quad ext\_def\_2(A_\mu,\gamma,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu).
```

The two extra almost-everywhere differentiability conditions are discarded; they are not used by `thm_8`.

After supplying this projected solution hypothesis, all remaining hypotheses are passed unchanged: $0\lt \alpha$, $0\lt T$, `hcoco`, the Hölder condition `hC₂`, and the smallness condition $\gamma T+T^2/\alpha\lt 1$. The theorem `thm_8` then returns the bound

```math
\forall \mu\in V,\ \forall \mu'\in V,\quad
\mathrm{pathSupNorm}_T\bigl(t\mapsto x_\mu(t)-x_{\mu'}(t)\bigr)
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\left(
\|u_0(\mu)-u_0(\mu')\|
+T\|v_0(\mu)-v_0(\mu')\|
+T^2\theta_1\|\mu-\mu'\|^{\theta_2}
\right),
```

which is exactly the conclusion of `rem_5`. Thus `rem_5` is a strengthened-hypothesis version of `thm_8`: it assumes more regularity of the trajectories, but obtains the same stability estimate by forgetting the extra differentiability information and applying the earlier theorem. No arithmetic or rewriting occurs in the proof itself; the smallness condition is used only inside `thm_8`.

