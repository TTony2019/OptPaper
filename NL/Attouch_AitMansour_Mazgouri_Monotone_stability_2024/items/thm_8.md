## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_8.lean`

## Lean statement
```lean
theorem thm_8 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (θ₁ θ₂ : ℝ) (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hγT : γ * T + T ^ 2 / α < 1) :
    ∀ μ ∈ V, ∀ μ' ∈ V,
      pathSupNorm T (fun t => x μ t - x μ' t) ≤ α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂)
```

## Statement explanation
`thm_8` is a quantitative stability estimate for a family of trajectories indexed by a parameter in a set $V$. The ambient space $H$ is a complete real inner product space, and the parameter space $M$ is a normed additive commutative group. The set $V\subseteq M$ is the set of admissible parameters. The operator family is

$$
A:M\to H\to H,\qquad A_\mu(u)=A(\mu)(u).
$$

For each admissible parameter $\mu\in V$, the theorem considers a trajectory

$$
x_\mu:\mathbb R\to H
$$

with derivative $dx_\mu$ and second derivative $ddx_\mu$, and with initial position $u_0(\mu)$ and initial velocity $v_0(\mu)$.

The numerical hypotheses are $\alpha\gt 0$ and $T\gt 0$. For every $\mu\in V$, the operator $A_\mu$ is assumed to be cocoercive on all of $H$ with constant $\alpha$. Also, for every $\mu\in V$, the trajectory $x_\mu$ is assumed to satisfy the predicate `ext_def_2` relating the operator $A_\mu$, the damping parameter $\gamma$, the initial data $u_0(\mu),v_0(\mu)$, and the derivatives $dx_\mu,ddx_\mu$. The exact differential equation or inclusion encoded by `ext_def_2` is not part of the provided source, so the present declaration only uses the fact that this solution predicate holds.

The main extra hypothesis is the parameter regularity of the operator family. There are real constants $\theta_1,\theta_2$ such that

$$
0<\theta_1,\qquad 0<\theta_2,\qquad \theta_2\le 1,
$$

and such that for all $u\in H$ and all $\mu,\mu'\in V$,

```math
\|A_\mu u-A_{\mu'}u\|\le \theta_1\|\mu-\mu'\|^{\theta_2}.
```

Thus $A_\mu$ depends on $\mu$ in a uniform Hölder/Lipschitz fashion, uniformly in the state variable $u$.

The final numerical assumption is the stability condition

$$
\gamma T+\frac{T^2}{\alpha}<1.
$$

Since $\alpha\gt 0$, this is equivalent to

$$
\alpha-\alpha\gamma T-T^2>0,
$$

so the denominator appearing in the conclusion is positive.

The conclusion says that for every two admissible parameters $\mu,\mu'\in V$, the supremum norm on $[0,T]$ of the trajectory difference is bounded by

```math
\mathrm{pathSupNorm}_T\bigl(t\mapsto x_\mu(t)-x_{\mu'}(t)\bigr)
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\Bigl(
\|u_0(\mu)-u_0(\mu')\|
+T\|v_0(\mu)-v_0(\mu')\|
+T^2\theta_1\|\mu-\mu'\|^{\theta_2}
\Bigr).
```

Thus the distance between the two trajectories is controlled by the initial-position difference, the initial-velocity difference, and the parameter perturbation, with the latter entering through the Hölder term $`\theta_1\|\mu-\mu'\|^{\theta_2}`$.

## Lean proof
```lean
by
  intro μ hμ μ' hμ'
  simpa only [mul_assoc] using
    thm_8_general V A x dx ddx u₀ v₀ α γ T hα hT hcoco hsol hγT μ hμ μ' hμ'
      (θ₁ * ‖μ - μ'‖ ^ θ₂)
      (by
        intro s hs v hv
        exact hC₂.2.2.2 v μ μ' hμ hμ')
```

## Proof explanation
The proof begins by introducing arbitrary admissible parameters. The tactic `intro μ hμ μ' hμ'` unwraps the universally quantified conclusion

$$
\forall \mu\in V,\ \forall \mu'\in V,\ \ldots
$$

and fixes $\mu,\mu'\in V$, with hypotheses $h\mu:\mu\in V$ and $h\mu':\mu'\in V$. The goal is then the displayed stability estimate for this particular pair.

The rest of the proof is a direct application of `thm_8_general`. That theorem has the same data $H,M,V,A,x,dx,ddx,u_0,v_0,\alpha,\gamma,T$, the same assumptions $\alpha\gt 0$, $T\gt 0$, cocoercivity of each $A_\mu$, the `ext_def_2` solution hypothesis, and the same condition

$$
\gamma T+\frac{T^2}{\alpha}<1.
$$

It then assumes an additional real number $D$ satisfying the bound

```math
\forall s\in[0,T],\ \forall v\in H,\quad
\|v-x_{\mu'}(s)\|\le \|u_0(\mu)-u_0(\mu')\|
\implies
\|A_\mu v-A_{\mu'}v\|\le D.
```

From these hypotheses, `thm_8_general` concludes

```math
\mathrm{pathSupNorm}_T(x_\mu-x_{\mu'})
\le
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\Bigl(
\|u_0(\mu)-u_0(\mu')\|
+T\|v_0(\mu)-v_0(\mu')\|
+T^2D
\Bigr).
```

In the present proof, the number $D$ is chosen to be

```math
D=\theta_1\|\mu-\mu'\|^{\theta_2}.
```

The nontrivial remaining obligation is therefore to prove the hypothesis `hDbound` from `thm_8_general`. The proof does this with the nested block
```lean
by
  intro s hs v hv
  exact hC₂.2.2.2 v μ μ' hμ hμ'
```
Mathematically, this introduces an arbitrary time $s\in[0,T]$, an arbitrary state $v\in H$, and the extra implication hypothesis

```math
\|v-x_{\mu'}(s)\|\le \|u_0(\mu)-u_0(\mu')\|.
```

The fourth conjunct of the hypothesis $hC_2$ states exactly that for all $u\in H$ and all $\mu,\mu'\in V$,

```math
\|A_\mu u-A_{\mu'}u\|\le \theta_1\|\mu-\mu'\|^{\theta_2}.
```

Applying it with $u=v$, the already introduced parameters $\mu,\mu'$, and the membership facts $h\mu,h\mu'$, gives

```math
\|A_\mu v-A_{\mu'}v\|\le \theta_1\|\mu-\mu'\|^{\theta_2}=D.
```

Thus the required `hDbound` condition is satisfied. The extra hypotheses $hs$ and $hv$ are not used because the Hölder estimate is uniform in the state variable and does not depend on the time variable or on the condition $`\|v-x_{\mu'}(s)\|\le \|u_0(\mu)-u_0(\mu')\|`$.

After this, `thm_8_general` yields the desired inequality with the term $T^2D$. Since $`D=\theta_1\|\mu-\mu'\|^{\theta_2}`$, that term is

```math
T^2\bigl(\theta_1\|\mu-\mu'\|^{\theta_2}\bigr).
```

The final tactic `simpa only [mul_assoc]` rewrites products using associativity of multiplication, so that this expression is recognized as

```math
T^2\theta_1\|\mu-\mu'\|^{\theta_2},
```

which is exactly the term appearing in the stated conclusion of `thm_8`. No `rw` or `linarith` step occurs in this proof; the argument is an instantiation of the general theorem with a suitably chosen $D$, followed by associativity normalization of the product.

