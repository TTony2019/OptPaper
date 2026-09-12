## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_9.lean`

## Lean statement
```lean
theorem derivative_inner_nonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (x v : ℝ → H)
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (_hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (_hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt v (deriv v t) t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ inner ℝ (deriv x t) (deriv v t)
```

## Statement explanation
Let $H$ be a normed additive group with a real inner product space structure. The theorem concerns maps $x,v:\mathbb R\to H$ and an extended-real-valued function

$$
\Phi:H\to \mathrm{Set.Ioi}(\bot:\mathrm{EReal}),
$$

meaning that each $\Phi(y)$ is an extended real number strictly above the bottom element $\bot$. The hypothesis `hPhi` says that $\Phi$ belongs to the class `ERealFunction.gammaZero H`, written $\Gamma_0(H)$ in the cited context. The proof uses this membership only through the fact that the coerced function

$$
F(y)=(\Phi(y):\mathrm{EReal})
$$

is proper.

The subdifferential used here is defined by the subgradient inequality

```math
\partial f(x)
=\left\{\,u\in H \;\middle|\;
\forall y\in H,\;
(\langle y-x,u\rangle_{\mathbb R}:\mathrm{EReal})
+(f(x):\mathrm{EReal})
\le
(f(y):\mathrm{EReal})
\,\right\}.
```

The hypothesis `hsubgradient` states that for every real $t$ with $0\le t$,

$$
v(t)\in \partial \Phi(x(t)).
$$

Thus $v(t)$ is a subgradient of $\Phi$ at the point $x(t)$ for every nonnegative time $t$.

The two hypotheses `_hx_ac` and `_hv_ac` say that $x$ and $v$ are absolutely continuous on the interval from $0$ to $b$, for every $b\gt 0$. They are present in the statement, but the proof below does not invoke them.

The differentiability hypotheses `hx_deriv` and `hv_deriv` say that, for almost every $t$ with respect to Lebesgue measure restricted to $(0,\infty)$, the maps $x$ and $v$ have derivatives

$$
\mathrm{deriv} x(t)
\qquad\text{and}\qquad
\mathrm{deriv} v(t)
$$

at $t$, respectively. The conclusion is that, for almost every $t\in(0,\infty)$,

$$
0\le
\left\langle
\mathrm{deriv} x(t),
\mathrm{deriv} v(t)
\right\rangle_{\mathbb R}.
$$

In words: along a curve $x$ for which $v(t)$ is always a subgradient of $\Phi$ at $x(t)$, the derivatives of $x$ and $v$ have nonnegative inner product almost everywhere on $(0,\infty)$.

## Lean proof
```lean
by
  have hmono : SetValuedOperator.IsMonotone
      (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
    ERealFunction.isMonotone_subdifferential
      (fun y : H => (Phi y : EReal))
      (ERealFunction.isProper_of_mem_gammaZero hPhi)
  filter_upwards [hx_deriv, hv_deriv,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t hxt hvt ht
  exact inner_deriv_nonneg_of_monotone hmono hsubgradient ht hxt hvt
```

## Proof explanation
The proof starts with the intermediate assertion `hmono`. Let

$$
F(y)=(\Phi(y):\mathrm{EReal}).
$$

The cited result `ERealFunction.isProper_of_mem_gammaZero` has the following content: if $f:H\to \mathrm{Set.Ioi}(\bot:\mathrm{EReal})$ lies in $\Gamma_0(H)$, then the coerced function $y\mapsto (f(y):\mathrm{EReal})$ is proper. Applying it to $\Phi$ and `hPhi` gives that $F$ is proper.

Next, the cited theorem `ERealFunction.isMonotone_subdifferential` states that if $F:H\to\mathrm{EReal}$ is proper, then its subdifferential operator $\partial F$ is monotone as a set-valued operator. In concrete terms, for all $p,q\in H$, all $u\in\partial F(p)$, and all $w\in\partial F(q)$,

$$
0\le \langle u-w,p-q\rangle_{\mathbb R}.
$$

Applying this theorem to the proper function $F(y)=(\Phi(y):\mathrm{EReal})$ gives exactly the asserted monotonicity `hmono`.

The tactic `filter_upwards` is then used to prove an almost-everywhere statement. It consumes the three almost-everywhere facts `hx_deriv`, `hv_deriv`, and

$$
\text{`MeasureTheory.ae\_restrict\_mem measurableSet\_Ioi`}.
$$

The first two say that $x$ and $v$ are differentiable at almost every point of the restricted measure. The third says that almost every point of that restricted measure belongs to the set $(0,\infty)$. Therefore, after `filter_upwards`, the proof has a point $t$ with $0\lt t$, together with the differentiability facts

$$
\mathrm{HasDerivAt} x (\mathrm{deriv} x(t)) t,
\qquad
\mathrm{HasDerivAt} v (\mathrm{deriv} v(t)) t.
$$

The remaining goal at that point is

$$
0\le
\left\langle
\mathrm{deriv} x(t),
\mathrm{deriv} v(t)
\right\rangle_{\mathbb R}.
$$

The final step applies the cited lemma `inner_deriv_nonneg_of_monotone`. Its statement is: if $T$ is a monotone set-valued operator on $H$, if for every $s\ge 0$ one has $v(s)\in T(x(s))$, and if at a positive time $t$ the maps $x$ and $v$ have derivatives $dx(t)$ and $dv(t)$, then

$$
0\le \langle dx(t),dv(t)\rangle_{\mathbb R}.
$$

In the present application, $T=\partial F$, the derivative $dx(t)$ is $\mathrm{deriv} x(t)$, and $dv(t)$ is $\mathrm{deriv} v(t)$. The hypothesis $v(s)\in T(x(s))$ for all $s\ge 0$ is exactly `hsubgradient`, after identifying $\partial \Phi$ with $\partial F$ via the coercion. The positivity $0\lt t$ is supplied by `ht`, and the two derivative facts are exactly the ones introduced by `filter_upwards`.

Mathematically, the lemma uses monotonicity at the two times $t$ and $t-h$, for small $h\gt 0$. Since both are nonnegative, it obtains

$$
v(t)\in T(x(t)),
\qquad
v(t-h)\in T(x(t-h)).
$$

Monotonicity then gives

```math
0\le
\left\langle
v(t)-v(t-h),\,
x(t)-x(t-h)
\right\rangle_{\mathbb R}.
```

Dividing by $h^2\gt 0$ yields

```math
0\le
\left\langle
\frac{v(t)-v(t-h)}{h},\,
\frac{x(t)-x(t-h)}{h}
\right\rangle_{\mathbb R}.
```

As $h\to 0^+$, the two difference quotients converge to $\mathrm{deriv} v(t)$ and $\mathrm{deriv} x(t)$, respectively. Hence

$$
0\le
\left\langle
\mathrm{deriv} v(t),
\mathrm{deriv} x(t)
\right\rangle_{\mathbb R}
=\left\langle
\mathrm{deriv} x(t),
\mathrm{deriv} v(t)
\right\rangle_{\mathbb R},
$$

because the real inner product is symmetric. This is exactly the desired pointwise inequality at $t$. Since $t$ was an arbitrary point satisfying the three almost-everywhere properties, the `filter_upwards` construction completes the proof of the almost-everywhere conclusion.

