## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/thm_2.lean`

## Lean statement
```lean
theorem togesVH_rate_descent_and_integrability {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (u : ℝ → H)
    (z : H) (alpha beta t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hFContDiff : ContDiff ℝ 2 f)
    (hMin : IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hUContDiff : ContDiff ℝ 3 u)
    (hTrajectory : IsTOGESVH u alpha beta f t0) :
    3 < alpha → 0 ≤ beta →
      let t1
```

## Statement explanation
The declaration `togesVH_rate_descent_and_integrability` states a quantitative decay and integrability estimate for a third-order-in-time evolution equation in a real Hilbert space. The space $H$ is a complete real inner product space. The data are a function $f:H\to \mathbb R$, a curve $u:\mathbb R\to H$, a point $z\in H$, and real parameters $\alpha,\beta,t_0$.

The hypotheses are:

- $f$ is convex on all of $H$, expressed by `ConvexOn ℝ Set.univ f`.
- $f$ is $C^2$, expressed by `ContDiff ℝ 2 f`.
- $z$ is a global minimizer of $f$, expressed by `IsMinOn f Set.univ z`.
- $t_0>0$.
- $u$ is $C^3$, expressed by `ContDiff ℝ 3 u`.
- $u$ satisfies the TOGES-V H trajectory property with parameters $\alpha,\beta$ and starting time $t_0$, expressed by `IsTOGESVH u alpha beta f t0`.

Write

$$
u'(t):=\mathrm{deriv}u(t),\qquad
u''(t):=\mathrm{deriv}(\mathrm{deriv}u)(t),\qquad
u'''(t):=\mathrm{deriv}(\mathrm{deriv}(\mathrm{deriv}u))(t).
$$

The conclusion is an implication: if

$$
3<\alpha
\qquad\text{and}\qquad
0\le \beta,
$$

then define

$$
t_1=\frac{2\beta(\alpha-2)}{\alpha-3},\qquad
t_{\mathrm{start}}=\max(t_0,t_1),
$$

and define the energy

$$
E_1=\mathrm{togesVLyapunov}(f,u,z,\alpha,\beta,t_{\mathrm{start}}).
$$

The definition of `togesVLyapunov` gives

$$
\mathrm{togesVLyapunov}(f,u,z,\alpha,\beta,t)
=4t\,\mathrm{togesVDelta}(\beta,t)
\left(f(\mathrm{togesVAuxiliary}(u,t))-\inf(\mathrm{range}f)\right)
+\frac12
\left\|\mathrm{togesVLyapunovVector}(u,z,\alpha,\beta,t,f)\right\|^2.
$$

Here $\inf(\mathrm{range}f)$ is the infimum of the values of $f$, i.e. $\inf_{x\in H}f(x)$.

The conclusion then says that for every $t\ge t_{\mathrm{start}}$,

$$
f\!\left(u(t)+\frac{t}{4}u'(t)\right)-\inf f
\le
\frac{(\alpha-2)E_1}{4t^3},
$$

and

$$
f(u(t))-\inf f
\le
\frac{
t_{\mathrm{start}}^4\bigl(f(u(t_{\mathrm{start}}))-\inf f\bigr)
-(\alpha-2)E_1t_{\mathrm{start}}
}{t^4}
+\frac{(\alpha-2)E_1}{t^3},
$$

and the function

$$
s\mapsto f(u(s))+\frac{(\alpha-2)E_1}{3s^3}
$$

is antitone on $[t_{\mathrm{start}},\infty)$. Finally, if $0<\beta$, then

$$
\int_{[t_{\mathrm{start}},\infty)}
s^4
\left\|
\nabla f\!\left(u(s)+\frac{s}{4}u'(s)\right)
\right\|^2
\,ds
\le
\frac{(\alpha-2)E_1}{\beta},
$$

where $\nabla f$ is `gradient f`.

Thus the theorem gives an objective-value decay rate of order $t^{-3}$ at the auxiliary point $u(t)+\frac{t}{4}u'(t)$, a mixed $t^{-4}$ and $t^{-3}$ estimate for $f(u(t))-\inf f$, monotonicity of a Lyapunov-type expression, and integrability of the weighted squared gradient norm along the auxiliary trajectory.

## Lean proof
```lean
2 * beta * (alpha - 2) / (alpha - 3)
      let tStart := max t0 t1
      let E1 := togesVLyapunov f u z alpha beta tStart
      ∀ t ≥ tStart,
        f (u t + (t / 4) • deriv u t) - sInf (Set.range f) ≤ (alpha - 2) * E1 / (4 * t ^ 3) ∧
        f (u t) - sInf (Set.range f) ≤
          (tStart ^ 4 * (f (u tStart) - sInf (Set.range f)) - (alpha - 2) * E1 * tStart) / t ^ 4 +
            (alpha - 2) * E1 / t ^ 3 ∧
        AntitoneOn (fun s => f (u s) + (alpha - 2) * E1 / (3 * s ^ 3)) (Set.Ici tStart) ∧
        (0 < beta → ∫ s in Set.Ici tStart, s ^ 4 *
            ‖gradient f (u s + (s / 4) • deriv u s)‖ ^ 2 ≤ (alpha - 2) * E1 / beta) := by
  have hGradient : ∀ x, HasFDerivAt f (innerSL ℝ (gradient f x)) x := by
    intro x
    simpa [innerSL_apply_apply] using
      ((hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have huDiff : Differentiable ℝ u := hUContDiff.differentiable (by norm_num)
  have hFirstDiff : Differentiable ℝ (deriv u) :=
    (hUContDiff.of_le (by norm_num)).differentiable_deriv_two
  have hSecondDiff : Differentiable ℝ (deriv (deriv u)) := by
    exact hUContDiff.deriv'.differentiable_deriv_two
  have hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      exact (huDiff t).hasDerivAt
    · intro t _
      exact (hFirstDiff t).hasDerivAt
    · intro t _
      exact (hSecondDiff t).hasDerivAt
  have hGradientContDiff : ContDiff ℝ 1 (gradient f) := by
    have hfderivContDiff : ContDiff ℝ 1 (fderiv ℝ f) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) f by simpa using hFContDiff)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderivContDiff
  have hGradientDerivative : ∀ t, t0 ≤ t → HasDerivAt
      (fun s => gradient f (u s + (s / 4) • deriv u s))
      (fderiv ℝ (gradient f) (u t + (t / 4) • deriv u t)
        ((5 / 4 : ℝ) • deriv u t + (t / 4) • deriv (deriv u) t)) t := by
    intro t ht
    have hv := togesVH_auxiliary_hasDerivAt u (deriv u) (deriv (deriv u)) t0
      (fun s _ => (huDiff s).hasDerivAt)
      (fun s _ => (hFirstDiff s).hasDerivAt) t ht
    exact (hGradientContDiff.differentiable (by norm_num)
      (u t + (t / 4) • deriv u t)).hasFDerivAt.comp_hasDerivAt t hv
  exact togesVH_rate_descent_and_integrability_core f u (deriv u) (deriv (deriv u))
    (deriv (deriv (deriv u))) z alpha beta t0 hConvex hGradient hGradientDerivative
    hMin ht0pos hRegularity.1 hRegularity.2.1 hRegularity.2.2
    (fun t => ⟨rfl, rfl, rfl⟩) hTrajectory
```

## Proof explanation
The proof reduces the smoothness hypotheses to the pointwise derivative hypotheses required by the private core theorem `togesVH_rate_descent_and_integrability_core`.

First, the proof establishes

$$
\forall x,\quad \mathrm{HasFDerivAt} f(\mathrm{innerSL} \mathbb R(\nabla f(x)))x.
$$

For arbitrary $x$, the hypothesis `hFContDiff : ContDiff ℝ 2 f` gives differentiability of $f$ at $x$. Since $H$ is an inner product space, the gradient $\nabla f(x)$ is the Riesz representative of the Fréchet derivative, so the derivative is the continuous linear functional

$$
h\mapsto \langle \nabla f(x),h\rangle.
$$

The simplification `innerSL_apply_apply` identifies `innerSL ℝ (gradient f x)` with this inner-product functional. This is exactly the `hGradientDirect` hypothesis needed by the core theorem.

Next, the proof records differentiability of $u$, of $u'$, and of $u''$:

- `huDiff : Differentiable ℝ u` follows from $u$ being $C^3$, hence in particular differentiable.
- `hFirstDiff : Differentiable ℝ (deriv u)` follows because $u$ is $C^3$, hence $u$ is $C^2$, so its derivative $u'$ is differentiable.
- `hSecondDiff : Differentiable ℝ (deriv (deriv u))` follows because $u'$ is $C^2$, so $u''$ is differentiable.

The `by norm_num` arguments discharge the numerical order conditions in these regularity implications.

The proof then packages the derivative relations into

$$
\begin{aligned}
&\forall t,\ t_0\le t\to \mathrm{HasDerivAt} u\ (u'(t))\ t,\\
&\forall t,\ t_0\le t\to \mathrm{HasDerivAt} u'\ (u''(t))\ t,\\
&\forall t,\ t_0\le t\to \mathrm{HasDerivAt} u''\ (u'''(t))\ t.
\end{aligned}
$$

This is the `hRegularity` conjunction. The tactic `refine ⟨?_, ?_, ?_⟩` splits the conjunction into three goals. In each branch, `intro t _` fixes a real $t$ and discards the inequality $t_0\le t$, which is not needed because differentiability is global. Then `.hasDerivAt` converts differentiability at $t$ into the corresponding `HasDerivAt` statement. These three facts become the `hu`, `hFirst`, and `hSecond` hypotheses of the core theorem.

The proof also shows that the gradient map is $C^1$:

$$
\mathrm{ContDiff}\mathbb R 1(\nabla f).
$$

From `hFContDiff : ContDiff ℝ 2 f`, the lemma `contDiff_succ_iff_fderiv` extracts that the Fréchet derivative $Df$ is $C^1$. The Riesz isomorphism `InnerProductSpace.toDual ℝ H` identifies $Df(x)$ with $\nabla f(x)$; composing its inverse with $Df$ gives the gradient. Since continuous linear equivalences are smooth, this composition is $C^1$. This regularity of $\nabla f$ is used to apply the chain rule to $s\mapsto \nabla f(u(s)+(s/4)u'(s))$.

Next the proof establishes that for every $t\ge t_0$,

$$
\frac{d}{dt}\nabla f\!\left(u(t)+\frac{t}{4}u'(t)\right)
=D(\nabla f)\!\left(u(t)+\frac{t}{4}u'(t)\right)
\!\left(\frac54 u'(t)+\frac{t}{4}u''(t)\right).
$$

The auxiliary theorem `togesVH_auxiliary_hasDerivAt` is applied to `u`, `deriv u`, and `deriv (deriv u)`. Its hypotheses are exactly the differentiability facts for $u$ and $u'$. It gives

$$
s\mapsto u(s)+\frac{s}{4}u'(s)
$$

has derivative

$$
\frac54 u'(t)+\frac{t}{4}u''(t)
$$

at $t$. Since $\nabla f$ is differentiable at the point $u(t)+(t/4)u'(t)$, the chain rule `HasFDerivAt.comp_hasDerivAt` gives the displayed derivative of the composition. The resulting statement is exactly the `hGradientDerivativeDirect` hypothesis required by the core theorem.

Finally, the proof invokes
`togesVH_rate_descent_and_integrability_core` with

$$
f,\quad u,\quad u',\quad u'',\quad u''',\quad z,\quad \alpha,\quad \beta,\quad t_0.
$$

The supplied arguments match the core theorem’s hypotheses: `hConvex` for convexity, `hGradient` for the direct gradient identification, `hGradientDerivative` for the derivative of the gradient along the auxiliary trajectory, `hMin` for global minimality, `ht0pos` for $t_0>0$, `hRegularity.1` for the derivative of $u$, `hRegularity.2.1` for the derivative of $u'$, and `hRegularity.2.2` for the derivative of $u''$. The pointwise compatibility with Lean’s `deriv` is supplied by `(fun t => ⟨rfl, rfl, rfl⟩)`, since the chosen first, second, and third derivatives are literally the corresponding iterated `deriv` expressions. The TOGES-V H trajectory hypothesis `hTrajectory` is passed unchanged.

The core theorem then yields exactly the implication stated in the target theorem: under $3<\alpha$ and $0\le\beta$, with $t_1$, $t_{\mathrm{start}}$, and $E_1$ as above, the four assertions about the objective decay, the antitone Lyapunov expression, and the weighted gradient integrability hold. Therefore the final `exact` application closes the proof.

