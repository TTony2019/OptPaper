## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_8.lean`

## Lean statement
```lean
theorem theorem_5_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {t₀ s₀ r α : ℝ} (hr : 0 < r) (hs₀ : 0 < s₀) (hα : 1 < α) (x₀ : H) (z g v w dw ddw : ℝ → H)
    (f : H → ℝ) (gradFstar gradPsiStar : H → H)
    (hessFstar : H → H →L[ℝ] H)
    (hgradFstar : ∀ q v,
      fderiv ℝ (fun q => (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal) q v =
        inner ℝ (gradFstar q) v)
    (hhessFstar : ∀ q v, fderiv ℝ gradFstar q v = hessFstar q v)
    (hgradFstar_smooth : ∀ q, HasFDerivAt gradFstar (hessFstar q) q)
    (_hsol : IsDrygradTrajectory r f z t₀)
    (hdualFlow : ∃ p : ℝ → H, ∀ t ∈ Set.Ici t₀, g t = gradient f (z t) ∧
      p t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt (fun u => gradFstar (g u)) (p t - g t) t)
    (hscale : ∀ s ∈ Set.Ici s₀, v s = g (s ^ 2 / (2 * (α - 1))) ∧
      HasDerivAt w (dw s) s ∧ HasDerivAt dw (ddw s) s ∧
        dw s + ((α - 1) / s) • (w s - v s) = 0)
    (hτIci : ∀ s ∈ Set.Ici s₀, s ^ 2 / (2 * (α - 1)) ∈ Set.Ici t₀)
    (_hw₀ : w s₀ = v s₀ ∧ v s₀ = x₀)
    (hv_deriv : ∀ s ∈ Set.Ici s₀,
      HasDerivAt v ((s / (α - 1)) • (ddw s + (α / s) • dw s)) s)
    (hdualScaled : ∀ s ∈ Set.Ici s₀,
      HasDerivAt (fun u => gradFstar (v u))
        ((s / (α - 1)) • (Classical.choose hdualFlow
          (s ^ 2 / (2 * (α - 1))) - v s)) s)
    (hv_decay : Filter.Tendsto (fun s : ℝ => s * Metric.infDist (v s) (frictionBall r)) Filter.atTop (nhds 0))
    (hw_decay : Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r)) Filter.atTop (nhds 0))
    (hpsi : ∀ u q, q ∈ frictionBallProjector r u → gradPsiStar u = u - q) :
    IsDryStarDualInertial r α s₀
      (fun q => (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal)
      gradFstar hessFstar gradPsiStar hgradFstar hhessFstar w dw ddw ∧
    Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s + (s / (α - 1)) • dw s) (frictionBall r)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r)) Filter.atTop (nhds 0)
```

## Statement explanation
The theorem is set in a complete real inner product space $H$. It fixes real parameters $r,s_0,\alpha$ with $r>0$, $s_0>0$, and $\alpha>1$, an initial vector $x_0\in H$, curves $z,g,v,w,dw,ddw:\mathbb R\to H$, a function $f:H\to\mathbb R$, maps $\operatorname{gradFstar},\operatorname{gradPsiStar}:H\to H$, and a map $\operatorname{hessFstar}:H\to H\to_L H$ whose values are continuous linear maps from $H$ to $H$.

The hypothesis `hgradFstar` says that if $F^*$ denotes the real-valued function obtained by taking the extended-real Fenchel conjugate of $f$ and converting back to a real number, then for all $q,v\in H$,

$$
D F^*(q)(v)=\left\langle \operatorname{gradFstar}(q),v\right\rangle .
$$

Thus $\operatorname{gradFstar}$ is the gradient of this conjugate. The hypothesis `hhessFstar` says that for all $q,v$,

$$
D\operatorname{gradFstar}(q)(v)=\operatorname{hessFstar}(q)(v),
$$

so $\operatorname{hessFstar}(q)$ is the derivative of $\operatorname{gradFstar}$ at $q$. The hypothesis `hgradFstar_smooth` strengthens this pointwise fact to the statement that $\operatorname{gradFstar}$ is Fréchet differentiable at every $q$ with derivative $\operatorname{hessFstar}(q)$.

The remaining hypotheses describe a scaled dry-gradient flow and its projection structure. The hypothesis `_hsol` says that $z$ is a dry gradient trajectory for the radius $r$ and the function $f$, starting at $t_0$. The hypothesis `hdualFlow` states that there exists a curve $p:\mathbb R\to H$ such that for every $t\ge t_0$,

$$
g(t)=\nabla f(z(t)),\qquad
p(t)\in \operatorname{frictionBallProjector}_r(g(t)),\qquad
(\operatorname{gradFstar}\circ g)'(t)=p(t)-g(t).
$$

Here $\operatorname{frictionBallProjector}_r(x)$ is by definition the set of all $p$ such that $p$ is a friction-ball best approximation of $x$ with radius $r$.

The hypothesis `hscale` uses the scaled time

$$
\tau(s)=\frac{s^2}{2(\alpha-1)}.
$$

For every $s\ge s_0$, it says that

$$
v(s)=g(\tau(s)),\qquad
w'(s)=dw(s),\qquad
dw'(s)=ddw(s),
$$

and

$$
dw(s)+\frac{\alpha-1}{s}\bigl(w(s)-v(s)\bigr)=0.
$$

The hypothesis `hτIci` says that $\tau(s)\ge t_0$ whenever $s\ge s_0$. The hypothesis `_hw₀` gives the initial condition $w(s_0)=v(s_0)=x_0$. The hypothesis `hv_deriv` says that for $s\ge s_0$,

$$
v'(s)=\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right).
$$

The hypothesis `hdualScaled` says that for the chosen curve $p$ from `hdualFlow`, and for every $s\ge s_0$,

$$
(\operatorname{gradFstar}\circ v)'(s)
=\frac{s}{\alpha-1}\bigl(p(\tau(s))-v(s)\bigr).
$$

The decay hypotheses `hv_decay` and `hw_decay` say that

$$
\lim_{s\to\infty}s\,\operatorname{infDist}(v(s),\operatorname{frictionBall}r)=0,
\qquad
\lim_{s\to\infty}s\,\operatorname{infDist}(w(s),\operatorname{frictionBall}r)=0.
$$

Finally, `hpsi` says that whenever $q\in\operatorname{frictionBallProjector}_r(u)$,

$$
\operatorname{gradPsiStar}(u)=u-q.
$$

Thus $\operatorname{gradPsiStar}$ is identified with the residual of the friction-ball projection.

The conclusion has three parts. The first part is

$$
\operatorname{IsDryStarDualInertial}
  r\,\alpha\,s_0\,F^*
  \operatorname{gradFstar}\operatorname{hessFstar}\operatorname{gradPsiStar}
  hgradFstar\,hhessFstar\,w\,dw\,ddw.
$$

By the supplied definition, this means that for every $s\ge s_0$,

$$
w'(s)=dw(s),\qquad dw'(s)=ddw(s),
$$

and

$$
\operatorname{hessFstar}\!\left(w(s)+\frac{s}{\alpha-1}dw(s)\right)
\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)
+\operatorname{gradPsiStar}\!\left(w(s)+\frac{s}{\alpha-1}dw(s)\right)=0.
$$

In the definition as given, the parameters $r$, $F^*$, $\operatorname{gradFstar}$ and the two gradient-consistency hypotheses are arguments to the definition, but the displayed body only uses $\alpha$, $s_0$, $\operatorname{hessFstar}$, $\operatorname{gradPsiStar}$, and the curves $w,dw,ddw$.

The second and third conclusions are the two asymptotic decay statements

$$
\lim_{s\to\infty}s\,\operatorname{infDist}\!\left(w(s)+\frac{s}{\alpha-1}dw(s),\operatorname{frictionBall}r\right)=0
$$

and

$$
\lim_{s\to\infty}s\,\operatorname{infDist}(w(s),\operatorname{frictionBall}r)=0.
$$

Thus the theorem transfers the scaled dry-gradient dynamics to a star-dual inertial equation for $w$, with $\operatorname{gradPsiStar}$ supplied by the projected residual, and it concludes the corresponding scale-invariant decay of the residuals.

## Lean proof
```lean
by
  constructor
  · unfold IsDryStarDualInertial
    intro s hs
    refine ⟨(hscale s hs).2.1, (hscale s hs).2.2.1, ?_⟩
    have hv_eq := scaled_point_eq_v hs₀ hα hs (hscale s hs).2.2.2
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hτpos : 0 < s / (α - 1) := div_pos hspos (sub_pos.mpr hα)
    have hτne : s / (α - 1) ≠ 0 := ne_of_gt hτpos
    let p : ℝ → H := Classical.choose hdualFlow
    have hpflow : ∀ t ∈ Set.Ici t₀, g t = gradient f (z t) ∧
        p t ∈ frictionBallProjector r (g t) ∧
          HasDerivAt (fun u => gradFstar (g u)) (p t - g t) t :=
      Classical.choose_spec hdualFlow
    have hp : p (s ^ 2 / (2 * (α - 1))) ∈ frictionBallProjector r
        (g (s ^ 2 / (2 * (α - 1)))) := (hpflow _ (hτIci s hs)).2.1
    have hdual' : HasDerivAt (fun u => gradFstar (v u))
        ((s / (α - 1)) • (p (s ^ 2 / (2 * (α - 1))) - v s)) s := by
      simpa only [p] using hdualScaled s hs
    have hv' : HasDerivAt v ((s / (α - 1)) • (ddw s + (α / s) • dw s)) s := hv_deriv s hs
    have hgrad : HasDerivAt (fun u => gradFstar (v u))
        (hessFstar (v s) ((s / (α - 1)) • (ddw s + (α / s) • dw s))) s :=
      (hgradFstar_smooth (v s)).comp_hasDerivAt s hv'
    have heq := hgrad.unique hdual'
    rw [ContinuousLinearMap.map_smul] at heq
    have hmain : hessFstar (v s) (ddw s + (α / s) • dw s) = p (s ^ 2 / (2 * (α - 1))) - v s :=
      smul_right_injective H hτne heq
    have hps : p (s ^ 2 / (2 * (α - 1))) ∈ frictionBallProjector r (v s) := by
      simpa only [(hscale s hs).1] using hp
    rw [hv_eq, hmain, hpsi _ _ hps]
    abel
  constructor
  · apply hv_decay.congr'
    filter_upwards [Filter.eventually_ge_atTop s₀] with s hs
    rw [scaled_point_eq_v hs₀ hα hs (hscale s hs).2.2.2]
  · exact hw_decay
```

## Proof explanation
The proof begins with `constructor`, splitting the conclusion into the first conjunct, namely the `IsDryStarDualInertial` statement, and the remaining conjunction of the two decay limits. A second `constructor` later splits that remaining conjunction.

For the first conjunct, the proof executes `unfold IsDryStarDualInertial` and then `intro s hs`, fixing an arbitrary $s$ with $s\in\operatorname{Set.Ici}s_0$, i.e. $s\ge s_0$. The definition of `IsDryStarDualInertial` requires three facts at this $s$: differentiability of $w$ with derivative $dw(s)$, differentiability of $dw$ with derivative $ddw(s)$, and the second-order equation. The proof uses `refine` with

$$
(hscale\,s\,hs).2.1,\qquad (hscale\,s\,hs).2.2.1,\qquad ?_,
$$

so the first two differentiability requirements are exactly the corresponding components of `hscale`, specialized to $s\ge s_0$. The remaining goal is the second-order equation.

To prove that equation, the proof first applies the cited private theorem `scaled_point_eq_v`. Its concrete content is as follows: if $0<s_0$, $\alpha>1$, $s\ge s_0$, and

$$
dw(s)+\frac{\alpha-1}{s}\bigl(w(s)-v(s)\bigr)=0,
$$

then

$$
w(s)+\frac{s}{\alpha-1}dw(s)=v(s).
$$

Indeed, multiplying the displayed ODE by $s/(\alpha-1)$ gives

$$
\frac{s}{\alpha-1}dw(s)+w(s)-v(s)=0,
$$

hence the stated equality. The hypothesis `(hscale s hs).2.2.2` is precisely the ODE needed, so `hv_eq` gives

$$
w(s)+\frac{s}{\alpha-1}dw(s)=v(s).
$$

This is the key identification that replaces the scaled point in the dual inertial equation by $v(s)$.

The proof then records $s>0$ because $s\ge s_0>0$, and

$$
\frac{s}{\alpha-1}>0
$$

because $s>0$ and $\alpha-1>0$. Therefore

$$
\frac{s}{\alpha-1}\ne 0.
$$

This nonzero scalar will later be cancelled.

Next, the proof chooses the witness curve from `hdualFlow`. Since `hdualFlow` is an existential statement, `Classical.choose hdualFlow` selects a curve $p$, and `Classical.choose_spec hdualFlow` supplies its defining property: for every $t\ge t_0$,

$$
g(t)=\nabla f(z(t)),\qquad
p(t)\in\operatorname{frictionBallProjector}_r(g(t)),\qquad
(\operatorname{gradFstar}\circ g)'(t)=p(t)-g(t).
$$

Using `hτIci s hs`, which says $\tau(s)\ge t_0$, the proof obtains

$$
p(\tau(s))\in\operatorname{frictionBallProjector}_r(g(\tau(s))).
$$

Since `hscale` gives $v(s)=g(\tau(s))$, the proof rewrites this to

$$
p(\tau(s))\in\operatorname{frictionBallProjector}_r(v(s)).
$$

This membership is called `hps`.

The proof now compares two derivatives of the composite function $u\mapsto \operatorname{gradFstar}(v(u))$ at $s$. From `hdualScaled s hs`, after unfolding the local definition of $p$, the derivative is

$$
\frac{s}{\alpha-1}\bigl(p(\tau(s))-v(s)\bigr).
$$

From `hv_deriv s hs`, the derivative of $v$ at $s$ is

$$
v'(s)=\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right).
$$

The hypothesis `hgradFstar_smooth (v s)` says that $\operatorname{gradFstar}$ has Fréchet derivative $\operatorname{hessFstar}(v(s))$ at the point $v(s)$. Therefore the chain rule `HasFDerivAt.comp_hasDerivAt` gives that the derivative of $u\mapsto \operatorname{gradFstar}(v(u))$ at $s$ is

$$
\operatorname{hessFstar}(v(s))
\left(\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)\right).
$$

Since a function has at most one derivative at a point, `HasDerivAt.unique` equates the two derivative expressions:

$$
\operatorname{hessFstar}(v(s))
\left(\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)\right)
=
\frac{s}{\alpha-1}\bigl(p(\tau(s))-v(s)\bigr).
$$

Because $\operatorname{hessFstar}(v(s))$ is a continuous linear map, `ContinuousLinearMap.map_smul` rewrites the left side as

$$
\frac{s}{\alpha-1}\,
\operatorname{hessFstar}(v(s))
\left(ddw(s)+\frac{\alpha}{s}dw(s)\right).
$$

Since $\frac{s}{\alpha-1}\ne0$, the scalar multiplication map $x\mapsto \frac{s}{\alpha-1}\cdot x$ is injective. The lemma `smul_right_injective H hτne` applies this cancellation and yields the key identity

$$
\operatorname{hessFstar}(v(s))
\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)
=
p(\tau(s))-v(s).
$$

Now the hypothesis `hpsi` is used with $u=v(s)$ and $q=p(\tau(s))$. The membership `hps` states that $p(\tau(s))$ lies in the friction-ball projector of $v(s)$, so `hpsi` gives

$$
\operatorname{gradPsiStar}(v(s))=v(s)-p(\tau(s)).
$$

The goal for the second-order equation originally has the form

$$
\operatorname{hessFstar}\!\left(w(s)+\frac{s}{\alpha-1}dw(s)\right)
\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)
+\operatorname{gradPsiStar}\!\left(w(s)+\frac{s}{\alpha-1}dw(s)\right)=0.
$$

The proof rewrites the scaled point by `hv_eq`, replaces the Hessian term by the identity just obtained, and replaces the $\operatorname{gradPsiStar}$ term by $v(s)-p(\tau(s))$. The goal then becomes

$$
\bigl(p(\tau(s))-v(s)\bigr)+\bigl(v(s)-p(\tau(s))\bigr)=0.
$$

The `abel` tactic closes this additive cancellation in the abelian group $H$. This proves the `IsDryStarDualInertial` conjunct.

For the second conjunct, the proof must show

$$
\lim_{s\to\infty}s\,\operatorname{infDist}\!\left(w(s)+\frac{s}{\alpha-1}dw(s),\operatorname{frictionBall}r\right)=0.
$$

It starts from `hv_decay`, which is the same limit with $v(s)$ in place of the scaled point. The command `apply hv_decay.congr'` invokes the congruence property of limits: if a function tends to a limit and another function is eventually equal to it, then the second function has the same limit. The proof then uses `filter_upwards [Filter.eventually_ge_atTop s₀]` to reduce the eventual equality to an arbitrary $s\ge s_0$. For such $s$, the theorem `scaled_point_eq_v` again gives

$$
w(s)+\frac{s}{\alpha-1}dw(s)=v(s).
$$

Hence the two functions $s\mapsto s\,\operatorname{infDist}(v(s),\operatorname{frictionBall}r)$ and

$$
s\mapsto s\,\operatorname{infDist}\!\left(w(s)+\frac{s}{\alpha-1}dw(s),\operatorname{frictionBall}r\right)
$$

agree eventually, so the decay for $v$ transfers to the scaled point.

The third conjunct is

$$
\lim_{s\to\infty}s\,\operatorname{infDist}(w(s),\operatorname{frictionBall}r)=0,
$$

which is exactly the hypothesis `hw_decay`. The proof therefore finishes with `exact hw_decay`.

