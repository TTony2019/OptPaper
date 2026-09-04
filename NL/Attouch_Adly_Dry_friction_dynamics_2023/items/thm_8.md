## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_8.lean`

## Lean statement
```lean
theorem theorem_5_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (hs₀ : 0 < s₀) (hα : 1 < α) (x₀ : H) (z dz g v w dw ddw : ℝ → H)
    (f : H → ℝ) (fstar : H → ℝ) (gradFstar gradPsiStar : H → H)
    (hf : Differentiable ℝ f)
    (hessFstar : H → H →L[ℝ] H)
    (_hconjugate : ∀ q, fstar q = (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal)
    (hgradFstar : ∀ q v, fderiv ℝ fstar q v = inner ℝ (gradFstar q) v)
    (hhessFstar : ∀ q v, fderiv ℝ gradFstar q v = hessFstar q v)
    (hgradFstar_smooth : ∀ q, HasFDerivAt gradFstar (hessFstar q) q)
    (_hsol : IsDrygradTrajectory r hr f hf z dz s₀)
    (hdualFlow : ∃ p : ℝ → H, ∀ t ∈ Set.Ici s₀, g t = gradient f (z t) ∧
      p t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt (fun u => gradFstar (g u)) (p t - g t) t)
    (hscale : ∀ s ∈ Set.Ici s₀, v s = g (s ^ 2 / (2 * (α - 1))) ∧
      HasDerivAt w (dw s) s ∧ HasDerivAt dw (ddw s) s ∧
        dw s + ((α - 1) / s) • (w s - v s) = 0)
    (hτIci : ∀ s ∈ Set.Ici s₀, s ^ 2 / (2 * (α - 1)) ∈ Set.Ici s₀)
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
    IsDryStarDualInertial r α s₀ fstar gradFstar hessFstar gradPsiStar hgradFstar hhessFstar w dw ddw ∧
    Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s + (s / (α - 1)) • dw s) (frictionBall r)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r)) Filter.atTop (nhds 0)
```

## Statement explanation
The theorem assumes a complete real inner product space \(H\). The real parameters are \(s_0,r,\alpha\), with hypotheses \(0<r\), \(0<s_0\), and \(1<\alpha\). The initial point is \(x_0\in H\). The data include functions \(z,dz,g,v,w,dw,ddw:\mathbb R\to H\), an objective \(f:H\to\mathbb R\), a dual function \(f^\star:H\to\mathbb R\), gradient maps \(\nabla f^\star,\nabla \Psi^\star:H\to H\), and a Hessian \(\nabla^2 f^\star:H\to H\toL[\mathbb R]H\).

The hypotheses are:
- \(f\) is differentiable over \(\mathbb R\).
- \(f^\star\) is the real-valued Fenchel conjugate of \(f\) in the extended-real sense.
- For all \(q,v\), the Fréchet derivative of \(f^\star\) at \(q\) in direction \(v\) is \(\langle \nabla f^\star(q),v\rangle\).
- For all \(q,v\), the Fréchet derivative of \(\nabla f^\star\) at \(q\) in direction \(v\) is \([\nabla^2 f^\star(q)]v\).
- \(\nabla f^\star\) is Fréchet differentiable everywhere with derivative \(\nabla^2 f^\star\).
- \(z\) is a dry gradient trajectory with derivative \(dz\) on \([s_0,\infty)\).
- There exists a dual path \(p\) such that for every \(t\ge s_0\), \(g(t)=\nabla f(z(t))\), \(p(t)\) belongs to the friction ball projection of \(g(t)\), and the derivative of \(t\mapsto \nabla f^\star(g(t))\) is \(p(t)-g(t)\).
- For every \(s\ge s_0\), \(v(s)=g(\tau(s))\) with \(\tau(s)=s^2/(2(\alpha-1))\), \(w'(s)=dw(s)\), \(dw'(s)=ddw(s)\), and
  \[
  dw(s)+\frac{\alpha-1}{s}(w(s)-v(s))=0.
  \]
- For every \(s\ge s_0\), \(\tau(s)\ge s_0\).
- Initial conditions: \(w(s_0)=v(s_0)\) and \(v(s_0)=x_0\).
- For every \(s\ge s_0\), the derivative of \(v\) is
  \[
  v'(s)=\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right).
  \]
- For every \(s\ge s_0\), the derivative of \(s\mapsto \nabla f^\star(v(s))\) is
  \[
  \frac{s}{\alpha-1}\left(p(\tau(s))-v(s)\right),
  \]
  where \(p\) is the path chosen from the dual-flow existence hypothesis.
- The functions \(s\, \operatorname{dist}(v(s),B_{\mathrm{fr}}(r))\) and \(s\, \operatorname{dist}(w(s),B_{\mathrm{fr}}(r))\) both tend to \(0\) as \(s\to\infty\).
- For any \(u\) and \(q\), if \(q\) is in the friction ball projection of \(u\), then \(\nabla \Psi^\star(u)=u-q\).

The conclusion has three parts:
1. The predicate \(\mathrm{IsDryStarDualInertial}\) holds for the given dual data and \(w,dw,ddw\).
2. As \(s\to\infty\),
   \[
   s\,\operatorname{dist}\left(w(s)+\frac{s}{\alpha-1}dw(s),B_{\mathrm{fr}}(r)\right)\to 0.
   \]
3. As \(s\to\infty\),
   \[
   s\,\operatorname{dist}(w(s),B_{\mathrm{fr}}(r))\to 0.
   \]

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
    have hpflow : ∀ t ∈ Set.Ici s₀, g t = gradient f (z t) ∧
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
The proof starts with `constructor`, splitting the three-part conclusion into the first predicate and the remaining two decay assertions.

For the first predicate, the proof unfolds `IsDryStarDualInertial`. After unfolding, for an arbitrary \(s\ge s_0\), it must prove three properties. The first two are supplied directly from `hscale`: \(w\) has derivative \(dw(s)\), and \(dw\) has derivative \(ddw(s)\). The remaining goal is an equation involving the Hessian and \(\nabla\Psi^\star\).

The proof first obtains the identity
\[
w(s)+\frac{s}{\alpha-1}dw(s)=v(s)
\]
using the previously proved lemma `scaled_point_eq_v`, applied to the algebraic relation in `hscale`. This identity is used to replace \(w(s)+\frac{s}{\alpha-1}dw(s)\) by \(v(s)\) in the remaining goal.

Next, the proof notes that since \(s\ge s_0>0\) and \(\alpha>1\), the scalar \(\frac{s}{\alpha-1}\) is nonzero. This will be used later to cancel scalar multiplication.

The proof then chooses a path \(p\) satisfying `hdualFlow` by classical choice. Let
\[
\tau(s)=\frac{s^2}{2(\alpha-1)}.
\]
Applying the chosen dual-flow property at \(t=\tau(s)\), and using \(h\tau Ici\), gives
\[
p(\tau(s))\in \operatorname{frictionBallProjector}_r(g(\tau(s))).
\]

The assumption `hdualScaled` gives one expression for the derivative of \(s\mapsto \nabla f^\star(v(s))\):
\[
(\nabla f^\star\circ v)'(s)
=
\frac{s}{\alpha-1}\left(p(\tau(s))-v(s)\right).
\]
On the other hand, `hv_deriv` gives
\[
v'(s)=\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right).
\]
Using the Fréchet differentiability of \(\nabla f^\star\), the chain rule gives another expression:
\[
(\nabla f^\star\circ v)'(s)
=
[\nabla^2 f^\star(v(s))]
\left(
\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)
\right).
\]
By uniqueness of derivatives, these two expressions must be equal:
\[
[\nabla^2 f^\star(v(s))]
\left(
\frac{s}{\alpha-1}\left(ddw(s)+\frac{\alpha}{s}dw(s)\right)
\right)
=
\frac{s}{\alpha-1}\left(p(\tau(s))-v(s)\right).
\]
Because \(\nabla^2 f^\star(v(s))\) is a continuous linear map, the scalar \(\frac{s}{\alpha-1}\) can be pulled out:
\[
\frac{s}{\alpha-1}\,
[\nabla^2 f^\star(v(s))]
\left(
ddw(s)+\frac{\alpha}{s}dw(s)
\right)
=
\frac{s}{\alpha-1}\left(p(\tau(s))-v(s)\right).
\]
Since \(\frac{s}{\alpha-1}\neq 0\), scalar multiplication is injective, so the proof cancels it and obtains
\[
[\nabla^2 f^\star(v(s))]
\left(
ddw(s)+\frac{\alpha}{s}dw(s)
\right)
=
p(\tau(s))-v(s).
\]

Using the equality \(v(s)=g(\tau(s))\) from `hscale`, the earlier projection membership is rewritten as
\[
p(\tau(s))\in \operatorname{frictionBallProjector}_r(v(s)).
\]
The remaining goal is then rewritten using three facts:
- `hv_eq`, replacing \(w(s)+\frac{s}{\alpha-1}dw(s)\) by \(v(s)\);
- the displayed Hessian equality just proved;
- the assumption `hpsi`, which gives
  \[
  \nabla \Psi^\star(v(s))=v(s)-p(\tau(s)).
  \]
After these rewrites, the goal becomes an algebraic identity of the form
\[
(p(\tau(s))-v(s))+(v(s)-p(\tau(s)))=0,
\]
which is solved by `abel`.

For the second and third conclusions, the proof again uses `constructor`. The first decay statement is proved using `hv_decay.congr'`. The proof shows that for all sufficiently large \(s\), namely \(s\ge s_0\), the two distance expressions are equal:
\[
w(s)+\frac{s}{\alpha-1}dw(s)=v(s).
\]
Thus the decay of
\[
s\operatorname{dist}\left(w(s)+\frac{s}{\alpha-1}dw(s),B_{\mathrm{fr}}(r)\right)
\]
follows from the already assumed decay of
\[
s\operatorname{dist}(v(s),B_{\mathrm{fr}}(r)).
\]
The final decay statement for \(w(s)\) is exactly `hw_decay`, so it is proved by `exact hw_decay`.

