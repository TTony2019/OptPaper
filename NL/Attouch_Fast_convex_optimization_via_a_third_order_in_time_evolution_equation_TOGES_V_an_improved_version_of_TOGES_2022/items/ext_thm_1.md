## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_thm_1.lean`

## Lean statement
```lean
theorem attouch_chbani_riahi_toges_rate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (u : ℝ → H) (alpha t0 : ℝ)
    (hConvex : ConvexOn ℝ Set.univ f)
    (hGradient : ∀ x : H, HasFDerivAt f (innerSL ℝ (gradient f x)) x)
    (hMin : ∃ z, IsMinOn f Set.univ z) (ht0pos : 0 < t0)
    (hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t))
    (hTrajectory : IsTOGES alpha u f t0) (hAlpha : 3 ≤ alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ≥ t0,
      f (u t + t • deriv u t) - sInf (Set.range f) ≤ C / t ^ 3 ∧
      f (u t) - sInf (Set.range f) ≤
        (t0 * (f (u t0) - sInf (Set.range f)) + C / (2 * t0 ^ 2)) / t
```

## Statement explanation
The declaration is a theorem in a real Hilbert space \(H\): the assumptions `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H` together give \(H\) the structure of a complete real inner product space. The fixed data are a function \(f:H\to\mathbb R\), a curve \(u:\mathbb R\to H\), and real parameters \(\alpha\) and \(t_0\).

The hypotheses are as follows. The function \(f\) is convex on all of \(H\), expressed by `ConvexOn ℝ Set.univ f`. For every \(x\in H\), \(f\) has Fréchet derivative at \(x\) given by the continuous linear functional \(y\mapsto \langle \operatorname{gradient} f x,y\rangle\), expressed by `HasFDerivAt f (innerSL ℝ (gradient f x)) x`; this says that `gradient f x` is the gradient vector of \(f\) at \(x\). There is a global minimizer of \(f\): some \(z\) satisfies `IsMinOn f Set.univ z`, i.e. \(f(z)\le f(x)\) for all \(x\in H\). The initial time is positive: \(0<t_0\). The curve \(u\) is three times classically differentiable on \([t_0,\infty)\): for every \(t\ge t_0\), \(u\) has derivative \(\operatorname{deriv}u(t)\), \(\operatorname{deriv}u\) has derivative \(\operatorname{deriv}(\operatorname{deriv}u)(t)\), and \(\operatorname{deriv}(\operatorname{deriv}u)\) has derivative \(\operatorname{deriv}(\operatorname{deriv}(\operatorname{deriv}u))(t)\). The curve also satisfies the TOGES trajectory condition `IsTOGES alpha u f t0` with parameter \(\alpha\), objective \(f\), and starting time \(t_0\). Finally, \(3\le \alpha\).

The conclusion is that there exists a positive real constant \(C\) such that for every \(t\ge t_0\),
\[
f\bigl(u(t)+t\,\operatorname{deriv}u(t)\bigr)-\inf_{x\in H}f(x)\le \frac{C}{t^3}
\]
and
\[
f(u(t))-\inf_{x\in H}f(x)
\le
\frac{t_0\bigl(f(u(t_0))-\inf_{x\in H}f(x)\bigr)+C/(2t_0^2)}{t}.
\]
Here \(\inf_{x\in H}f(x)\) is the value `sInf (Set.range f)`, the infimum of the range of \(f\); because a minimizer is assumed to exist, it is the global minimum of \(f\). Thus the theorem gives a third-order decay estimate for the suboptimality at the extrapolated point \(u(t)+t\dot u(t)\), and a first-order-in-time bound for the suboptimality at \(u(t)\), with the constant \(C\) independent of \(t\). The internal differential equation encoded by `IsTOGES` is not displayed in the supplied context; the proof uses it as the final condition of the classical TOGES predicate.

## Lean proof
```lean
by
  exact attouch_chbani_riahi_toges_rate_core f u (deriv u) (deriv (deriv u))
    (deriv (deriv (deriv u))) (gradient f) alpha t0 hConvex hGradient hMin
    ⟨ht0pos, hRegularity.1, hRegularity.2.1, hRegularity.2.2, hTrajectory⟩ hAlpha
```

## Proof explanation
The proof is a direct application of the cited core theorem `attouch_chbani_riahi_toges_rate_core`. That theorem states, in the same Hilbert-space setting, that if \(f\) is convex, if a map \(g:H\to H\) represents the gradient of \(f\) by the Fréchet derivative \(y\mapsto \langle g(x),y\rangle\) at every \(x\), if \(f\) has a global minimizer, if a curve \(u\) is a classical TOGES trajectory with first three derivative functions \(u_1,u_2,u_3\) and gradient map \(g\), and if \(3\le\alpha\), then there is \(C>0\) such that for all \(t\ge t_0\),
\[
f\bigl(u(t)+t\,u_1(t)\bigr)-\inf f\le \frac{C}{t^3}
\]
and
\[
f(u(t))-\inf f
\le
\frac{t_0(f(u(t_0))-\inf f)+C/(2t_0^2)}{t}.
\]
This is exactly the target conclusion after specializing \(u_1=\operatorname{deriv}u\), \(u_2=\operatorname{deriv}(\operatorname{deriv}u)\), \(u_3=\operatorname{deriv}(\operatorname{deriv}(\operatorname{deriv}u))\), and \(g=\operatorname{gradient}f\).

The proof therefore supplies to the core theorem the same function \(f\), the same curve \(u\), the derivative functions just listed, the gradient map \(\operatorname{gradient}f\), and the parameters \(\alpha,t_0\). The hypotheses `hConvex`, `hGradient`, `hMin`, and `hAlpha` are passed unchanged, since they already have the required types. In particular, the target hypothesis `hGradient` says precisely that \(f\) has Fréchet derivative given by the inner product with `gradient f x`, so it matches the core theorem’s gradient hypothesis with \(g=\operatorname{gradient}f\).

The remaining core hypothesis is that \(u\) is a classical TOGES trajectory. The proof builds this by the anonymous constructor \(\langle\dots\rangle\), whose five components are exactly the needed fields. First, `ht0pos` gives \(0<t_0\). Next, `hRegularity.1` gives the differentiability of \(u\) on \([t_0,\infty)\) with derivative \(\operatorname{deriv}u(t)\). Then `hRegularity.2.1` gives the differentiability of \(\operatorname{deriv}u\) on \([t_0,\infty)\) with derivative \(\operatorname{deriv}(\operatorname{deriv}u)(t)\), and `hRegularity.2.2` gives the differentiability of \(\operatorname{deriv}(\operatorname{deriv}u)\) on \([t_0,\infty)\) with derivative \(\operatorname{deriv}(\operatorname{deriv}(\operatorname{deriv}u))(t)\). Finally, `hTrajectory` supplies the condition `IsTOGES alpha u f t0`, which is the remaining TOGES equation condition required by the classical TOGES predicate when the gradient map is \(\operatorname{gradient}f\). Hence the constructed tuple has the type `IsClassicalTOGES` with the intended derivative and gradient arguments.

The command `exact` then closes the goal by providing the conclusion of the core theorem. The surrounding `by` merely opens tactic mode, and `exact` says that the following term is a proof of the goal. The notation \(\langle\dots\rangle\) is Lean’s anonymous constructor for a structure or conjunction, and the projections `.1`, `.2.1`, `.2.2` extract the three derivative clauses from `hRegularity`. No `intro`, `rw`, `simp`, or `linarith` is used; the proof contains no additional rewriting, simplification, or arithmetic reasoning beyond repackaging the hypotheses and applying the core rate theorem.

