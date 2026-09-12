## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/def_8.lean`

## Lean statement
```lean
def IsTOGESVR {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (lam : ERealFunction.PosReal) (prox : H → H) (u : ℝ → H)
    (alpha t0 : ℝ) (hProper : ERealFunction.IsProper f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f)) : Prop :=
  0 < (lam : ℝ) ∧
  (∀ x : H, ERealFunction.IsProxPoint
    (lam • ERealFunction.properIoi f hProper) x (prox x)) ∧
  (∀ x : H, gradient (fun y => (ERealFunction.moreauEnvelope f lam y).toReal) x =
    (1 / (lam : ℝ)) • (x - prox x)) ∧
  ∀ t : ℝ, t0 ≤ t → t ≠ 0 →
    deriv (deriv (deriv u)) t + ((alpha + 7) / t) • deriv (deriv u) t +
      (5 * (alpha + 1) / t ^ 2) • deriv u t +
      gradient (fun y => (ERealFunction.moreauEnvelope f lam y).toReal)
        (u t + (t / 4) • deriv u t) = 0
```

## Statement explanation
The declaration defines a predicate `IsTOGESVR`. Its data are a real Hilbert space \(H\), an extended-real-valued function \(f:H\to \overline{\mathbb R}\), a positive real parameter \(\lambda\) represented by `ERealFunction.PosReal`, a map \(prox:H\to H\), a curve \(u:\mathbb R\to H\), and two real parameters \(\alpha,t_0\). It also takes a proof \(hProper\) that \(f\) is proper and a proof \(hConvex\) that the epigraph of \(f\) is convex over \(\mathbb R\). The convexity proof is part of the signature, but it is not mentioned in the body of the definition; the properness proof occurs only as an argument to `ERealFunction.properIoi`.

The proposition `IsTOGESVR f lam prox u alpha t0 hProper hConvex` is a conjunction of four conditions.

First,
\[
0 < \lambda_{\mathbb R},
\]
where \(\lambda_{\mathbb R}\) is the real value obtained from the positive-real parameter `lam`.

Second, for every \(x\in H\), the point \(prox(x)\) is asserted to be a proximal point of the function
\[
\lambda_{\mathbb R}\cdot \operatorname{properIoi}(f,hProper)
\]
at \(x\). In symbols,
\[
\forall x\in H,\quad
\operatorname{IsProxPoint}
\bigl(\lambda_{\mathbb R}\cdot \operatorname{properIoi}(f,hProper),\,x,\,prox(x)\bigr).
\]
The source does not unfold `ERealFunction.properIoi` or `ERealFunction.IsProxPoint`; the visible mathematical content is that \(prox\) is tied to the proximal-point relation for that \(\lambda\)-scaled function.

Third, for every \(x\in H\),
\[
\nabla\bigl(y\mapsto (\mathcal M_\lambda f(y))_{\mathbb R}\bigr)(x)
=
\frac{1}{\lambda_{\mathbb R}}\,(x-prox(x)),
\]
where \(\mathcal M_\lambda f(y)\) denotes `ERealFunction.moreauEnvelope f lam y`, the Moreau envelope of \(f\) with parameter \(\lambda\), evaluated at \(y\), and the notation \((\mathcal M_\lambda f(y))_{\mathbb R}\) denotes the real value obtained from the extended-real value by `.toReal`. Thus this conjunct identifies the gradient of the real-valued Moreau envelope with the vector \(\frac1\lambda(x-prox(x))\).

Fourth, for every real \(t\) such that \(t_0\le t\) and \(t\neq 0\),
\[
u'''(t)+\frac{\alpha+7}{t}\,u''(t)
+\frac{5(\alpha+1)}{t^2}\,u'(t)
+\nabla\bigl(y\mapsto (\mathcal M_\lambda f(y))_{\mathbb R}\bigr)
\left(u(t)+\frac{t}{4}u'(t)\right)
=0.
\]
Here \(u'\), \(u''\), and \(u'''\) are the first, second, and third derivatives of the curve \(u:\mathbb R\to H\), and the equality takes place in \(H\). The hypothesis \(t\neq 0\) makes the divisions by \(t\) and \(t^2\) meaningful. The time interval is restricted to \(t\ge t_0\).

In summary, `IsTOGESVR` says that \(\lambda\) is positive, that `prox` is a proximal mapping associated with \(\lambda_{\mathbb R}\cdot \operatorname{properIoi}(f,hProper)\), that the gradient of the Moreau envelope of \(f\) determines \(x-prox(x)\) by the factor \(1/\lambda_{\mathbb R}\), and that the curve \(u\) satisfies a third-order vector differential equation with time-dependent damping coefficients and a gradient-of-Moreau-envelope term evaluated at \(u(t)+\frac{t}{4}u'(t)\).

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, and the supplied Lean code explicitly says that there is no proof body. Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or lemma is invoked.

The mathematical content is entirely the right-hand side of the definition. The Lean command `def` simply names the predicate `IsTOGESVR` and packages the four conditions as a proposition. The symbol `∧` is logical conjunction, so the definition asserts the positivity condition, the two pointwise conditions over all \(x\in H\), and the differential-equation condition for all admissible \(t\). The universal quantifiers `∀ x : H` and `∀ t : ℝ` express the pointwise and time-dependent requirements. The arrows in `t0 ≤ t → t ≠ 0 → ...` are implications: the displayed differential equation is required only when \(t_0\le t\) and \(t\neq 0\). The final equality is an equality in the Hilbert space \(H\), and the notation `•` denotes scalar multiplication of vectors in \(H\) by real numbers. The divisions by \(t\), \(t^2\), and \(\lambda_{\mathbb R}\) are ordinary real divisions; the assumptions \(t\neq 0\) and \(0<\lambda_{\mathbb R}\) are precisely what make the intended expressions nondegenerate in the usual mathematical reading. The uses of `gradient` produce vectors in \(H\), while `.toReal` converts the Moreau-envelope values from extended reals to real numbers before the gradient is taken. No further proof steps are present to analyze.

