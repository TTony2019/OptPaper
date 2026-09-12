## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/def_2.lean`

## Lean statement
```lean
def IsStronglyConvex {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ x y : H, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y -
      (δ / 2) * t * (1 - t) * ‖x - y‖ ^ 2
```

## Statement explanation
The declaration introduces the predicate `IsStronglyConvex`. It takes a real normed vector space \(H\) (encoded by the typeclass assumptions that \(H\) is a normed additive commutative group and a normed vector space over \(\mathbb{R}\)), a function \(f : H \to \mathbb{R}\), and a real number \(\delta\). It then defines the proposition
\[
\mathrm{IsStronglyConvex}(f,\delta)
\]
to mean
\[
0<\delta
\]
and, for every \(x,y\in H\) and every real \(t\) with \(0\le t\le 1\),
\[
f\bigl(tx+(1-t)y\bigr)
\le
t f(x)+(1-t)f(y)
-\frac{\delta}{2}\,t(1-t)\,\lVert x-y\rVert^2 .
\]
Here \(tx+(1-t)y\) is the convex combination of \(x\) and \(y\) with weight \(t\), and the right-hand side is the usual chord interpolation \(t f(x)+(1-t)f(y)\) minus the quadratic penalty term
\[
\frac{\delta}{2}\,t(1-t)\,\lVert x-y\rVert^2 .
\]
Thus the definition expresses that \(f\) is strongly convex with modulus \(\delta\): first, \(\delta\) is strictly positive, and second, the value of \(f\) at any convex combination is bounded above by the linear interpolation of the endpoint values minus a nonnegative multiple of the squared distance between the endpoints.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, not a theorem, so the Lean source contains no proof tactics and no invocation of named lemmas, theorems, or previously established facts. In particular, there are no steps involving `intro`, `rw`, `simp`, `exact`, or `linarith`.

The mathematical content is entirely the defining proposition. Unfolding `IsStronglyConvex f δ` gives exactly the conjunction of two assertions:

1. the strict positivity condition \(0<\delta\); and
2. the universal inequality which, for arbitrary \(x,y\in H\) and arbitrary \(t\in\mathbb{R}\), takes the hypotheses \(0\le t\) and \(t\le 1\) and concludes
\[
f\bigl(tx+(1-t)y\bigr)
\le
t f(x)+(1-t)f(y)
-\frac{\delta}{2}\,t(1-t)\,\lVert x-y\rVert^2 .
\]

Accordingly, to establish `IsStronglyConvex f δ` one would need to provide precisely these two components: a proof of \(0<\delta\), and a proof of the displayed inequality for all \(x,y,t\) satisfying \(0\le t\le 1\). Conversely, from a hypothesis `h : IsStronglyConvex f δ`, one may extract the positivity \(h.1 : 0<\delta\) and apply \(h.2\) to chosen \(x,y,t\) and the two interval bounds to obtain the corresponding inequality. These are the definitional introduction and elimination principles for the predicate, not separate mathematical lemmas.

