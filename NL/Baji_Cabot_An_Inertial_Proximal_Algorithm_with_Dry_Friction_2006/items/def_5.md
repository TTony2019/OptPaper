## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_5.lean`

## Lean statement
```lean
noncomputable def PhiA (A : SetValuedOperator H H) (x : H) : EReal :=
  sInf ((fun y : H => (inner ℝ y x : EReal)) '' A x)
```

## Statement explanation
The declaration `PhiA` is a noncomputable definition. In the ambient context, \(H\) is used as a type equipped with the real inner-product structure needed for `inner ℝ`; \(A\) is a set-valued operator from \(H\) to \(H\), so for each \(x\in H\), the value \(A(x)\) is a subset of \(H\). The second argument \(x\) is a point of \(H\). The return type is `EReal`, Lean's extended real line \(\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}\).

Mathematically, the definition is

\[
\Phi_A(x)
= \operatorname{sInf}\left(\left\{ \iota(\langle y,x\rangle_{\mathbb R}) : y\in A(x)\right\}\right),
\]

where \(\iota:\mathbb R\to \overline{\mathbb R}\) is the canonical embedding of the real numbers into the extended reals, and the infimum is taken in the extended-real order. Equivalently,

\[
\Phi_A(x)
= \inf_{y\in A(x)} \langle y,x\rangle_{\mathbb R}.
\]

Thus \(\Phi_A(x)\) is the greatest extended-real lower bound of all real inner products \(\langle y,x\rangle_{\mathbb R}\) with \(y\) ranging over the set \(A(x)\). The inner product is written with \(y\) first and \(x\) second. There is no explicit nonemptiness hypothesis on \(A(x)\); if \(A(x)\) is empty, the definition takes the `sInf` of the empty image in `EReal`.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. Since the declaration is a `def`, it has no proof body and no proof obligations; no named theorem, lemma, or local result is cited or used. Consequently there are no occurrences of tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`.

Reading the body from the inside out: the expression `(fun y : H => (inner ℝ y x : EReal))` defines a function \(f_x:H\to \overline{\mathbb R}\) by

\[
f_x(y)=\iota(\langle y,x\rangle_{\mathbb R}),
\]

where \(\iota\) is the coercion from \(\mathbb R\) to `EReal`. The image operator `''` forms the image of the set \(A(x)\) under \(f_x\), namely

\[
\{f_x(y): y\in A(x)\}\subseteq \overline{\mathbb R}.
\]

Finally, `sInf` takes the infimum of this subset of `EReal`, yielding its greatest lower bound in the extended-real order. The `noncomputable` marker only indicates that this `sInf` is not evaluated computationally; it adds no mathematical hypothesis and does not change the formula.

