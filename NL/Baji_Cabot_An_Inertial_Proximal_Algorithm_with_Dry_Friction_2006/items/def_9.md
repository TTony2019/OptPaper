## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_9.lean`

## Lean statement
```lean
def IsC11 (f : H → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ LocallyLipschitz (gradient f)
```

## Statement explanation
The declaration introduces a predicate named `IsC11` on real-valued functions \(f : H \to \mathbb{R}\). Here \(H\) is the domain type supplied by the surrounding Lean context; it must carry whatever normed or inner-product structure is needed for `ContDiff` and `gradient` to be meaningful. The variable \(f\) is a function from \(H\) to \(\mathbb{R}\), so it is a scalar-valued function. There are no explicit hypotheses beyond the ambient typeclass assumptions: the declaration simply assigns to each such \(f\) the proposition

\[
\texttt{IsC11}(f) \;:=\; \texttt{ContDiff}\ \mathbb{R}\ 1\ f \;\wedge\; \texttt{LocallyLipschitz}(\texttt{gradient}\ f).
\]

The first conjunct, `ContDiff ℝ 1 f`, says that \(f\) is continuously differentiable of order \(1\) over the real scalars. In ordinary language, \(f\) is \(C^1\): it is differentiable, and its derivative depends continuously on the point. Since \(f\) is real-valued, its derivative at a point is a continuous linear functional from \(H\) to \(\mathbb{R}\).

The second conjunct, `LocallyLipschitz (gradient f)`, concerns the gradient map \(x \mapsto \nabla f(x)\). It says that this gradient map is locally Lipschitz. Concretely, in the metric structure available on \(H\), for every point \(x_0 \in H\) there is a neighborhood \(U\) of \(x_0\) and a finite constant \(L\) such that for all \(x,y \in U\),

\[
\lVert \nabla f(x) - \nabla f(y) \rVert \le L \lVert x - y \rVert.
\]

Thus `IsC11 f` expresses the local \(C^{1,1}\) condition: \(f\) is \(C^1\), and its gradient is locally Lipschitz. It is a local version of the condition that the gradient be Lipschitz continuous.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so the text after `:=` is the definition body, not a proof of a theorem. Therefore there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no cited local results to explain.

The entire mathematical content is the definitional unfolding: for any \(f : H \to \mathbb{R}\), the proposition `IsC11 f` is by definition the conjunction

\[
\texttt{ContDiff}\ \mathbb{R}\ 1\ f \;\wedge\; \texttt{LocallyLipschitz}(\texttt{gradient}\ f).
\]

So to establish `IsC11 f`, one would need to provide both conjuncts: a proof that \(f\) is \(C^1\), and a proof that its gradient is locally Lipschitz. Conversely, from a hypothesis `h : IsC11 f`, one may extract the two components, namely the \(C^1\) property and the local Lipschitz property of the gradient. No further mathematical argument is contained in the declaration itself.

