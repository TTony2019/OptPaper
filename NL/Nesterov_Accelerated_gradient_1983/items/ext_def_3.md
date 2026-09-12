## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_def_3.lean`

## Lean statement
```lean
def argmaxOn {X V : Type*} [Preorder V] (g : X → V) (S : Set X) : Set X :=
  {x | x ∈ S ∧ ∀ z ∈ S, g z ≤ g x}
```

## Statement explanation
The declaration defines the set-valued operation `argmaxOn`. Its inputs are two arbitrary types $X$ and $V$, with $V$ equipped with a preorder $\le$, meaning that $\le$ is reflexive and transitive but not necessarily antisymmetric or total. It also takes a function $g:X\to V$ and a subset $S\subseteq X$. The result is a subset of $X$, namely

$$
\mathrm{argmaxOn}(g,S)
=
\{\, x \in X \mid x\in S \ \text{and}\ \forall z\in S,\ g(z)\le g(x) \,\}.
$$

Thus $x$ belongs to $\mathrm{argmaxOn}(g,S)$ exactly when $x$ lies in $S$ and the value $g(x)$ is an upper bound, under the preorder on $V$, for all values $g(z)$ with $z\in S$. Equivalently, $g(x)$ is a greatest element of the image $g(S)$, and $x$ is a point of $S$ realizing that greatest value. The definition does not assert that such an $x$ exists, nor that it is unique. If $S$ is empty, the condition is vacuous for every $x$ but the requirement $x\in S$ fails, so the set is empty. If $S$ is nonempty but $g(S)$ has no greatest element in this preorder, the set is also empty. If the preorder is not antisymmetric, there may be several distinct points $x$ whose values $g(x)$ are mutually $\le$-equivalent maxima.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. This is a definition, not a theorem, so the declaration consists only of the defining expression for the set $\mathrm{argmaxOn}(g,S)$. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or lemma is invoked.

The mathematical content is the defining equivalence

$$
x\in \mathrm{argmaxOn}(g,S)
\longleftrightarrow
\bigl(x\in S \ \text{and}\ \forall z\in S,\ g(z)\le g(x)\bigr).
$$

In Lean, the set-builder notation collects all elements $x$ satisfying that predicate. The condition $\forall z\in S,\ g(z)\le g(x)$ is shorthand for the statement that every $z\in S$ satisfies $g(z)\le g(x)$. The ambient `Preorder` instance on $V$ is what makes the expression $g(z)\le g(x)$ meaningful and gives $\le$ its reflexive and transitive behavior; the definition itself only uses the relation in the universal condition and does not add any further assumptions about existence, uniqueness, totality, or antisymmetry.

