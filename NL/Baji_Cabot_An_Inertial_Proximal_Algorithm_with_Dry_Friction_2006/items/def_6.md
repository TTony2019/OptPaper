## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_6.lean`

## Lean statement
```lean
def stationaryIndices (x : ℕ → H) : Set ℕ := {n | x (n+1) = x n}
```

## Statement explanation
The declaration defines `stationaryIndices` for a sequence $x:\mathbb N\to H$, where $H$ is the ambient type supplied by the surrounding Lean context. The explicit argument is the sequence $x$, and the result is a subset of $\mathbb N$:

$$
\operatorname{stationaryIndices}(x)
= \{\, n\in\mathbb N \mid x(n+1)=x(n) \,\}.
$$

Thus a natural number $n$ belongs to $\operatorname{stationaryIndices}(x)$ exactly when the $n$-th term of the sequence equals the next term. There are no hypotheses on $H$ or on $x$ in the declaration itself, and no existence of any stationary index is asserted: the set may be empty, finite, infinite, or all of $\mathbb N$. The definition only selects the indices at which the sequence is locally constant from one step to the next.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, not a theorem, so Lean does not need to establish a proposition. Its body is the set-builder term

$$
\{\, n \mid x(n+1)=x(n) \,\}.
$$

To type-check this body, Lean uses the fact that for any $n:\mathbb N$, both $x(n+1)$ and $x(n)$ are elements of the same type $H$. Therefore the equality $x(n+1)=x(n)$ is a well-formed proposition, and the set-builder expression has type $\mathrm{Set}\,\mathbb N$. The only mathematical content is the definitional unfolding of membership: for any $n$,

$$
n\in \operatorname{stationaryIndices}(x)
\quad\Longleftrightarrow\quad
x(n+1)=x(n).
$$

No tactics such as `intro`, `rw`, `simp`, or `linarith` occur, and no named theorem, lemma, or previously established result is invoked.

