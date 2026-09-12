## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_1.lean`

## Lean statement
```lean
recall Metric.infDist
```

## Statement explanation
The declaration `recall Metric.infDist` is not a theorem or lemma with hypotheses and a conclusion; it is a recall of an existing Mathlib definition. In the ambient (pseudo)metric space, for a point $x$ and a set $s$, the function `Metric.infDist` assigns the real number

$$
\mathrm{infDist}(x,s)=\inf\{\mathrm{dist}(x,y)\mid y\in s\}.
$$

More formally in Lean, it is the infimum of the image of $s$ under the map $y\mapsto \mathrm{dist}(x,y)$, i.e.

$$
\mathrm{infDist}(x,s)=\mathrm{sInf}\bigl((\mathrm{dist} x)''s\bigr).
$$

The parameters of the recalled definition are an ambient type equipped with a metric or pseudometric structure, a point $x:\alpha$, and a set $s\subseteq\alpha$. The value lies in $\mathbb R$. There are no logical hypotheses and no conclusion in this declaration, because `recall` merely brings the definition into scope. Mathematically, $\mathrm{infDist}(x,s)$ is the greatest lower bound of the distances from $x$ to points of $s$; it need not be attained. If $s$ is nonempty, this is the usual infimum of a nonempty set of nonnegative real numbers. If $s$ is empty, the value is determined by Lean’s convention for `sInf` on the empty subset of $\mathbb R$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The source explicitly has no proof part, so the declaration is only the recall of the definition `Metric.infDist`. Consequently there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named lemmas or previously established facts are invoked. The role of the declaration is definitional: it makes available the mathematical object $\mathrm{infDist}(x,s)$, the infimum of distances from a point $x$ to a set $s$, for later statements and proofs.

