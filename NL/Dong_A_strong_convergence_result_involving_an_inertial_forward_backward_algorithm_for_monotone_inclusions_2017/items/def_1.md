## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/def_1.lean`

## Lean statement
```lean
recall isNonexpansiveOn_restrict_iff_lipschitzOnWith_one
```

## Statement explanation
The declaration is a `recall` command for the theorem named `isNonexpansiveOn_restrict_iff_lipschitzOnWith_one`. It does not itself introduce new local hypotheses; it refers to an already available theorem. The mathematical content of that theorem is as follows.

Let $\alpha$ and $\beta$ be pseudo-extended metric spaces, let $s \subseteq \alpha$ be a set, and let $f : \alpha \to \beta$ be a function. Write $f|_s : s \to \beta$ for the restriction of $f$ to the subtype $s$, so $(f|_s)(x) = f(x)$ for $x \in s$. The theorem states

$$
\mathrm{IsNonexpansiveOn}(f|_s, \mathrm{univ})
\longleftrightarrow
\mathrm{LipschitzOnWith}(1, f, s).
$$

The left-hand side says that the restricted map $f|_s$ is nonexpansive on its entire domain $s$: for all $x,y \in s$,

$$
\mathrm{edist}(f(x), f(y)) \le \mathrm{edist}(x,y).
$$

The right-hand side says that $f$ is Lipschitz on the set $s$ with constant $1$: for all $x,y \in s$,

$$
\mathrm{edist}(f(x), f(y)) \le 1 \cdot \mathrm{edist}(x,y)
= \mathrm{edist}(x,y).
$$

Thus the two sides express exactly the same pointwise inequality. The left side phrases it for the subtype $s$, while the right side phrases it for the ambient set $s$. In the ordinary metric-space case, $\mathrm{edist}$ is the usual distance $\mathrm{dist}$. The theorem has no additional side conditions beyond the ambient pseudo-extended metric structure.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The Lean source contains only the `recall` command and the comment that there is no proof part. A `recall` declaration is not a proof of a new theorem; it refers to a previously established result. Therefore there are no proof steps, no tactic invocations such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no intermediate goals to explain.

The mathematical content is exactly the equivalence described above: restricting $f$ to $s$ and asking that the resulting map be nonexpansive on all of $s$ is equivalent to asking that $f$ be $1$-Lipschitz on $s$.

