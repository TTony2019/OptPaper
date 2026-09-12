## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_def_5.lean`

## Lean statement
```lean
def ext_def_5 {X : Type*} [PseudoMetricSpace X] (T : X → X) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y, dist (T x) (T y) ≤ c * dist x y
```

## Statement explanation
The declaration `ext_def_5` defines a property of a self-map of a pseudometric space. The type $X$ is equipped with a pseudometric structure, which provides a distance function $\mathrm{dist} : X \times X \to \mathbb{R}$ satisfying the pseudometric axioms; in particular, distinct points are not required to have positive distance. The explicit argument is a map $T : X \to X$, so $T$ sends points of $X$ to points of $X$.

The definition says exactly that there exists a real number $c$ such that

$$
0 \le c < 1
$$

and for every pair of points $x,y \in X$,

$$
\mathrm{dist}(T x, T y) \le c \cdot \mathrm{dist}(x,y).
$$

Thus $`\mathrm{ext\_def\_5}(T)`$means that$T$is a strict contraction: it is a Lipschitz map with some uniform constant$c$lying in the half-open interval$[0,1)$. The inequalities require$c$to be nonnegative and strictly less than$1$, and the quantified inequality requires the same contraction estimate to hold for all pairs$x,y$ in the whole space. Because the space is only a pseudometric space, the condition is a statement about distances, not about equality or injectivity of points.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source consists only of the definition and a comment stating that there is no proof. Therefore there are no proof steps to explain: no variables are introduced by `intro`, no rewriting is performed by `rw`, no simplification is performed by `simp`, no exact proof is supplied by `exact`, and no arithmetic reasoning such as `linarith` occurs. No named theorem or lemma is invoked.

The mathematical content is therefore exactly the right-hand side of the definition. To establish $`\mathrm{ext\_def\_5}(T)`$, one must exhibit a real number$c$, prove$0 \le c$, prove$c < 1$, and prove

$$
\mathrm{dist}(T x, T y) \le c \cdot \mathrm{dist}(x,y)
$$

for all $x,y \in X$. Conversely, assuming $`\mathrm{ext\_def\_5}(T)`$gives exactly such a$c$ together with those properties. Since the source contains no proof, there is nothing further to justify.

