## Source file
`Beck_Teboulle_FISTA_2009/items/def_4.lean`

## Lean statement
```lean
def subdifferential {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {γ | ∀ y, g x + ⟪γ, y - x⟫ ≤ g y}
```

## Statement explanation
The declaration defines the set `subdifferential` for a real-valued function on a finite-dimensional Euclidean space. The parameters are a natural number $n$, a function $g : \mathbb R^n \to \mathbb R$ (represented in Lean by `EuclideanSpace ℝ (Fin n) → ℝ`), and a point $x \in \mathbb R^n$. The definition returns a subset of $\mathbb R^n$, whose elements are the vectors $\gamma$ satisfying the following condition for every $y \in \mathbb R^n$:

$$
g(x) + \langle \gamma, y - x \rangle \le g(y).
$$

Thus, mathematically,

```math
\mathrm{subdifferential}(g,x)
=\left\{
\gamma \in \mathbb R^n
\;\middle|\;
\forall y \in \mathbb R^n,\;
g(x) + \langle \gamma, y - x \rangle \le g(y)
\right\}.
```

Here $\langle \cdot, \cdot \rangle$ is the real inner product on $\mathbb R^n$. The inequality says that the affine function

$$
y \mapsto g(x) + \langle \gamma, y - x \rangle
$$

lies below the graph of $g$ everywhere. The vector $\gamma$ is the slope of this affine lower bound, and $y-x$ is the displacement from the base point $x$. The definition imposes no convexity, differentiability, continuity, or nonemptiness assumptions; it simply characterizes the set of all vectors $\gamma$ satisfying that global inequality. The set may be empty for some choices of $g$ and $x$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, so its mathematical content is exactly the set-builder condition

```math
\gamma \in \mathrm{subdifferential}(g,x)
\iff
\forall y \in \mathbb R^n,\;
g(x) + \langle \gamma, y - x \rangle \le g(y).
```

No named lemma or theorem is invoked, and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear. The only definitional step is unfolding membership in `subdifferential`: to establish that a vector $\gamma$ belongs to the set, one must prove the displayed inequality for every $y \in \mathbb R^n$; conversely, if one has a proof of that inequality for all $y$, then it directly yields membership of $\gamma$ in the set.

