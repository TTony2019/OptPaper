## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_def_5.lean`

## Lean statement
```lean
def IsWeakLimitPoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℝ → H) (y : H) : Prop :=
  ∃ t : ℕ → ℝ, Tendsto t Filter.atTop Filter.atTop ∧
    Tendsto (fun k => toWeakSpace ℝ H (u (t k))) Filter.atTop
      (nhds (toWeakSpace ℝ H y))
```

## Statement explanation
The declaration defines a predicate named `IsWeakLimitPoint`. It takes a type $H$, a function $u : \mathbb{R} \to H$, and a point $y \in H$. The type $H$ is assumed to satisfy `NormedAddCommGroup` and `InnerProductSpace` over $\mathbb{R}$; thus $H$ is a real normed vector space equipped with an inner product. The statement does not assume completeness, finite-dimensionality, separability, or nontriviality. The function $u$ is an arbitrary curve in $H$ indexed by the real line, and $y$ is a candidate weak limit point.

Formally, the predicate is defined by

```math
\mathrm{IsWeakLimitPoint}(u,y) :=
\exists t:\mathbb{N}\to\mathbb{R},\;
\mathrm{Tendsto}\bigl(t,\mathrm{atTop},\mathrm{atTop}\bigr)
\wedge
\mathrm{Tendsto}\!\left(k\mapsto \mathrm{toWeakSpace}_{\mathbb{R} H}(u(t_k)),\mathrm{atTop},\mathrm{nhds}\!\left(\mathrm{toWeakSpace}_{\mathbb{R} H}(y)\right)\right).
```

The first `Tendsto` condition is between the filter `Filter.atTop` on the index type $\mathbb{N}$ and the filter `Filter.atTop` on $\mathbb{R}$. It says exactly that $t_k \to +\infty$ as $k\to\infty$: for every real $a$, all sufficiently large $k$ satisfy $t_k \ge a$. The second `Tendsto` condition is between `Filter.atTop` on $\mathbb{N}$ and the neighborhood filter `nhds` of the weak-space image of $y$. It says that the sequence of weak-space images $\mathrm{toWeakSpace}_{\mathbb{R} H}(u(t_k))$ converges, in the weak topology, to $\mathrm{toWeakSpace}_{\mathbb{R} H}(y)$. The map `toWeakSpace ℝ H` is the canonical passage from $H$ to the weak-topology version of $H$, so this is convergence in the weak topology rather than in the norm topology.

In ordinary language, $y$ is a weak limit point at infinity of the curve $u$: there exists an unbounded sequence of real times $t_k$ such that $u(t_k)$ converges weakly to $y$. The sequence $t$ need not be monotone or injective, and $y$ need not be a value attained by $u$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so the material after `:=` is the definition body, a term of type `Prop`; it is not a proof of a theorem and no proof obligations are discharged. Consequently there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no local named lemma or theorem is cited. The logical structure of the body is an existential quantifier over $t:\mathbb{N}\to\mathbb{R}$, followed by a conjunction of two `Tendsto` statements. To prove `IsWeakLimitPoint u y`, one would supply a sequence $t$, a proof that $t_k\to+\infty$, and a proof that $\mathrm{toWeakSpace}_{\mathbb{R} H}(u(t_k))$ tends to $\mathrm{toWeakSpace}_{\mathbb{R} H}(y)$ in the weak topology. To use a hypothesis `IsWeakLimitPoint u y`, one may extract exactly those witnesses. The mathematical content is therefore just the definition of a weak sequential limit point at infinity, as described in the first section.

