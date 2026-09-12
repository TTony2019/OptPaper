## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_10.lean`

## Lean statement
```lean
def IsBoundedlyInfCompact {H : Type*} [NormedAddCommGroup H]
    (f : H → EReal) : Prop :=
  ∀ r R : ℝ, 0 < R → IsCompact (closure {v | f v ≤ (r : EReal) ∧ ‖v‖ ≤ R})
```

## Statement explanation
The declaration introduces a predicate `IsBoundedlyInfCompact`. It is not a theorem and has no hypotheses beyond the ambient structure on the type. The type variable `H` is assumed to carry the structure `NormedAddCommGroup`, so it has a norm $`\|\cdot\|`$ and the topology in which closure and compactness are interpreted. The function

$$
f : H \to \mathrm{EReal}
$$

takes values in the extended real numbers. For such an $f$, the proposition `IsBoundedlyInfCompact f` means:

```math
\forall r,R\in\mathbb R,\quad 0<R \implies
\mathrm{IsCompact}\!\left(
\mathrm{closure}\{v\in H : f(v)\le (r:\mathrm{EReal}) \ \text{and}\ \|v\|\le R\}
\right).
```

Here $r$ is an arbitrary real threshold for the values of $f$, and $R$ is a positive real radius. The coercion $(r:\mathrm{EReal})$ interprets the real number $r$ as an extended real, so that it can be compared with $f(v)$. The set

```math
\{v\in H : f(v)\le r \ \text{and}\ \|v\|\le R\}
```

is the intersection of the sublevel set of $f$ at level $r$ with the closed ball of radius $R$ centered at the origin. The definition requires the closure of this intersection to be compact. Since compactness of the closure means that the set itself is relatively compact, the predicate says that every sublevel set of $f$, after being localized to a bounded closed ball, has compact closure. The definition does not assume convexity, lower semicontinuity, properness, or any other property of $f$; those are not part of the statement.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, and the supplied proof section consists only of the comment `-- No separate proof part.` Therefore no theorem, lemma, or previously established local result is invoked, and there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain.

Mathematically, the entire content is the defining equation of the predicate. If one unfolds `IsBoundedlyInfCompact f`, one obtains exactly the universal proposition

```math
\forall r,R\in\mathbb R,\quad 0<R \implies
\mathrm{IsCompact}\!\left(
\mathrm{closure}\{v\in H : f(v)\le (r:\mathrm{EReal}) \ \text{and}\ \|v\|\le R\}
\right).
```

Thus, to prove `IsBoundedlyInfCompact f` in a later argument, one would introduce arbitrary real numbers $r$ and $R$, assume the hypothesis $0\lt R$, and then prove the compactness of the closure of the corresponding localized sublevel set. Conversely, to use an already established hypothesis `hf : IsBoundedlyInfCompact f`, one would apply it to chosen real numbers $r$ and $R$ and a proof of $0\lt R$, obtaining compactness of that closure. No such proof steps are present in this definition itself, and no named mathematical result is cited.

