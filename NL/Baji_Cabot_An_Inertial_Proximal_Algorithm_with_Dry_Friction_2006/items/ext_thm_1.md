## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_thm_1.lean`

## Lean statement
```lean
theorem sum_maximal_monotone (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (hB : IsMaximalMonotone B) (hdom : (interior A.dom ∩ B.dom).Nonempty) :
    IsMaximalMonotone (A + B)
```

## Statement explanation
Let $H$ be the ambient real inner product space on which the set-valued operators act. A set-valued operator $A : H \rightrightarrows H$ assigns to each point $x \in H$ a subset $A(x) \subseteq H$, and its domain is

$$
\mathrm{dom} A = \{x \in H : A(x) \neq \varnothing\}.
$$

The theorem `sum_maximal_monotone` takes two set-valued operators $A$ and $B$ on $H$, together with three hypotheses:

- `hA : IsMaximalMonotone A`, meaning that $A$ is a maximal monotone set-valued operator.
- `hB : IsMaximalMonotone B`, meaning that $B$ is a maximal monotone set-valued operator.
- `hdom : (interior A.dom ∩ B.dom).Nonempty`, meaning that there exists a point lying simultaneously in the topological interior of $\mathrm{dom} A$ and in $\mathrm{dom} B$:

  $$
  \exists x,\quad x \in \mathrm{int}(\mathrm{dom} A) \cap \mathrm{dom} B.
  $$

The conclusion is

$$
\mathrm{IsMaximalMonotone}(A+B).
$$

Here $A+B$ is the sum of the two set-valued operators, formed pointwise. Thus the theorem says that if two maximal monotone set-valued operators satisfy the domain/interior condition that the interior of the first domain meets the second domain, then their sum is again maximal monotone. The cited equivalence `isMaximalMonotone_iff_maximal_isMonotone` identifies the operator-theoretic notion $\mathrm{IsMaximalMonotone}(A)$ with the order-theoretic maximality statement $\mathrm{Maximal}(\mathrm{IsMonotone})(A)$, i.e. maximality among monotone set-valued operators.

## Lean proof
```lean
by
  exact (isMaximalMonotone_iff_maximal_isMonotone (A + B)).2
    (Maximal.add_of_interior_dom_inter_dom_nonempty
      ((isMaximalMonotone_iff_maximal_isMonotone A).1 hA)
      ((isMaximalMonotone_iff_maximal_isMonotone B).1 hB) hdom)
```

## Proof explanation
The proof is a single term-style proof introduced by `by` and completed by `exact`. There are no uses of `intro`, `rw`, `simp`, or `linarith`; the whole proof is the construction of a proof term of the required type.

The target goal is

$$
\mathrm{IsMaximalMonotone}(A+B).
$$

The proof first applies the cited equivalence `isMaximalMonotone_iff_maximal_isMonotone` to the operator $A+B$. Specialized to $A+B$, that theorem gives

$$
\mathrm{IsMaximalMonotone}(A+B)
\longleftrightarrow
\mathrm{Maximal}(\mathrm{IsMonotone})(A+B).
$$

The term `(isMaximalMonotone_iff_maximal_isMonotone (A + B)).2` is the backward direction of this equivalence. Therefore, to prove the desired conclusion, it is enough to prove

$$
\mathrm{Maximal}(\mathrm{IsMonotone})(A+B),
$$

namely that $A+B$ is maximal among monotone set-valued operators.

To obtain that maximality statement, the proof invokes
`Maximal.add_of_interior_dom_inter_dom_nonempty`. The full statement of this result is not reproduced in the supplied context, but the exact consequence used in this proof is visible from the way it is called. It consumes three arguments:

- a proof that $A$ is maximal among monotone set-valued operators;
- a proof that $B$ is maximal among monotone set-valued operators;
- the hypothesis `hdom`, that

  $$
  \mathrm{int}(\mathrm{dom} A) \cap \mathrm{dom} B \neq \varnothing.
  $$

It returns a proof that $A+B$ is maximal among monotone set-valued operators:

$$
\mathrm{Maximal}(\mathrm{IsMonotone})(A+B).
$$

The first two arguments to this additivity result are produced by converting the maximal-monotone hypotheses `hA` and `hB` into maximality statements. For $A$, the proof uses

$$
\texttt{(isMaximalMonotone\_iff\_maximal\_isMonotone A).1 hA}.
$$

The direction `.1` of the equivalence for $A$ is

$$
\mathrm{IsMaximalMonotone}(A)
\longrightarrow
\mathrm{Maximal}(\mathrm{IsMonotone})(A),
$$

so applying it to `hA` gives $\mathrm{Maximal}(\mathrm{IsMonotone})(A)$. The analogous expression

$$
\texttt{(isMaximalMonotone\_iff\_maximal\_isMonotone B).1 hB}
$$

gives $\mathrm{Maximal}(\mathrm{IsMonotone})(B)$.

Thus the additivity result receives exactly the two maximality hypotheses it needs, together with the interior-domain-intersection hypothesis `hdom`, and produces

$$
\mathrm{Maximal}(\mathrm{IsMonotone})(A+B).
$$

Finally, the surrounding expression applies the backward direction `.2` of the equivalence for $A+B$ to this maximality proof, converting

$$
\mathrm{Maximal}(\mathrm{IsMonotone})(A+B)
$$

back into

$$
\mathrm{IsMaximalMonotone}(A+B).
$$

The `exact` command then checks that this entire proof term has precisely the declared goal type.

