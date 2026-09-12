## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_def_2.lean`

## Lean statement
```lean
def argmin {H : Type*} {R : Type*} [ConditionallyCompleteLattice R] (F : H → R)
    (_hBoundedBelow : BddBelow (Set.range F)) : Set H :=
  {x | F x = sInf (Set.range F)}
```

## Statement explanation
The declaration introduces the Lean definition `argmin`. Its parameters are a type $H$, a type $R$ carrying a conditionally complete lattice structure, a function $F : H \to R$, and a proof $h$ that the range of $F$ is bounded below. The conditionally complete lattice structure supplies an order and an infimum operation $\operatorname{sInf}$; mathematically, a conditionally complete lattice is a lattice in which bounded-above subsets have least upper bounds and bounded-below subsets have greatest lower bounds. The hypothesis on $h$ says that the set of values of $F$ has a lower bound in $R$:

$$
\operatorname{range} F = \{\, F(x) \mid x \in H \,\},
\qquad
\operatorname{BddBelow}(\operatorname{range} F)
\ \text{means}\
\exists b : R,\ \forall y \in \operatorname{range} F,\ b \le y.
$$

The definition returns the subset of $H$ consisting exactly of those $x$ for which $F(x)$ is equal to the infimum of the range of $F$:

$$
\operatorname{argmin}(F,h)
=
\{\, x : H \mid F(x) = \operatorname{sInf}(\operatorname{range} F) \,\}.
$$

Thus it is the set of points at which $F$ attains the infimum of all its values. It is a set rather than a choice of one point, so it may contain no points, one point, or many points. The hypothesis $h$ records that the set of values is bounded below, so that its infimum is the intended greatest lower bound in the usual mathematical sense. The definition itself does not assert that this infimum is attained, nor does it assert that a minimum exists.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, not a theorem, so its content is the right-hand side term rather than a proof obligation. The body is the set-builder term

$$
\{\, x : H \mid F(x) = \operatorname{sInf}(\operatorname{range} F) \,\}.
$$

This means that an element $x$ belongs to $\operatorname{argmin}(F,h)$ exactly when the equality $F(x) = \operatorname{sInf}(\operatorname{range} F)$ holds. The variable $x$ ranges over $H$, and the equality is an equality in $R$.

The argument named `_hBoundedBelow` is unused in the definition body, as indicated by the underscore prefix. It remains an explicit parameter of `argmin`, so a proof of boundedness below must be supplied to form the term $\operatorname{argmin}(F,h)$, but the resulting set does not inspect that proof. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, because there is no proof script. No named theorem or lemma is invoked either. The definition simply introduces the set of all minimizers: if the infimum is attained, the set consists of exactly the attaining points; if the infimum is not attained, the set is empty.

