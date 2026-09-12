## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_8.lean`

## Lean statement
```lean
noncomputable def distanceToSet {H : Type*} [PseudoMetricSpace H] (x : H) (C : Set H) : EReal :=
  sInf (Set.range fun v : C ↦ (dist x v : EReal))
```

## Statement explanation
The declaration defines the distance from a point to a set in a pseudometric space, with the result taken in the extended real numbers. The type $H$ is an arbitrary type carrying a `PseudoMetricSpace` structure, so there is a distance function $d$ on $H$ satisfying the pseudometric axioms. The argument $x : H$ is the point from which distance is measured, and $C : Set H$ is a subset of $H$. The codomain is `EReal`, the extended real line $\overline{\mathbb{R}}$, rather than the ordinary real line.

The body of the definition takes each element $v$ of the subtype $C$, coerces it to the underlying point of $H$, computes the ordinary pseudometric distance $d(x,v)$, and then coerces that real number into $\overline{\mathbb{R}}$. The term `Set.range` collects all these values, so it forms the set

```math
D_{x,C} = \{\, d(x,v) : v \in C \,\} \subseteq \overline{\mathbb{R}}.
```

Finally, `sInf` takes the infimum of this set in the order on $\overline{\mathbb{R}}$. Thus the declaration defines

```math
\mathrm{distanceToSet}(x,C)
= \inf \{\, d(x,v) : v \in C \,\},
```

where the infimum is understood in the extended-real order.

Because $H$ is only assumed to be a pseudometric space, two distinct points may have distance $0$. Consequently, the defined value can be $0$ even when $x \notin C$, exactly as with the usual distance-to-set function on a pseudometric space. If $C$ is nonempty, the displayed set consists of ordinary finite nonnegative distances embedded in $\overline{\mathbb{R}}$, and its infimum is the usual extended-real distance from $x$ to $C$. If $C$ is empty, the set of distances is empty, and the value is the infimum of the empty set in $\overline{\mathbb{R}}$, which under the usual `sInf` convention on `EReal` is $+\infty$. The definition is marked `noncomputable` because computing an infimum over an arbitrary subset of a pseudometric space is not an executable operation in general.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. This declaration is a definition, not a theorem, and the Lean source explicitly says that there is no proof part.

The definitional body constructs the distance-to-set value in three mathematical stages. First, $v$ ranges over the subtype $C$, meaning $v$ is an element of $C$ together with its inclusion into $H$. The expression `dist x v` evaluates the pseudometric distance $d(x,v)$ in the real numbers. Second, the coercion `(dist x v : EReal)` embeds that real distance into the extended real line $\overline{\mathbb{R}}$. Third, `Set.range` collects the images of all such $v$, producing the subset

```math
\{\, d(x,v) : v \in C \,\}
```

of $\overline{\mathbb{R}}$. Finally, `sInf` takes the greatest lower bound of that subset in the extended-real order.

There are no hypotheses to introduce, no equalities to rewrite, no simplification steps, and no applications of named lemmas. In particular, no use is made of tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no local result is cited. The declaration only introduces the noncomputable function `distanceToSet` by specifying its value as the extended-real infimum of the distances from $x$ to the points of $C$.

