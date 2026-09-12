## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/ext_def_1.lean`

## Lean statement
```lean
noncomputable def distanceToSet (y : H) (C : Set H) : EReal :=
  sInf ((fun c : H => (‖y - c‖ : EReal)) '' C)
```

## Statement explanation
`distanceToSet` is a noncomputable definition. It has an ambient type $H$, whose subtraction and norm operations are used in the expression, and it has two explicit arguments: a point $y : H$ and a set $`C : \mathrm{Set}\,H`$. It returns a value of type `EReal`, the extended real numbers. The defining equation is

```math
\mathrm{distanceToSet}(y,C)
=\inf \left\{\|y-c\| : c \in C\right\},
```

where each real norm $`\|y-c\|`$ is coerced into `EReal`. In Lean, the set whose infimum is taken is the image of $C$ under the function

```math
c \mapsto (\|y-c\| : \mathrm{EReal}),
```

and `sInf` is the infimum, or greatest lower bound, in the order on `EReal`. Thus the declaration defines the distance from the point $y$ to the set $C$, valued in extended reals. If $C$ is nonempty, this is the infimum of a nonempty set of finite nonnegative real distances, so it is a finite nonnegative extended real; if $C$ is empty, the infimum is taken over the empty set and therefore gives the empty-infimum value, conventionally $+\infty$ in the complete-lattice order on extended reals. The value need not be attained by any point of $C$. The definition is marked `noncomputable` because it uses an arbitrary infimum over a set.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, so its right-hand side is the whole mathematical content and no hypotheses need to be discharged. No named theorem or lemma is invoked, and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur. The only construction is: take the image of $C$ under the map $`c \mapsto \|y-c\|`$, interpreted in the extended-real type `EReal`, and then apply `sInf` to that image. Mathematically, this is exactly the extended-real infimum

```math
\inf_{c \in C} \|y-c\|,
```

with the usual empty-set convention when $C = \varnothing$.

