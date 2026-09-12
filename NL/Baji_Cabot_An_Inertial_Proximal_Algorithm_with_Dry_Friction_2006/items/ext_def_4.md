## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_def_4.lean`

## Lean statement
```lean
noncomputable def supportFunction (C : Set H) (x : H) : EReal :=
  sSup ((fun z : H => (inner ℝ z x : EReal)) '' C)
```

## Statement explanation
The declaration introduces a noncomputable function named `supportFunction`. It takes two arguments: a set $C$ of points of a type $H$, and a point $x\in H$. The value returned lies in `EReal`, the extended real number type. The expression uses the real inner product $\langle z,x\rangle_{\mathbb R}$, where the variable $z$ ranges over $H$. For each such $z$, the inner product is coerced into the extended-real type $\mathrm{EReal}$. The image of $C$ under the map

$$
z \mapsto (\langle z,x\rangle_{\mathbb R})_{\mathrm{EReal}}
$$

is therefore

$$
\{(\langle z,x\rangle_{\mathbb R})_{\mathrm{EReal}} : z\in C\}.
$$

The definition then takes the supremum of this set in the order on $\mathrm{EReal}$. Thus

$$
\operatorname{supportFunction}(C,x)
=
\sup_{z\in C}\langle z,x\rangle_{\mathbb R},
$$

with the supremum interpreted in the extended real numbers. There are no hypotheses on $C$ or $x$ beyond the typing needed for the real inner product and the extended-real supremum; in particular, $C$ need not be convex, closed, bounded, or nonempty. This is a definition rather than a theorem, so its whole mathematical content is the displayed formula.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration kind is `def`, and the proof field only says that no separate proof is provided. Therefore there are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem or lemma is invoked. The body is a defining term. The modifier `noncomputable` marks that the definition uses `sSup`, a supremum operation that is not computably evaluable; it does not add any mathematical hypothesis.

Reading the defining term from the inside out: for fixed $x$, the subterm `fun z : H => ...` is the function

$$
z \mapsto (\langle z,x\rangle_{\mathbb R})_{\mathrm{EReal}}.
$$

The explicit cast to `EReal` is the embedding of the real inner-product value into the extended-real order. The image operator `''` applies this function to the set $C$, producing

$$
\{(\langle z,x\rangle_{\mathbb R})_{\mathrm{EReal}} : z\in C\}.
$$

Finally, `sSup` takes the least upper bound of that set in $\mathrm{EReal}$. Hence the definition returns the extended-real supremum of the values $\langle z,x\rangle_{\mathbb R}$ as $z$ ranges over $C$. Since no goal is being proved, there are no hypotheses to discharge and no conclusions derived beyond this defining equation.

