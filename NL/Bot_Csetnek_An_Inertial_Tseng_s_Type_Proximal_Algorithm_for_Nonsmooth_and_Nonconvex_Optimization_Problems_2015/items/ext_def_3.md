## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_3.lean`

## Lean statement
```lean
def CoerciveEReal {m : Nat} (g : EuclideanSpace m -> EReal) : Prop :=
  ∀ c : Real, Bornology.IsBounded (ERealFunction.lowerLevelSet g c)
```

## Statement explanation
The declaration defines a predicate named `CoerciveEReal`. It has an implicit natural-number parameter $m$. Its explicit argument is a function

$$
g : \mathrm{EuclideanSpace}(m) \to \mathrm{EReal},
$$

so $g$ maps points of the $m$-dimensional Euclidean space to extended real values, i.e. to values in $`\mathbb R \cup \{-\infty,+\infty\}`$. The predicate

$$
\mathrm{CoerciveEReal}(g)
$$

is the proposition that for every real number $c$,

$$
\mathrm{Bornology.IsBounded}\bigl(\mathrm{ERealFunction.lowerLevelSet}(g,c)\bigr)
$$

holds.

The expression `ERealFunction.lowerLevelSet g c` denotes the lower level set, or sublevel set, of $g$ at level $c$, namely

```math
\{x : g(x) \le c\}.
```

Here $c$ is a real number coerced into $\mathrm{EReal}$, while $g(x)$ may be finite or infinite. The assertion `Bornology.IsBounded` applied to this set means that the set is bounded in the bornology of the Euclidean space. In this Euclidean setting this is the usual boundedness of a subset, equivalently that the set is contained in some ball, or has finite diameter.

Thus, mathematically, `CoerciveEReal g` says that every sublevel set of $g$ at a finite real height is a bounded subset of $\mathrm{EuclideanSpace}(m)$. In optimization terminology, this is the condition that $g$ has bounded lower level sets, a standard form of coercivity or level-coercivity. The definition imposes no additional assumptions such as convexity, lower semicontinuity, properness, or nonemptiness of the level sets. It only asserts boundedness for all real levels $c$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so its content is exactly the defining proposition described above. Consequently, there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to analyze, and no named theorem or lemma is invoked.

The intended mathematical reading of the definition is as follows. To prove `CoerciveEReal g`, one must show, for an arbitrary real level $c$, that the set

```math
\{x : g(x) \le c\}
```

is bounded. In a Lean proof this would correspond to introducing an arbitrary $c$ and then proving the boundedness of the corresponding lower level set. Conversely, if one has a hypothesis $h : \mathrm{CoerciveEReal}(g)$, then applying $h$ to any real $c$ yields the boundedness of the lower level set at that level $c$. The declaration itself does not contain such a proof; it only introduces the predicate that captures precisely this quantified boundedness condition.

