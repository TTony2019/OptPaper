## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_prop_2.lean`

## Lean statement
```lean
theorem normalCone_stability_convexPolyhedron (C : Set H) (hC : ConvexPolyhedron C) (xbar : H)
    (hxbar : xbar ∈ C) : ∃ (V : Set H), V ∈ 𝓝 xbar ∧ ∀ x ∈ V, normalCone C x ⊆ normalCone C xbar
```

## Statement explanation
The declaration `normalCone_stability_convexPolyhedron` is a theorem about a set $C$ in an ambient type $H$, a point $\bar{x}\in H$, and the normal cones of $C$. The variable $C$ is a subset of $H$. The hypothesis `hC : ConvexPolyhedron C` says that $C$ is a convex polyhedron. The variable `xbar : H` is the base point, and the hypothesis `hxbar : xbar ∈ C` says that $\bar{x}$ lies in $C$. The conclusion is the existential statement that there is a set $V \subseteq H$ such that $V \in \mathcal{N}(\bar{x})$ — that is, $V$ belongs to the neighborhood filter of $\bar{x}$, so $V$ is a neighborhood of $\bar{x}$ — and for every $x \in V$, the normal cone of $C$ at $x$ is contained in the normal cone of $C$ at $\bar{x}$. Writing $N_C(x)$ for the normal cone denoted in Lean by `normalCone C x`, the second part is $N_C(x) \subseteq N_C(\bar{x})$ for all $x \in V$. Thus, near $\bar{x}$, every normal direction to $C$ at a nearby point is also a normal direction to $C$ at $\bar{x}$. The statement is one-sided: it asserts only containment, not equality of normal cones, and it does not assert that $V$ is open or contained in $C$. The quantifier $\forall x \in V$ ranges over all points of the ambient space $H$ that lie in $V$. Mathematically, this is a local stability property of normal cones of a convex polyhedron: at a point $\bar{x}$ of the polyhedron, a sufficiently small neighborhood has the property that normal cones of points in that neighborhood do not contain any direction outside the normal cone at $\bar{x}$.

## Lean proof
```lean
by
  sorry
```

## Proof explanation
The Lean proof consists only of `by sorry`. The keyword `by` opens tactic mode, and `sorry` is a placeholder that closes the goal without supplying a proof; it causes Lean to warn that the declaration uses `sorry`. Therefore no actual mathematical argument is present in this source. No witness $V$ is constructed, no proof that $V$ is a neighborhood of $\bar{x}$ is given, and no proof of $N_C(x) \subseteq N_C(\bar{x})$ for $x\in V$ is given. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear, and no named lemmas or imported results are invoked. Consequently there are no cited theorem statements to specialize or explain; the entire mathematical content is the statement above, which is admitted rather than proved.

