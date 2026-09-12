## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/def_2.lean`

## Lean statement
```lean
structure HasPotentialAssumption {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → ℝ) where
  contDiff : ContDiff ℝ 1 Phi
  convex : ConvexOn ℝ Set.univ Phi
  bounded_below : ∃ m : ℝ, ∀ x : H, m ≤ Phi x
```

## Statement explanation
This declaration bundles the standing hypotheses on the potential function \(\Phi\) used later in the formalization.

The ambient space is a type \(H\) carrying two typeclass assumptions: `[NormedAddCommGroup H]` gives \(H\) the structure of a normed abelian group, and `[InnerProductSpace ℝ H]` gives it a real inner product together with the norm induced by that inner product. Together, \(H\) is a real inner product space (in particular a normed real vector space), so the expressions \(\Phi(x)\), \(\|\cdot\|\), and the ambient topology on \(H\) are all meaningful.

The argument \(\Phi : H \to ℝ\) is a real-valued function on \(H\), and the structure `HasPotentialAssumption Phi` asserts three things about it:

1. `contDiff : ContDiff ℝ 1 Phi`. The function \(\Phi\) is continuously differentiable of order \(1\) over \(ℝ\): it is Fréchet differentiable at every point of \(H\), and the derivative map \(x \mapsto D\Phi(x)\) is continuous as a map from \(H\) into the space of continuous linear functionals \(H \to_{L[ℝ]} ℝ\).

2. `convex : ConvexOn ℝ Set.univ Phi`. The function \(Φ\) is convex on the whole space, i.e. on \(Set.univ = H\). Concretely this is the inequality

\[
\Phi\bigl(t\,x + (1-t)\,y\bigr) \le t\,\Phi(x) + (1-t)\,\Phi(y)
\]

for all \(x, y \in H\) and all \(t \in [0,1]\).

3. `bounded_below : ∃ m : ℝ, ∀ x : H, m ≤ Phi x`. There is a real constant \(m\) that is a global lower bound for \(\Phi\), i.e. \(\Phi(x) \ge m\) for every \(x \in H\).

A single ordinary-language summary of the declaration: \(Φ\) is a \(C^{1}\) real-valued convex function on a real inner product space whose values are bounded below on the entire space. The name suggests that these are the hypotheses imposed on the potential entering the second-order dissipative minimization framework, but the declaration itself asserts only the three properties listed above; no additional relations between \(Φ\), \(H\), or any dynamics are part of the structure.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `structure` rather than a `theorem` or `lemma`, so the body following `where` is a list of fields, not a proof script. Each field is a proposition that must hold of \(Φ\):

- `ContDiff ℝ 1 Phi` is the proposition that \(Φ\) is \(C^{1}\),
- `ConvexOn ℝ Set.univ Phi` is the proposition that \(Φ\) is convex on all of \(H\),
- `∃ m : ℝ, ∀ x : H, m ≤ Phi x` is the proposition that \(Φ\) is bounded below by some real constant.

Consequently, an inhabitant of `HasPotentialAssumption Phi` is exactly a triple consisting of a proof of \(C^{1}\)-smoothness, a proof of convexity on \(H\), and a proof of the existence of a lower bound. The declaration itself proves none of these; it merely records them as the interface that downstream statements can assume. No tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` occurs in this source, and no previously established lemma or theorem is invoked, because the declaration contains no proof term and no reference to any named result.

