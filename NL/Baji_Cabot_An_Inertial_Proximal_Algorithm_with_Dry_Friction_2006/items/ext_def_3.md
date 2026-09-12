## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_def_3.lean`

## Lean statement
```lean
def normalConeSet (C S : Set H) : Set H := ⋃ ξ ∈ S, normalCone C ξ
```

## Statement explanation
The declaration introduces a set-valued operation `normalConeSet`. Its ambient type is \(H\), and it takes two subsets \(C\subseteq H\) and \(S\subseteq H\) as arguments. It returns a subset of \(H\), defined by

\[
\operatorname{normalConeSet}(C,S)
=
\bigcup_{\xi \in S} \operatorname{normalCone}(C,\xi).
\]

Here \(\operatorname{normalCone}(C,\xi)\) denotes the normal cone of the set \(C\) at the point \(\xi\), as supplied by the surrounding Mathlib context. The Lean notation \(\bigcup_{\xi \in S} \operatorname{normalCone}(C,\xi)\) is the union over all points \(\xi\) satisfying \(\xi \in S\). Therefore, an element \(x\in H\) belongs to \(\operatorname{normalConeSet}(C,S)\) exactly when there exists some \(\xi\in S\) such that

\[
x \in \operatorname{normalCone}(C,\xi).
\]

Mathematically, the definition collects together the normal cones to \(C\) at all points lying in the set \(S\). If \(S\) is empty, the union is empty. The definition itself imposes no requirement that \(S\subseteq C\), nor any convexity, closedness, or nonemptiness conditions on \(C\) or \(S\); any such conditions would belong to the imported definition of \(\operatorname{normalCone}\) or to later theorems. The new operation is simply a set-level construction from a family of normal cones indexed by points of \(S\).

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The Lean declaration is a `def`, so its body is a definitional expression rather than a theorem proof. Consequently, there are no hypotheses to introduce, no goals to rewrite or simplify, and no calls to tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`. No named lemma or theorem is invoked. The only mathematical content is the defining equality

\[
\operatorname{normalConeSet}(C,S)
=
\bigcup_{\xi \in S} \operatorname{normalCone}(C,\xi),
\]

which defines the new set by taking the union of the normal cones at all points \(\xi\) belonging to \(S\).

