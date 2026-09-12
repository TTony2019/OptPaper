## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_6.lean`

## Lean statement
```lean
def IsSemiAlgebraicEReal {m : Nat} (g : EuclideanSpace m -> EReal) : Prop :=
  ∃ pieces : Finset (Set (EuclideanSpace m × Real)),
    (∀ s, s ∈ pieces -> BasicSemialgebraicSet s) ∧
      ERealFunction.epigraph g = {p | ∃ s, s ∈ pieces ∧ p ∈ s}
```

## Statement explanation
The declaration defines a predicate named `IsSemiAlgebraicEReal`. It has an implicit parameter \(m \in \mathbb N\), representing the dimension of the Euclidean space, and an explicit argument

\[
g : \mathbb R^m \to \overline{\mathbb R},
\]

where \(\overline{\mathbb R}\) is the type of extended real numbers. The predicate says that \(g\) is semi-algebraic in the extended-real-valued sense.

More precisely, `IsSemiAlgebraicEReal g` is the proposition that there exists a finite family \(P\) of subsets of \(\mathbb R^m \times \mathbb R\) such that:

1. Every member \(s\in P\) satisfies `BasicSemialgebraicSet s`; that is, each piece \(s\) is a basic semialgebraic subset of \(\mathbb R^m \times \mathbb R\).
2. The epigraph of \(g\), denoted `ERealFunction.epigraph g`, is exactly the union of the pieces:
\[
\operatorname{epigraph}(g)
=
\{p \mid \exists s,\; s\in P \land p\in s\}.
\]

The right-hand side is the union

\[
\bigcup_{s\in P} s.
\]

Thus the definition expresses that the epigraph of \(g\) can be written as a finite union of basic semialgebraic sets. There are no additional hypotheses on \(g\): the proposition is purely existential, requiring only the existence of such a finite semialgebraic decomposition of the epigraph. Since finite unions of basic semialgebraic sets are semialgebraic sets, this is a way of encoding semi-algebraicity of an extended-real-valued function through its epigraph.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, so the expression after the colon and equality sign is the defining proposition itself, not a theorem to be proved. Consequently, no proof tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named lemmas or prior results are invoked. The only logical structure is an existential quantifier over the finite family of pieces, followed by a conjunction: the first conjunct requires every chosen piece to be basic semialgebraic, and the second conjunct requires the epigraph of \(g\) to equal the union of those pieces. No local cited result is used because there is no proof step to justify.

