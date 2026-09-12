## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_4.lean`

## Lean statement
```lean
theorem mem_argminSet_iff {m : Nat} (G : EuclideanSpace m -> EReal)
    (p : EuclideanSpace m) :
    p ∈ argminSet G ↔ G p = sInf (Set.range G)
```

## Statement explanation
The declaration `mem_argminSet_iff` fixes an implicit natural number \(m\), an extended-real-valued function
\[
G:\text{EuclideanSpace }m\to \text{EReal},
\]
and a point
\[
p:\text{EuclideanSpace }m.
\]
There are no additional hypotheses beyond these data. The expression `Set.range G` is the image of \(G\), namely
\[
\{G(x):x\in \text{EuclideanSpace }m\},
\]
and `sInf (Set.range G)` is the infimum of that set of extended real values, computed in the complete order on `EReal`. Thus \(\operatorname{sInf}(\operatorname{range} G)\) is the greatest lower bound of all values taken by \(G\) on its whole domain. The set `argminSet G` is the global argmin set, i.e. the set of points at which \(G\) attains its global minimum value.

The theorem states
\[
p\in \operatorname{argminSet} G
\quad\Longleftrightarrow\quad
G(p)=\operatorname{sInf}(\operatorname{range} G).
\]
In ordinary mathematical language: a point \(p\) belongs to the set of global minimizers of \(G\) exactly when its value \(G(p)\) is the infimum of all values of \(G\). Since the codomain is `EReal`, the infimum may be \(-\infty\), and the criterion still has the same meaning in the extended-real order.

## Lean proof
```lean
Iff.rfl
```

## Proof explanation
The proof is the single term `Iff.rfl`. In Lean, `Iff.rfl` is the reflexivity principle for logical equivalence: for any proposition \(A\), it gives a proof of
\[
A\leftrightarrow A.
\]
For `Iff.rfl` to prove the stated biconditional, Lean must regard the left-hand proposition
\[
p\in \operatorname{argminSet} G
\]
and the right-hand proposition
\[
G(p)=\operatorname{sInf}(\operatorname{range} G)
\]
as definitionally the same proposition. This is exactly what the definition of `argminSet` provides: membership \(p\in \operatorname{argminSet} G\) unfolds to the condition that \(G(p)\) equals the infimum of the range of \(G\). Therefore the two sides of the biconditional are not merely logically equivalent by some external argument; they are the same condition after unfolding the definition.

Consequently, the forward direction says that if \(p\) is a global minimizer, then by definition its value is the infimum of all values of \(G\). The reverse direction says that if \(G(p)\) is that infimum, then by definition \(p\) belongs to the global argmin set. The proof uses no named theorem, no arithmetic reasoning, and no tactics such as `intro`, `rw`, `simp`, or `linarith`; its entire mathematical content is the definitional characterization of the global argmin set.

