## Source file
`Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators/items/ext_def_2.lean`

## Lean statement
```lean
theorem mem_sum_iff (A B : SetValuedOperator H H) (x : H) (w : H) :
    w ∈ (A + B) x ↔ ∃ a ∈ A x, ∃ b ∈ B x, w = a + b
```

## Statement explanation
`mem_sum_iff` is a theorem about two set-valued operators \(A\) and \(B\) on an ambient type \(H\), an evaluation point \(x\in H\), and an element \(w\in H\). In this context, \(A\) and \(B\) are set-valued operators from \(H\) to \(H\), so \(A x\) and \(B x\) are subsets of \(H\). The operation \(A+B\) is the pointwise sum of set-valued operators, and \((A+B)x\) is the value of that sum at \(x\). The theorem has no additional hypotheses beyond the variables themselves; it states, for all such \(A,B,x,w\), the equivalence

\[
w \in (A+B)x \iff \exists a \in A x,\ \exists b \in B x,\ w = a+b.
\]

Mathematically, this says that an element \(w\) belongs to the value at \(x\) of the sum operator \(A+B\) exactly when \(w\) can be decomposed as \(a+b\), where \(a\) is chosen from the value \(A x\) of \(A\) at \(x\) and \(b\) is chosen from the value \(B x\) of \(B\) at \(x\). Equivalently, the value \((A+B)x\) is precisely the Minkowski sum of the two sets \(A x\) and \(B x\).

## Lean proof
```lean
by
  simpa [sum_apply, eq_comm] using Set.mem_add
```

## Proof explanation
The proof is a single simplification step. It does not use `intro`, `rw`, `exact`, or `linarith`; instead it uses `simpa` with `Set.mem_add` as the supplied proof term.

The cited theorem `sum_apply` says that for the given \(A\), \(B\), and \(x\),

\[
(A+B)x = A x + B x.
\]

That is, the value of the sum operator at \(x\) is the pointwise sum of the two sets \(A x\) and \(B x\). In the proof, this fact is used as a rewrite rule on the left-hand side of the goal, changing

\[
w \in (A+B)x
\]

into

\[
w \in A x + B x.
\]

The proof then uses the library lemma `Set.mem_add`. The full declaration of that lemma is not included in the supplied context, but the instance needed here is exactly the characterization of membership in a set-theoretic sum: for the sets \(A x\) and \(B x\),

\[
w \in A x + B x \iff \exists a \in A x,\ \exists b \in B x,\ w = a+b,
\]

up to the orientation of the equality. If the lemma naturally produces the equation \(a+b=w\), then `eq_comm`, the symmetry of equality, rewrites it to the orientation \(w=a+b\) required by the goal.

Thus `simpa` simplifies the goal using `sum_apply` and `eq_comm`, and then closes it by supplying `Set.mem_add` as the proof of the resulting statement. No case distinction or additional hypothesis is needed: the equivalence follows directly from the pointwise definition of the sum of set-valued operators and the membership rule for sums of sets.

