## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/def_2.lean`

## Lean statement
```lean
recall tendsto_iff_tendsto_weakly_and_tendsto_norm
```

## Statement explanation
The source contains a `recall` declaration, not a theorem with an explicitly displayed Lean type. The only mathematical information visible is the name `tendsto_iff_tendsto_weakly_and_tendsto_norm`. This name indicates an equivalence between ordinary convergence and the conjunction of weak convergence and convergence of norms. In the usual functional-analytic reading, for a sequence \((x_n)\) and a limit \(x\), the recalled statement is
\[
x_n \to x \text{ in norm}
\quad\Longleftrightarrow\quad
\bigl(x_n \rightharpoonup x \text{ weakly}\bigr)
\ \text{and}\
\bigl(\|x_n\| \to \|x\|\bigr).
\]
Here the left-hand side is strong convergence, meaning \(\|x_n-x\|\to 0\). The weak convergence condition means that for every continuous linear functional \(f\), one has \(f(x_n)\to f(x)\). The final condition is convergence of the scalar sequence of norms. The exact Lean type, the ambient space, the indexing filter, and any completeness or inner-product assumptions are not shown in the provided snippet; they would be supplied by the imported result that this `recall` makes available. No additional hypotheses or conclusions can be read off from the source itself.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration kind is `recall`, and the proof field is `-- No separate proof part.` Therefore there are no proof steps, no introductions of variables, no rewrites, no simplifications, and no applications of named lemmas. No tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` occurs. The `recall` declaration merely records or makes available the named equivalence between norm convergence and the combination of weak convergence with convergence of norms, to be used later when the appropriate hypotheses for that recalled result are supplied.

