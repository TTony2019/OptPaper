## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/cor_2.lean`

## Lean statement
```lean
theorem hpe_distance_converges {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun k ↦ ‖A.x k - xStar‖) Filter.atTop (nhds L)
```

## Statement explanation
The declaration `hpe_distance_converges` is a theorem in a normed vector space \(H\) that is also an inner product space over \(\mathbb R\). It fixes a set-valued operator \(T : H \rightrightarrows H\) and an object \(A : \mathrm{HPEIterates}(H,T)\). The HPE iterate object supplies an iterate sequence \(A.x : \mathbb N \to H\), together with scalar sequences \(A.\alpha : \mathbb N \to \mathbb R\) and \(A.\delta : \mathbb N \to \mathbb R\). From the proof, the HPE structure guarantees the nonnegativity facts \(0 \le A.\alpha(k)\) and \(0 \le A.\delta(k)\) for every \(k\), as well as summability of the scalar sequences \(A.\alpha\) and \(A.\delta\). The theorem also fixes a point \(x^\star \in H\) and assumes \(0 \in T x^\star\), meaning that the zero vector belongs to the set \(T(x^\star)\), so \(x^\star\) is a zero of the set-valued operator \(T\).

The conclusion is that there exists a real number \(L\) with \(L \ge 0\) such that
\[
\|A.x(k)-x^\star\| \longrightarrow L
\]
as \(k \to \infty\), i.e. the sequence of distances from the iterates \(A.x(k)\) to the zero \(x^\star\) converges to some nonnegative limit. In ordinary language, the theorem says that for the HPE iteration associated with \(A\), the distance to a zero \(x^\star\) of \(T\) converges, without asserting what the limit is or how fast the convergence is.

## Lean proof
```lean
by
  refine polyak_scalar_convergence A.α A.δ (fun k ↦ ‖A.x k - xStar‖)
    A.α_nonneg A.δ_nonneg (fun k ↦ norm_nonneg _) A.summable_alpha A.summable_delta ?_
  intro k
  exact hpe_distance_bound A hxStar k
```

## Proof explanation
The proof applies the scalar convergence lemma `polyak_scalar_convergence`. That lemma states that if \(\alpha,\delta,\gamma : \mathbb N \to \mathbb R\) are nonnegative sequences, if the series \(\sum_k \alpha(k)\) and \(\sum_k \delta(k)\) are summable, and if for every \(k\)
\[
\gamma(k+1) \le \alpha(k) + \sqrt{\gamma(k)^2 + \delta(k)},
\]
then there exists \(L \ge 0\) such that \(\gamma(k) \to L\) as \(k \to \infty\). This is a Polyak-type scalar convergence result: a nonnegative scalar sequence satisfying a recursive bound with summable error terms must converge to a nonnegative limit.

The tactic invocation
\[
\texttt{refine polyak\_scalar\_convergence A.$\alpha$ A.$\delta$ (fun k $\mapsto$ $\|A.x k - xStar\|$) ...}
\]
instantiates that lemma with
\[
\alpha(k) = A.\alpha(k), \qquad
\delta(k) = A.\delta(k), \qquad
\gamma(k) = \|A.x(k)-x^\star\|.
\]
The hypotheses of the scalar lemma are then supplied as follows. The nonnegativity of \(A.\alpha\) is given by `A.α_nonneg`, the nonnegativity of \(A.\delta\) by `A.δ_nonneg`, and the nonnegativity of \(\gamma\) by `norm_nonneg _`, which says that for every \(k\), \(\|A.x(k)-x^\star\| \ge 0\). The summability of \(A.\alpha\) and \(A.\delta\) is supplied by `A.summable_alpha` and `A.summable_delta`. The only remaining hypothesis of `polyak_scalar_convergence` is the recursive inequality, which the proof leaves as a placeholder `?_`.

The goal after this `refine` is therefore
\[
\forall k,\quad
\|A.x(k+1)-x^\star\|
\le A.\alpha(k) + \sqrt{\|A.x(k)-x^\star\|^2 + A.\delta(k)}.
\]
The command `intro k` introduces an arbitrary natural number \(k\) and reduces the goal to the inequality for that fixed \(k\). The command `exact hpe_distance_bound A hxStar k` then closes the goal by applying the previously established distance bound `hpe_distance_bound`. Its concrete content in this setting is exactly the needed inequality:
\[
\|A.x(k+1)-x^\star\|
\le A.\alpha(k) + \sqrt{\|A.x(k)-x^\star\|^2 + A.\delta(k)}.
\]
The hypothesis `hxStar`, namely \(0 \in T x^\star\), is the zero-membership assumption required by `hpe_distance_bound`; the iterate object \(A\) and the index \(k\) are the other two inputs.

Thus the recursive bound required by `polyak_scalar_convergence` is proved for every \(k\). Applying the scalar convergence lemma yields the existence of \(L \ge 0\) such that
\[
\|A.x(k)-x^\star\| \longrightarrow L.
\]
This is precisely the conclusion of `hpe_distance_converges`. No `rw`, `simp`, or `linarith` steps are used; the proof consists of `refine`, `intro`, and `exact`, together with the concrete applications of `polyak_scalar_convergence` and `hpe_distance_bound`.

