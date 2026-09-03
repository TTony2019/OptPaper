## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/thm_1.lean`

## Lean statement
```lean
theorem inertial_proximal_point_converges
    {A : SetValuedOperator H H} (hA : A.IsMaximalMonotone)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ)
    (hiteration : InertialProximalPointAlgorithm A x alpha lambda)
    (hzeros : A.zeros.Nonempty)
    (hlambda : ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ k : ℕ, lambda0 ≤ lambda k)
    (halpha : ∃ alpha0 : ℝ, 0 ≤ alpha0 ∧ alpha0 < 1 ∧
      ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0)
    (hsummable : Summable (fun k : ℕ => alpha (k + 1) * ‖x (k + 1) - x k‖ ^ 2)) :
    ∃ xhat : H, xhat ∈ A.zeros ∧
      Tendsto (fun k => toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xhat))
```

## Statement explanation
The ambient space \(H\) is the Hilbert space in which the statement is made; its typeclass assumptions are not shown in this theorem snippet. The theorem has an implicit operator parameter \(A : \mathsf{SetValuedOperator}\ H\ H\), i.e. a set-valued/multivalued operator from \(H\) to itself. The explicit hypotheses are:

- \(hA : A.\mathsf{IsMaximalMonotone}\): the operator \(A\) is maximal monotone.
- \(x : \mathbb{N} \to H\): a sequence \(x_0, x_1, x_2,\dots\) in \(H\).
- \(\alpha : \mathbb{N} \to \mathbb{R}\) and \(\mathsf{lambda} : \mathbb{N} \to \mathbb{R}\): real coefficient sequences used in the algorithm.  
- \(hiteration : \mathsf{InertialProximalPointAlgorithm}\ A\ x\ \alpha\ \mathsf{lambda}\): a formal hypothesis asserting that the sequence \(x\), together with the coefficient sequences \(\alpha\) and \(\mathsf{lambda}\), satisfies the inertial proximal point algorithm equation for the operator \(A\). The exact definition of this predicate is not unfolded in the statement.
- \(hzeros : A.\mathsf{zeros}.\mathsf{Nonempty}\): the zero set of \(A\), i.e. the set of \(z \in H\) with \(0 \in A(z)\), is nonempty.
- \(hlambda\): there exists a real \(\lambda_0\) with \(0 < \lambda_0\) and \(\lambda_0 \le \lambda_k\) for every \(k\); thus the step-size sequence is bounded below by a positive constant.
- \(halpha\): there exists a real \(\alpha_0\) with \(0 \le \alpha_0 < 1\), and for every \(k\), \(0 \le \alpha_k \le \alpha_0\). Hence all \(\alpha_k\) lie in \([0,\alpha_0]\subset[0,1)\).
- \(hsummable\): the series over \(k\) of
  \[
  \alpha_{k+1}\,\|x_{k+1}-x_k\|^2
  \]
  is summable; in Lean this is expressed as
  \(\mathsf{Summable}\ (\lambda k.\ \alpha(k+1)\cdot \|x(k+1)-x(k)\|^2)\).

The conclusion is:
\[
\exists \hat x \in H,\quad \hat x \in A.\mathsf{zeros}
\ \text{and}\quad
x_k \rightharpoonup \hat x
\]
as \(k\to\infty\). In Lean notation, weak convergence is written as
\[
\mathsf{Tendsto}\ (\lambda k.\ \mathsf{toWeakSpace}\ \mathbb{R}\ H\ (x\,k))\ \mathsf{atTop}\ (\mathcal{N}(\mathsf{toWeakSpace}\ \mathbb{R}\ H\ \hat x)).
\]
Here \(\mathsf{toWeakSpace}\ \mathbb{R}\ H\) is the map viewing the space \(H\) with its weak topology, so the conclusion says that the sequence \(x_k\) converges weakly to a zero \(\hat x\) of \(A\).

## Lean proof
```lean
by
  have halg : InertialProximalAlgorithm A x alpha lambda := by
    intro k hk
    exact hiteration.update k hk
  exact convergence_of_inertial_proximal_method hA x alpha lambda halg hzeros hlambda halpha
    hsummable
```

## Proof explanation
The proof is

