## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_def_1.lean`

## Lean statement
```lean
noncomputable def T_n_g {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (μ ν_n : ℝ) (x : H) : H :=
  resolventOperator g (1 / (μ + ν_n)) x
```

## Statement explanation
The declaration is a noncomputable definition named `T_n_g`. It takes an implicit type parameter \(H\) together with the assumptions that \(H\) is a normed additive commutative group and a real inner product space. Thus \(H\) carries a norm and an inner product over \(\mathbb R\), but no completeness assumption is made. The explicit data are a real-valued function \(g:H\to\mathbb R\), real numbers \(\mu\) and \(\nu_n\), and a point \(x:H\). The output lies again in \(H\). Writing \(T_n^g\) for the Lean function `T_n_g`, the definition says
\[
T_n^g(g,\mu,\nu_n,x)
=
\operatorname{resolventOperator}\!\left(g,\frac{1}{\mu+\nu_n},x\right).
\]
Mathematically, once \(g\), \(\mu\), and \(\nu_n\) are fixed, this defines a mapping \(T_n^g:H\to H\) sending each \(x\) to the resolvent operator of \(g\) at the scalar step \(1/(\mu+\nu_n)\). In convex-analytic language, this is the proximal/resolvent step associated with the function \(g\) and that step size. The parameter \(\nu_n\) enters only through the reciprocal \(1/(\mu+\nu_n)\). The declaration itself imposes no convexity assumption on \(g\), no positivity assumption on \(\mu+\nu_n\), and no condition that \(\mu+\nu_n\neq 0\). The `noncomputable` marker indicates that the definition may rely on noncomputable choice inside `resolventOperator`; it adds no mathematical hypothesis.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
The declaration is a `def`, so there is no separate proof part. Its content is purely definitional: for every allowed \(H\), every \(g:H\to\mathbb R\), every \(\mu,\nu_n:\mathbb R\), and every \(x:H\), the value of \(T_n^g\) is by definition the resolvent operator applied to \(g\), the real number \(1/(\mu+\nu_n)\), and the point \(x\). There are no hypotheses to introduce, no goals to prove, and therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`. No named theorem or local lemma is invoked, because there is no proof script. If a later argument unfolds `T_n_g`, it replaces that expression with the corresponding call to `resolventOperator` with parameter \(1/(\mu+\nu_n)\). The exact internal definition of `resolventOperator` is not part of the supplied source, so the only assertion made here is the displayed definitional equality; the declaration does not claim a more specific formula for that imported operator.

