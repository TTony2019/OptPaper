## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_2.lean`

## Lean statement
```lean
noncomputable def IsGradientProjectionTrajectory {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (gradPsi : H → H) (lam μ : ℝ) (u y : ℕ → H) : Prop :=
  μ = lam / (1 + lam) ∧ ∀ k,
    u (k + 1) = projectionPoint C hC (lam • y k + (1 - lam) • u k) ∧
    y (k + 1) = (1 - μ) • y k + μ • (u (k + 1) - gradPsi (u (k + 1)))
```

## Statement explanation
The declaration introduces a predicate named `IsGradientProjectionTrajectory`. Its parameters are:

- \(H\): an arbitrary type equipped with the structures of a normed additive commutative group and a real inner product space. Thus \(H\) supports addition, subtraction, real scalar multiplication, and a norm.
- \(C\): a subset of \(H\), written \(C\subseteq H\).
- `hC`: a proof of the proposition `IsChebyshev C`. In the definition this proof is passed to the projection-point construction; it is otherwise not analyzed.
- `gradPsi`: a function \(g:H\to H\). The definition does not require \(g\) to be differentiable or to be the gradient of any function.
- `lam` and `mu`: real parameters, written below as \(\lambda\) and \(\mu\).
- \(u\) and \(y\): sequences \(\mathbb N\to H\), written \(u_k=u(k)\) and \(y_k=y(k)\).

For these data, \( \texttt{IsGradientProjectionTrajectory}\ C\ hC\ g\ \lambda\ \mu\ u\ y \) is the proposition stating two things. First,

\[
\mu=\frac{\lambda}{1+\lambda}.
\]

Second, for every \(k\in\mathbb N\),

\[
u_{k+1}=P_{C,hC}\bigl(\lambda y_k+(1-\lambda)u_k\bigr)
\]

and

\[
y_{k+1}=(1-\mu)y_k+\mu\bigl(u_{k+1}-g(u_{k+1})\bigr),
\]

where \(P_{C,hC}(z)\) denotes the projection point of \(z\) onto \(C\) associated to the Chebyshev hypothesis \(hC\). The first equation projects an affine combination of \(y_k\) and \(u_k\), with weights \(\lambda\) and \(1-\lambda\), onto \(C\). The second equation forms an affine combination of the current point \(y_k\) and the vector \(u_{k+1}-g(u_{k+1})\), with weights \(1-\mu\) and \(\mu\). The equality \(\mu=\lambda/(1+\lambda)\) couples the two real parameters. The definition does not assert the existence of such sequences; it is a condition saying that given sequences satisfy these recurrences.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, not a theorem, and the supplied proof part is empty. Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or lemma is invoked.

The only proof-relevant content is the logical structure of the definition itself: an outer conjunction, a universal quantifier over \(k\in\mathbb N\), and an inner conjunction of two equalities. A term of `IsGradientProjectionTrajectory` consists of a proof of \( \mu=\lambda/(1+\lambda) \) together with, for each \(k\), proofs of the two recurrence equations. The `noncomputable` marker indicates that the definition is not used as executable code; it simply names this proposition. No additional mathematical conclusion is derived.

