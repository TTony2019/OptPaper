## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_6.lean`

## Lean statement
```lean
noncomputable def IsIFBCQTrajectory {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (C : Set H) (hC : IsChebyshev C)
    (Q : Set K) (hQ : IsChebyshev Q) (A : H → K) (At : K → H)
    (_hAt : ∀ x z, inner ℝ (A x) z = inner ℝ x (At z)) (a b lam : ℝ)
    (u y : ℕ → H) : Prop := 0 < a ∧ 0 < b ∧ 0 < lam ∧ ∀ k,
  u (k + 1) = projectionPoint C hC ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (lam / (1 + lam * b)) • (u (k + 1) - At
      (A (u (k + 1)) - projectionPoint Q hQ (A (u (k + 1)))))
```

## Statement explanation
The declaration defines a predicate named `IsIFBCQTrajectory`. It is parameterized by two real inner-product spaces \(H\) and \(K\), meaning each is a normed additive group equipped with a real inner product; no completeness assumption is present in the declaration. It also takes sets \(C\subseteq H\) and \(Q\subseteq K\), together with parameters \(h_C\) and \(h_Q\) supplying the Chebyshev hypotheses for \(C\) and \(Q\). In the defining body these are used as arguments to `projectionPoint`, so \(P_C=\text{projectionPoint }C\,h_C\) and \(P_Q=\text{projectionPoint }Q\,h_Q\) stand for the projections associated with \(C\) and \(Q\). The exact definition of `IsChebyshev` is not included in the snippet, but its role here is precisely to supply the projection onto the set.

The declaration further takes maps \(A:H\to K\) and \(A^\top:K\to H\), where \(A^\top\) is the Lean function `At`, and a parameter `_hAt` asserting adjointness:
\[
\forall x\in H,\ \forall z\in K,\quad
\langle A x,z\rangle_K=\langle x,A^\top z\rangle_H .
\]
The leading underscore indicates that this parameter is unused in the defining body: it is an input to the definition, but it is not itself a conjunct of the predicate that is defined.

Finally, the declaration takes real parameters \(a,b,\lambda\) and two sequences \(u,y:\mathbb N\to H\). Writing \(u_k=u(k)\) and \(y_k=y(k)\), the predicate `IsIFBCQTrajectory C hC Q hQ A At _hAt a b lam u y` says
\[
0<a \;\land\; 0<b \;\land\; 0<\lambda \;\land\;
\forall k\in\mathbb N,\quad
\Bigl(
u_{k+1}=P_C\bigl((1-\lambda a)u_k+(\lambda b)y_k\bigr)
\;\land\;
y_{k+1}=
\frac{1}{1+\lambda b}y_k
+\frac{\lambda a}{1+\lambda b}u_{k+1}
-\frac{\lambda}{1+\lambda b}
\Bigl(u_{k+1}-A^\top\bigl(Au_{k+1}-P_Q(Au_{k+1})\bigr)\Bigr)
\Bigr).
\]
Thus \(u\) is updated by projecting an inertial linear combination of \(u_k\) and \(y_k\) onto \(C\). The sequence \(y\) is updated by a weighted combination of \(y_k\) and \(u_{k+1}\), together with a correction obtained from the residual of \(Au_{k+1}\) after projection onto \(Q\), brought back to \(H\) by the adjoint map \(A^\top\). The predicate does not impose initial conditions on \(u_0\) or \(y_0\), nor does it assert existence, convergence, or optimality of the sequences; it only classifies the pair of sequences as satisfying this recurrence.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, and the source explicitly says that there is no proof part. The part after `:=` is the definition body, a proposition built from logical connectives and quantifiers rather than a proof of that proposition.

The body is a conjunction: first \(0<a\), then \(0<b\), then \(0<\lambda\), and finally a statement quantified over all natural numbers \(k\). The quantifier ranges over \(\mathbb N\), and inside its scope there is another conjunction of two equalities, one for \(u(k+1)\) and one for \(y(k+1)\). Thus both recurrence equations must hold for every \(k\). The Lean symbol `∧` is logical conjunction, `∀ k` is universal quantification, `•` is scalar multiplication, `/` is real division, and `k+1` is the successor of the natural number \(k\). Under the positivity conditions \(0<b\) and \(0<\lambda\), the denominator \(1+\lambda b\) is positive, so the fractions in the \(y\)-update are mathematically well-defined.

No named theorem, lemma, or local result is invoked in this declaration. The only mathematical objects used in the body are the Chebyshev projections via `projectionPoint`, the maps \(A\) and \(A^\top\), and the scalar operations on \(H\) and \(K\). The adjointness parameter `_hAt` is not used in the body, so the predicate itself does not assert the adjoint identity; it only accepts it as an input to the definition. The `noncomputable` marker indicates that the definition is not intended as an executable algorithm, which is consistent with its use of projection data. There are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, because there is no proof script.

