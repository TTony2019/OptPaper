## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_def_4.lean`

## Lean statement
```lean
def IsSaddlePoint {E U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (F : U → ℝ) (fbar : E → U) (Q : Set E) (lstar : U) (xstar : E) : Prop :=
  lstar ∈ subdifferential (fun y => (F y : EReal)) 0 ∧ xstar ∈ Q ∧
    ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, ∀ x ∈ Q,
      inner ℝ l (fbar xstar) ≤ inner ℝ lstar (fbar xstar) ∧
        inner ℝ lstar (fbar xstar) ≤ inner ℝ lstar (fbar x)
```

## Statement explanation
The declaration introduces the predicate `IsSaddlePoint`. Its implicit parameters are two types \(E\) and \(U\), with the assumptions that \(U\) is a normed additive commutative group and a real inner-product space. Thus \(U\) carries a real inner product \(\langle \cdot,\cdot\rangle\) and a zero vector \(0\). The type \(E\) is unrestricted in this declaration.

The explicit data are:

- \(F: U \to \mathbb R\), a real-valued function on \(U\). Inside the subdifferential it is viewed as the extended-real function
  \[
  f: U \to \overline{\mathbb R},\qquad f(y)=(F y : \overline{\mathbb R}),
  \]
  where \(\overline{\mathbb R}\) is Lean’s type `EReal` of extended real numbers.
- \(\bar f: E \to U\), a map from \(E\) to \(U\).
- \(Q \subseteq E\), the admissible set for the variable \(x\).
- \(l^\star \in U\), the proposed dual variable.
- \(x^\star \in E\), the proposed primal variable.

The predicate
\[
\operatorname{IsSaddlePoint}(F,\bar f,Q,l^\star,x^\star)
\]
asserts three things. First,
\[
l^\star \in \partial f(0),
\]
where \(\partial f(0)\) denotes the subdifferential of the extended-real function \(f\) at the zero vector of \(U\). In the usual subgradient sense, this means that \(l^\star\) is a subgradient of \(f\) at \(0\), i.e.
\[
f(0)+\langle l^\star,z-0\rangle \le f(z)
\quad\text{for all }z\in U.
\]
Since \(f\) is the extended-real coercion of the real-valued function \(F\), and since the point is \(0\), this reads equivalently as
\[
F(0)+\langle l^\star,z\rangle \le F(z)
\quad\text{for all }z\in U.
\]
Second,
\[
x^\star \in Q.
\]
Third, for every \(l\in \partial f(0)\) and every \(x\in Q\),
\[
\langle l,\bar f(x^\star)\rangle \le \langle l^\star,\bar f(x^\star)\rangle
\]
and
\[
\langle l^\star,\bar f(x^\star)\rangle \le \langle l^\star,\bar f(x)\rangle.
\]
Thus \(l^\star\) maximizes the linear functional
\[
l \mapsto \langle l,\bar f(x^\star)\rangle
\]
over the subdifferential \(\partial f(0)\), while \(x^\star\) minimizes the function
\[
x \mapsto \langle l^\star,\bar f(x)\rangle
\]
over \(Q\). Equivalently, for all admissible \(l\) and \(x\),
\[
\langle l,\bar f(x^\star)\rangle
\le
\langle l^\star,\bar f(x^\star)\rangle
\le
\langle l^\star,\bar f(x)\rangle.
\]
So \((l^\star,x^\star)\) is a saddle point of the pairing
\[
L(l,x)=\langle l,\bar f(x)\rangle
\]
on the product \(\partial f(0)\times Q\), with a maximum in the \(l\)-variable and a minimum in the \(x\)-variable. The first two conjuncts ensure that the proposed pair actually lies in that product.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The source declares a `def`, and its proof field says explicitly that there is no separate proof part. Therefore there are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named theorem or lemma is invoked.

The only mathematical content is the defining right-hand side after the `:=`. It is a conjunction. The first conjunct says \(l^\star\in\partial f(0)\), i.e. that \(l^\star\) is a subgradient of the extended-real function \(f\) at \(0\). The second conjunct says \(x^\star\in Q\), i.e. that the proposed primal point is admissible. The third conjunct is universally quantified: for every \(l\) satisfying \(l\in\partial f(0)\) and every \(x\) satisfying \(x\in Q\), it asserts the two inequalities
\[
\langle l,\bar f(x^\star)\rangle \le \langle l^\star,\bar f(x^\star)\rangle
\]
and
\[
\langle l^\star,\bar f(x^\star)\rangle \le \langle l^\star,\bar f(x)\rangle.
\]
These two inequalities are joined by logical conjunction \(\wedge\). The variables \(l\) and \(x\) are bound by the universal quantifiers, and the membership conditions \(l\in\partial f(0)\) and \(x\in Q\) are hypotheses inside those quantifiers. Since \(l^\star\) itself lies in \(\partial f(0)\) and \(x^\star\) lies in \(Q\), choosing \(l=l^\star\) and \(x=x^\star\) makes the two inequalities equalities, but the definition records the stronger universal saddle inequalities for all admissible \(l\) and \(x\). This unpacking is definitional, not a proof step.

