## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_8.lean`

## Lean statement
```lean
def IsIFBSignalRecoveryTrajectory {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [InnerProductSpace ℝ K] (prox : (n → ℝ) → n → ℝ) (A : (n → ℝ) → K) (At : K → n → ℝ)
    (data : K) (a b lam γ : ℝ) (_hAt : ∀ x z, inner ℝ (A x) z = ∑ i, x i * (At z) i)
    (f : (n → ℝ) → EReal) (_hf : ∀ v, f v = ((lam * γ * ∑ i, |v i| : ℝ) : EReal))
    (hfproper : ERealFunction.IsProper f) (hflsc : IsClosed (ERealFunction.epigraph f))
    (hfconvex : Convex ℝ (ERealFunction.epigraph f))
    (_hprox : ∀ x, ERealFunction.IsProxPoint (ERealFunction.properIoi f hfproper) x (prox x))
    (u y : ℕ → n → ℝ) : Prop := ∀ k,
  u (k + 1) = prox ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (2 * lam / (1 + lam * b)) • At (A (u (k + 1)) - data)
```

## Statement explanation
The declaration `IsIFBSignalRecoveryTrajectory` defines a predicate on two sequences of vectors. Its ambient data are a finite index type $n$, so that functions $n\to\mathbb R$ are finite real vectors, and a real inner product space $K$. The definition takes a proximity-type map `prox` of type $(n\to\mathbb R)\to(n\to\mathbb R)$, a forward map $A:(n\to\mathbb R)\to K$, a map `At` of type $K\to(n\to\mathbb R)$, a datum $\mathrm{data}\in K$, real parameters $a,b,\lambda,\gamma$, an extended-real function $f:(n\to\mathbb R)\to\overline{\mathbb R}$, and two sequences $u,y:\mathbb N\to(n\to\mathbb R)$.

The contextual hypotheses supplied as parameters are as follows. The hypothesis `_hAt` says that for every $x:n\to\mathbb R$ and every $z\in K$,

```math
\langle A x,z\rangle_K=\sum_{i} x_i\,(\text{At}(z))_i.
```

This is the adjoint identity saying that `At` acts as the adjoint of $A$ with respect to the standard coordinate inner product on $n\to\mathbb R$. The hypothesis `_hf` says that for every $v:n\to\mathbb R$,

$$
f(v)=\left(\lambda\gamma\sum_i |v_i|\right)
$$

as an extended real number. Thus $f$ is the scaled $\ell_1$-type regularizer. The hypotheses `hfproper`, `hflsc`, and `hfconvex` assert respectively that $f$ is proper, that its epigraph is closed, and that its epigraph is convex over $\mathbb R$. The hypothesis `_hprox` asserts that for every $x$, `prox x` is a proximal point of the imported extended-real object `ERealFunction.properIoi f hfproper` at $x$. The source does not expand `ERealFunction.properIoi` or `ERealFunction.IsProxPoint` here, so only that visible assertion is part of the present declaration.

The proposition defined by the declaration is: for every $k\in\mathbb N$,

$$
u_{k+1}=\mathrm{prox}\bigl((1-\lambda a)u_k+(\lambda b)y_k\bigr)
$$

and

$$
y_{k+1}
=\frac{1}{1+\lambda b}y_k
+\frac{\lambda a}{1+\lambda b}u_{k+1}
-\frac{2\lambda}{1+\lambda b}A^{\top}\bigl(A u_{k+1}-\mathrm{data}\bigr),
$$

where $u_k=u(k)$, $y_k=y(k)$, and $A^{\top}$ denotes the Lean parameter `At`. The operations are pointwise vector operations, and scalar multiplication is pointwise. Thus the predicate says that the sequence $u$ follows an inertial forward-backward/proximal update and the sequence $y$ follows a momentum-like update with a data-consistency correction involving the adjoint of the residual $A u_{k+1}-\mathrm{data}$. No initial conditions on $u_0$ or $y_0$ are included. Also, the parameters $\gamma$ and $f$ do not appear in the recurrence itself; they occur only through the surrounding hypotheses about the regularizer and the proximity operator.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, and the Lean proof section is only the comment `-- No separate proof part.` Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named local theorem or lemma is invoked.

The body of the definition is exactly the quantified conjunction

$$
\forall k\in\mathbb N,\quad
P(k)\land Q(k),
$$

where $P(k)$ is the equality defining $u_{k+1}$ and $Q(k)$ is the equality defining $y_{k+1}$. To prove that a given pair of sequences satisfies the predicate, one must prove both equalities for every natural number $k$. To use a hypothesis that the predicate holds, one may specialize it to any chosen $k$ and extract either of the two conjuncts.

The Lean notation `•` denotes scalar multiplication, while `+` and `-` are pointwise vector arithmetic on functions $n\to\mathbb R$. The notation `∑ i` denotes the finite sum over the finite index type $n$. The coercion $((\ldots:\mathbb R):\mathbb EReal)$ turns the real number $\lambda\gamma\sum_i |v_i|$ into an extended real in the statement of `_hf`. The hypotheses `_hAt`, `_hf`, `hfproper`, `hflsc`, `hfconvex`, and `_hprox` are arguments of the definition, but the recurrence body does not reference them; mathematically they describe the intended setting and the proximity operator, while the predicate on $u,y$ itself consists only of the two displayed recurrence equations.

