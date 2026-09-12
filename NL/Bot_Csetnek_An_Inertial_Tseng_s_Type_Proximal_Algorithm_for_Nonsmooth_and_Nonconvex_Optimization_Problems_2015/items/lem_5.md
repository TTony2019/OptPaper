## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_5.lean`

## Lean statement
```lean
theorem lemma_3_5_subgradient_estimate {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) :
    ∀ n, 2 <= n ->
      subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) ∧
        ‖subgradientEstimateVector A n‖ <=
          (A.Lgrad_u / A.lambda n + P.Lgrad_h) * ‖A.x n - A.p n‖ +
            (A.alphaSeq n / A.lambda n) * (1 + A.lambda (n - 1) * P.Lgrad_h) *
              ‖A.x (n - 1) - A.p (n - 1)‖
```

## Statement explanation
The theorem `lemma_3_5_subgradient_estimate` concerns a fixed natural number $m$, a problem datum $P$ of type `ProblemData m`, and algorithm data $A$ of type `AlgorithmData P`. For each natural number $n$ satisfying $2\le n$, it makes two assertions about the vector

$$
s_n := \operatorname{subgradientEstimateVector}(A,n).
$$

Writing

$$
x_n=A.x_n,\qquad p_n=A.p_n,\qquad \lambda_n=A.\lambda_n,\qquad \alpha_n=A.\operatorname{alphaSeq}_n,
$$

$$
L_u=A.Lgrad_u,\qquad L_h=P.Lgrad_h,\qquad u=A.u,\qquad h=P.h,\qquad F=P.\mathrm{objective},
$$

the vector $s_n$ is the four-term expression

$$
\begin{aligned}
s_n={}&
\frac{1}{\lambda_n}\bigl(\nabla u(x_n)-\nabla u(p_n)\bigr)
+\bigl(\nabla h(p_n)-\nabla h(x_n)\bigr)\\
&+\frac{\alpha_n}{\lambda_n}\bigl(p_{n-1}-x_{n-1}\bigr)
+\frac{\alpha_n\lambda_{n-1}}{\lambda_n}
\bigl(\nabla h(x_{n-1})-\nabla h(p_{n-1})\bigr).
\end{aligned}
$$

The first conclusion is that

$$
s_n \in \partial_L F(p_n),
$$

where $\partial_L$ is the limiting subdifferential. Concretely, the cited definition `limitingSubdifferential` says that $v\in\partial_L f(x)$ exactly when $x$ lies in the effective domain of $f$ and there exist sequences $x_k\to x$, $v_k\to v$ such that $f(x_k)\to f(x)$, and each $v_k$ is a Fréchet subgradient of $f$ at $x_k$. Thus the theorem produces a particular limiting subgradient of the objective at the point $p_n$.

The second conclusion is the norm estimate

$$
\|s_n\|
\le
\left(\frac{L_u}{\lambda_n}+L_h\right)\|x_n-p_n\|
+
\frac{\alpha_n}{\lambda_n}
\left(1+\lambda_{n-1}L_h\right)
\|x_{n-1}-p_{n-1}\|.
$$

So the vector $s_n$ is both a limiting subgradient of the objective at $p_n$ and is controlled in norm by the two previous displacement quantities $\|x_n-p_n\|$ and $\|x_{n-1}-p_{n-1}\|$, with coefficients built from the algorithm steps $\lambda_n,\lambda_{n-1},\alpha_n$ and the constants $L_u,L_h$.

## Lean proof
```lean
by
  intro n hn
  have hn1 : 1 <= n := by omega
  have hbase := algorithm_optimality_subgradient_base A n hn1
  have hvec := subgradientEstimateVector_eq_base A hn
  have hmembership :
      subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) := by
    rw [hvec]
    exact hbase
  exact ⟨hmembership, subgradientEstimateVector_norm_bound A hn⟩
```

## Proof explanation
The proof begins by introducing an arbitrary iteration index and the relevant hypothesis. The command `intro n hn` fixes $n$ and assumes

$$
2\le n.
$$

After this, the goal is precisely the two-part conclusion for this fixed $n$: membership of $s_n$ in the limiting subdifferential and the displayed norm bound.

Next, the proof derives a weaker inequality:

$$
1\le n.
$$

This is done by
```lean
have hn1 : 1 <= n := by omega
```
The tactic `omega` is a linear-arithmetic decision procedure, and here it uses $2\le n$ to conclude $1\le n$. This weaker hypothesis is needed because the cited optimality theorem is stated under $1\le n$, not directly under $2\le n$.

The proof then invokes the cited theorem `algorithm_optimality_subgradient_base`:
```lean
have hbase := algorithm_optimality_subgradient_base A n hn1
```
That theorem says that, whenever $1\le n$, the vector

$$
b_n=
\frac{1}{\lambda_n}\bigl(\nabla u(x_n)-\nabla u(p_n)\bigr)
+\bigl(\nabla h(p_n)-\nabla h(x_n)\bigr)
+\frac{\alpha_n}{\lambda_n}\bigl(x_n-x_{n-1}\bigr)
$$

belongs to

$$
\partial_L F(p_n).
$$

This is the “base” subgradient estimate: it has the same first two gradient-difference terms as $s_n$, but its last term uses $x_n-x_{n-1}$ rather than the two final terms appearing in the definition of $s_n$. The result `hbase` therefore supplies the desired membership for $b_n$, not yet for $s_n$.

The proof also invokes the cited equality
```lean
have hvec := subgradientEstimateVector_eq_base A hn
```
The theorem `subgradientEstimateVector_eq_base` states that, under the assumption $2\le n$,

$$
\operatorname{subgradientEstimateVector}(A,n)=b_n.
$$

In other words, for $n\ge2$, the four-term vector $s_n$ is equal to the three-term base vector $b_n$

$$
\frac{1}{\lambda_n}\bigl(\nabla u(x_n)-\nabla u(p_n)\bigr)
+\bigl(\nabla h(p_n)-\nabla h(x_n)\bigr)
+\frac{\alpha_n}{\lambda_n}\bigl(x_n-x_{n-1}\bigr).
$$

This equality is the bridge between the known membership of $b_n$ and the required membership of $s_n$.

The membership part is then proved as follows:
```lean
have hmembership :
      subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) := by
    rw [hvec]
    exact hbase
```
The goal is

$$
s_n\in\partial_L F(p_n).
$$

The command `rw [hvec]` rewrites the goal using the equality $s_n=b_n$, replacing $s_n$ by $b_n$. The rewritten goal is exactly

$$
b_n\in\partial_L F(p_n).
$$

The command `exact hbase` closes this goal because `hbase` is precisely a proof of that membership. Thus the first conjunct of the theorem is established.

Finally, the proof closes the whole theorem with
```lean
exact ⟨hmembership, subgradientEstimateVector_norm_bound A hn⟩
```
The anonymous constructor $\langle\cdot,\cdot\rangle$ builds a proof of a conjunction. The first component is `hmembership`, the limiting-subgradient statement just proved. The second component is supplied by the cited theorem `subgradientEstimateVector_norm_bound`. That theorem states, for $2\le n$,

$$
\|\operatorname{subgradientEstimateVector}(A,n)\|
\le
\left(\frac{L_u}{\lambda_n}+L_h\right)\|x_n-p_n\|
+
\frac{\alpha_n}{\lambda_n}
\left(1+\lambda_{n-1}L_h\right)
\|x_{n-1}-p_{n-1}\|.
$$

This is exactly the second required conjunct. Therefore the conjunction for this arbitrary $n\ge2$ is proved, and since $n$ was arbitrary, the original universally quantified statement follows. No use of `simp` or `linarith` occurs in the proof; the main logical steps are arithmetic weakening by `omega`, rewriting by `rw`, and direct term closure by `exact`.

