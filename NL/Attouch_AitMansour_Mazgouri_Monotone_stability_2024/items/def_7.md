## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/def_7.lean`

## Lean statement
```lean
theorem def_7_yosida_equivalence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    SetValuedOperator.resolventDistance A B hA hB lam ρ hlam hρ =
      lam * sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
        q = ‖(lam⁻¹ • (u - SetValuedOperator.resolventMap A hA lam hlam u)) -
          (lam⁻¹ • (u - SetValuedOperator.resolventMap B hB lam hlam u))‖}
```

## Statement explanation
The theorem `def_7_yosida_equivalence` is stated in a complete real inner product space $H$, i.e. a real Hilbert space: $H$ is a normed additive commutative group, has a real inner product, and is complete. It takes two set-valued operators $A$ and $B$ on $H$, together with proofs $h_A$ and $h_B$ that $A$ and $B$ are maximal monotone. It also takes real parameters $\lambda$ and $\rho$, with hypotheses $h_\lambda : 0 < \lambda$ and $h_\rho : 0 < \rho$.

Let $J_\lambda^A(u)$ denote the value of the resolvent map of $A$ at parameter $\lambda$ evaluated at $u$, i.e. `SetValuedOperator.resolventMap A hA lam hlam u`, and define $J_\lambda^B(u)$ analogously. The conclusion is the identity

$$
\operatorname{resolventDistance}(A,B;h_A,h_B,\lambda,\rho;h_\lambda,h_\rho)
=
\lambda \cdot \sup \left\{
q \in \mathbb{R}
\;\middle|\;
\exists u \in H,\ \|u\| \le \rho
\ \text{and}\ 
q =
\left\|
\lambda^{-1}\cdot(u-J_\lambda^A(u))
-
\lambda^{-1}\cdot(u-J_\lambda^B(u))
\right\|
\right\}.
$$

The expression inside the norm is the difference between the $\lambda$-Yosida approximations associated with $A$ and $B$ at $u$, namely

$$
A_\lambda(u)=\lambda^{-1}(u-J_\lambda^A(u)),
\qquad
B_\lambda(u)=\lambda^{-1}(u-J_\lambda^B(u)).
$$

Thus the set whose supremum is taken consists of all real numbers $q$ that occur as the norm of the difference $A_\lambda(u)-B_\lambda(u)$ for points $u$ in the closed ball of radius $\rho$. The right-hand side is therefore $\lambda$ times the supremum of these differences of Yosida approximations over that ball. The left-hand side is the formal resolvent distance between the two maximal monotone operators for the same parameters. The theorem says exactly that this resolvent distance is given by the displayed Yosida-approximation supremum formula.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof is the single tactic `rfl`. In Lean, `rfl` proves a goal of the form $x=x$ by reflexivity, and it succeeds when the two sides are definitionally equal after unfolding the relevant transparent definitions. Here, after unfolding the definition of `SetValuedOperator.resolventDistance` for the arguments $A,B,h_A,h_B,\lambda,\rho,h_\lambda,h_\rho$, the left-hand side reduces to the displayed right-hand side

$$
\lambda \cdot \sup \left\{
q \in \mathbb{R}
\;\middle|\;
\exists u \in H,\ \|u\| \le \rho
\ \text{and}\ 
q =
\left\|
\lambda^{-1}\cdot(u-J_\lambda^A(u))
-
\lambda^{-1}\cdot(u-J_\lambda^B(u))
\right\|
\right\}.
$$

Therefore no separate mathematical argument is needed: no `intro`, `rw`, `simp`, or `linarith` step is used, and no named theorem or lemma is invoked. The assumptions $h_A,h_B,h_\lambda,h_\rho$ appear only as arguments required by the definitions of the resolvent distance and resolvent map; the identity itself is definitional in this formalization.

