## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_4.lean`

## Lean statement
```lean
noncomputable def mechanicalEnergy {H : Type*} [NormedAddCommGroup H] (Θ : H → EReal)
    (u : ℕ → H) (γ : ℝ) (k : ℕ) (hk : 1 ≤ k) : EReal :=
  Θ (u k) + ((γ * ‖velocity u k hk‖ ^ 2 : ℝ) : EReal)
```

## Statement explanation
The declaration `mechanicalEnergy` is a noncomputable definition. It is parametrized by a type $H$ equipped with a `NormedAddCommGroup` structure, so each element of $H$ has a norm taking values in $\mathbb R$. It also takes an extended-real-valued function

$$
\Theta : H \to \mathrm{EReal},
$$

a sequence

$$
u : \mathbb N \to H,
$$

a real coefficient $\gamma \in \mathbb R$, a natural number $k \in \mathbb N$, and a proof $hk$ of the inequality $1 \le k$. The result is an extended real number in $\mathrm{EReal}$.

The body of the definition is

$$
\mathrm{mechanicalEnergy}(\Theta,u,\gamma,k,hk)
=\Theta(u(k))
+\bigl(\gamma\,\|\mathrm{velocity}(u,k,hk)\|^2\bigr)_{\mathrm{EReal}}.
$$

Here $u(k)$ is the $k$-th term of the sequence $u$, and $\mathrm{velocity}(u,k,hk)$ is a term of $H$ supplied by the identifier `velocity`; its norm $\|\mathrm{velocity}(u,k,hk)\|$ is a real number. The expression $\gamma\,\|\mathrm{velocity}(u,k,hk)\|^2$ is first computed in $\mathbb R$, then coerced into $\mathrm{EReal}$. Finally, that coerced real number is added to $\Theta(u(k))$ using the addition operation on extended real numbers.

Thus the declaration defines the mechanical energy at index $k$ as the sum of the objective value $\Theta(u(k))$ and a kinetic term $\gamma$ times the squared norm of the velocity at step $k$. No sign restriction is imposed on $\gamma$. The hypothesis $hk : 1 \le k$ is passed as an argument to `velocity`; it is an auxiliary condition on the index $k$, required because the velocity term is only available for indices at least $1$. The definition itself does not state the formula for `velocity`; it uses only the fact that `velocity u k hk` is an element of $H$ whose norm can be taken.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. `mechanicalEnergy` is a definition, not a theorem, and its Lean body is a single expression rather than a tactic proof. Therefore there are no commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named lemmas or theorems are invoked.

The `noncomputable` keyword marks the definition as one that may use noncomputable data, such as the norm operation supplied by an arbitrary `NormedAddCommGroup` instance on $H$. The expression is evaluated as follows:

1. The sequence $u$ is applied to the index $k$, producing the element $u(k) \in H$.
2. The function $\Theta$ is applied to $u(k)$, producing the extended real number $\Theta(u(k)) \in \mathrm{EReal}$.
3. The term `velocity u k hk` is formed. Its type is $H$, since the norm symbol is applied to it.
4. The norm $\|\mathrm{velocity}(u,k,hk)\|$ is taken in $\mathbb R$ and squared.
5. The real number $\gamma \,\|\mathrm{velocity}(u,k,hk)\|^2$ is multiplied out in $\mathbb R$.
6. That real number is coerced into $\mathrm{EReal}$.
7. The extended-real sum $\Theta(u(k)) + \bigl(\gamma\,\|\mathrm{velocity}(u,k,hk)\|^2\bigr)_{\mathrm{EReal}}$ is formed in $\mathrm{EReal}$.

The hypothesis $hk$ enters only as the third argument to `velocity`; it ensures that the velocity term is being taken at an index $k$ satisfying $1 \le k$. The declaration therefore introduces the mechanical energy functional and assigns it the displayed formula, but it makes no additional mathematical assertion and has no proof obligations to discharge.

