## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_7.lean`

## Lean statement
```lean
theorem auxiliaryG_defined_of_two_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (_hk : 2 ≤ k) :
    auxiliaryG u y a b lam q k _hk =
      inner ℝ (zSequence u y a b lam k (by omega)) (u k - q) -
        ∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega))
          (velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega))
```

## Statement explanation
The declaration `auxiliaryG_defined_of_two_le` is a theorem about a real inner product space $H$. The typeclass assumptions say that $H$ is a normed additive commutative group and also a real inner product space, so subtraction such as $u_k-q$ and real-valued inner products $\langle\cdot,\cdot\rangle$ are available. The variables are: two sequences $u,y:\mathbb N\to H$, three real parameters $a,b,\lambda\in\mathbb R$, a vector $q\in H$, a natural number $k\in\mathbb N$, and an explicit hypothesis $2\le k$, named `_hk`. The theorem is conditional on $2\le k$; it says nothing about indices $k<2$.

The conclusion is an equality of real numbers. With the side-condition proofs suppressed, it has the form

$$
\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k)
=\left\langle z_k,\; u_k-q\right\rangle
-\sum_{i=2}^{k}\left\langle z_i,\; v_i\right\rangle,
$$

where $z_i$ denotes the vector `zSequence` evaluated at $u,y,a,b,\lambda,i$, and $v_i$ denotes the vector `velocity` evaluated at $u,i$, in both cases with the required side-condition proofs attached. The first term uses $z_k$ at the index $k$, whose side condition is supplied from $2\le k$. The sum is over the attached finite set `Finset.Icc 2 k`, which mathematically is the inclusive interval $\{2,3,\dots,k\}$; for each such $i$, the side conditions for `zSequence` and `velocity` are supplied from the lower bound $2\le i$. Thus the theorem states that, for $k\ge 2$, the auxiliary quantity `auxiliaryG` equals the inner product of the $k$-th $z$-term with the displacement $u_k-q$, minus the sum from $i=2$ to $i=k$ of the inner products of the $i$-th $z$-term with the $i$-th velocity term. The definitions of `zSequence` and `velocity` are not included in the provided source, so their internal mathematical content cannot be inferred from this declaration; only their roles as vector-valued auxiliary and velocity sequences appear here. The theorem contains no convexity, minimization, or convergence assumptions; it is simply the defining formula for `auxiliaryG` on the range $k\ge 2$.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof consists of the single tactic `rfl`. In Lean, `rfl` proves a goal of the form $x=x$ and can also close a goal $x=y$ when $x$ and $y$ are definitionally equal after unfolding reducible definitions. Here the left-hand side is `auxiliaryG` applied to the given arguments, and the right-hand side is the displayed expression. The definition of `auxiliaryG` in the relevant range $2\le k$ is such that unfolding it makes the left-hand side reduce exactly to the right-hand side. Therefore the theorem is a definitional identity: it records the value of `auxiliaryG` under the hypothesis $2\le k$, rather than deriving a new mathematical fact from other properties.

The occurrences of `by omega` in the statement are side-condition proofs, not separate steps of the theorem proof. The tactic `omega` solves linear arithmetic goals over natural numbers. In the first term, the proof `by omega` uses the hypothesis $2\le k$ to supply the inequality side condition required by `zSequence` at index $k$. Inside the sum, each element of `(Finset.Icc 2 k).attach` is a pair consisting of a natural number $i$ and a proof that $i\in \mathrm{Icc} 2 k$. The expression `Finset.mem_Icc.mp i.2` converts that membership proof into the conjunction $2\le i\land i\le k$, and the projection `.1` extracts the lower bound $2\le i$. Then `omega` uses that lower bound to discharge the side conditions required by `zSequence` and `velocity` at index $i$. These proof arguments are proof-irrelevant, so they do not affect the mathematical value of the terms.

The finite set `Finset.Icc 2 k` is the set $\{2,3,\dots,k\}$, and `.attach` turns it into a finset of elements carrying proofs of membership. In the sum, `i.1` is the underlying natural number and `i.2` is its membership proof. The notation `inner ℝ` denotes the real inner product, so every summand is a real number and the whole equality is an equality in $\mathbb R$. No named theorem or lemma is invoked in the proof, and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` are used. The only mathematical content is the definitional unfolding of `auxiliaryG` into the displayed inner-product expression.

