## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_5.lean`

## Lean statement
```lean
theorem zeta_eq_sub_of_one_le {H : Type*} [Sub H] (y : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) :
    zeta y k _hk = y k - y (k - 1)
```

## Statement explanation
The theorem `zeta_eq_sub_of_one_le` concerns an arbitrary type $H$ equipped with a subtraction operation, written in Lean as `Sub H`. It does not assume that $H$ is a group, a vector space, or has any algebraic laws for subtraction; it only assumes that an expression of the form $a-b$ is available for elements $a,b\in H$. The theorem is quantified over a sequence

$$
y:\mathbb N\to H,
$$

a natural number $k:\mathbb N$, and a proof $h_k$ of the hypothesis

$$
1\le k.
$$

It concludes that

$$
\mathrm{zeta}(y,k,h_k)=y(k)-y(k-1).
$$

Here $k-1$ is the natural-number predecessor, and the hypothesis $1\le k$ guarantees that this is the ordinary predecessor rather than the truncated value at zero. The expression $\mathrm{zeta}(y,k,h_k)$ denotes the value assigned by the previously defined operation `zeta` to the sequence $y$, the index $k$, and the proof that $k$ lies in the admissible range. Thus the theorem says that, for every index $k$ at least $1$, the `zeta` value at $k$ is exactly the backward difference between the $k$-th term and the $(k-1)$-st term of the sequence. It is a computation or characterization lemma exposing the defining formula of `zeta` on the domain $1\le k$.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof consists of the single Lean tactic `rfl`. In Lean, `rfl` proves an equality $a=b$ when the two sides are definitionally equal, meaning that after unfolding definitions and performing computation they reduce to the same expression. Here, unfolding the definition of `zeta` at the arguments $y$, $k$, and the proof `_hk` yields exactly the expression $y(k)-y(k-1)$. Therefore the left-hand side of the theorem and the right-hand side are the same by definition, and `rfl` closes the goal immediately.

No named theorem, lemma, or previously established mathematical fact is invoked. The proof does not use `intro`, `rw`, `simp`, or `linarith`; it is purely a definitional equality check. The hypothesis `1\le k` is passed as the third argument to `zeta`, so it is part of the data required to form the left-hand side. The mathematical content of the proof is therefore simply that the equation stated by the theorem is the defining equation of `zeta` on the range $1\le k$. This theorem can then be used in later arguments to rewrite $\mathrm{zeta}(y,k,h_k)$ as the difference $y(k)-y(k-1)$ whenever $1\le k$.

