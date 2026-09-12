## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_3.lean`

## Lean statement
```lean
theorem velocity_eq_sub_of_one_le {H : Type*} [Sub H] (u : ℕ → H) (k : ℕ) (_hk : 1 ≤ k) :
    velocity u k _hk = u k - u (k - 1)
```

## Statement explanation
The declaration `velocity_eq_sub_of_one_le` is stated for an arbitrary type $H$ carrying a subtraction operation, expressed in Lean by the typeclass `Sub H`. It takes a sequence $u : \mathbb{N} \to H$, a natural number $k : \mathbb{N}$, and a proof `_hk` of the hypothesis $1 \le k$. Its conclusion is

$$
\mathrm{velocity}(u,k,\_hk) = u(k) - u(k-1).
$$

Here $u(k)$ and $u(k-1)$ are elements of $H$, and the subtraction is the binary operation supplied by `Sub H`; no group, module, vector-space, or topological structure on $H$ is assumed. The index $k$ is positive because of the hypothesis $1 \le k$, so $k-1$ is the predecessor of $k$. Thus the theorem says that the `velocity` function applied to the sequence $u$ at time $k$, together with the positivity proof, is definitionally the backward difference between the $k$-th term and the immediately preceding term of $u$. The proof `_hk` is an argument to `velocity` and is what allows the expression to be formed for positive indices.

The theorem is not an algebraic identity about subtraction in an abstract group; it is simply the defining equation of `velocity` in the case $1 \le k$. It asserts no limiting, differentiability, or continuity property, and it does not claim that $u(k)-u(k-1)$ has any special meaning beyond being the value of the subtraction operation.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof consists exactly of `rfl`. In Lean, `rfl` proves an equality $a = b$ when the two sides are definitionally equal, meaning that after unfolding definitions and reducing terms, the left-hand side and right-hand side become the same expression. Here, unfolding the definition of `velocity` for a positive index $k$, with the proof `_hk : 1 \le k` in hand, makes the term `velocity u k _hk` reduce to

$$
u(k) - u(k-1).
$$

Therefore the goal

$$
\mathrm{velocity}(u,k,\_hk) = u(k) - u(k-1)
$$

is a reflexive equality after definitional unfolding, and `rfl` closes it immediately.

No named theorem or lemma is cited. The hypothesis `_hk : 1 \le k` is used only to supply the argument needed to form `velocity u k _hk` and to select the appropriate defining case for positive $k$; it is not used as a separate mathematical input in the proof. The proof does not perform induction, arithmetic reasoning, rewriting by previously established facts, or any appeal to results about subtraction. It relies solely on the definitional equality between `velocity u k _hk` and $u(k)-u(k-1)$.

