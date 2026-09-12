## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_thm_1.lean`

## Lean statement
```lean
theorem subdifferential_demiclosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hf_lsc : LowerSemicontinuous f)
    (x_seq : ℕ → H) (u_seq : ℕ → H) (x u : H)
    (hx_weak : Tendsto (fun n : ℕ => toWeakSpace ℝ H (x_seq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu_strong : Tendsto u_seq atTop (𝓝 u))
    (hu_sub : ∀ n, u_seq n ∈ subdifferential f (x_seq n)) :
    u ∈ subdifferential f x
```

## Statement explanation
The declaration `subdifferential_demiclosed` states a demiclosedness property of the subdifferential of a convex, lower semicontinuous, real-valued function. Let $H$ be a complete real inner product space; in Lean this is encoded by the typeclasses `NormedAddCommGroup`, `InnerProductSpace ℝ`, and `CompleteSpace`. Let $f : H \to \mathbb{R}$. The hypotheses on $f$ are:

- `hf_conv`: $f$ is convex on all of $H$, meaning for all $x,y\in H$ and all $t$ with $0\le t\le 1$,

$$
f((1-t)x+ty)\le (1-t)f(x)+t f(y).
$$

- `hf_lsc`: $f$ is lower semicontinuous, meaning that if a sequence converges to a point, then the value at the limit is at most the liminf of the values along the sequence.

The data of the theorem are sequences $x_{\mathrm{seq}} : \mathbb{N}\to H$ and $u_{\mathrm{seq}} : \mathbb{N}\to H$, written $x_n=x_{\mathrm{seq}}(n)$ and $u_n=u_{\mathrm{seq}}(n)$, together with points $x,u\in H$. The hypotheses are:

- `hx_weak`: the sequence $x_n$ converges weakly to $x$. In Lean this is expressed as convergence after applying the canonical map `toWeakSpace ℝ H`, so it is exactly weak convergence in the weak topology.
- `hu_strong`: the sequence $u_n$ converges strongly to $u$, i.e. converges in the norm topology.
- `hu_sub`: for every $n$, the vector $u_n$ is a subgradient of $f$ at $x_n$. Equivalently,

$$
\forall z\in H,\qquad f(z)\ge f(x_n)+\langle u_n,z-x_n\rangle.
$$

The conclusion is that $u$ is a subgradient of $f$ at $x$, i.e.

$$
u\in \partial f(x),
$$

which means

$$
\forall z\in H,\qquad f(z)\ge f(x)+\langle u,z-x\rangle.
$$

Thus the theorem says that the subdifferential relation is closed under weak convergence in the base point and strong convergence in the subgradient: if each $u_n$ is a subgradient at $x_n$, $x_n$ converges weakly to $x$, and $u_n$ converges strongly to $u$, then $u$ is a subgradient at $x$.

## Lean proof
```lean
by
  rw [subdifferential, Set.mem_setOf_eq]
  exact subdifferential_demiclosed_real_valued hf_conv hf_lsc hx_weak hu_strong (by
    intro n z
    have h := hu_sub n
    rw [subdifferential, Set.mem_setOf_eq] at h
    exact h z)
```

## Proof explanation
The proof begins with the goal

$$
u\in \partial f(x).
$$

The tactic
```lean
rw [subdifferential, Set.mem_setOf_eq]
```
unfolds the definition of `subdifferential` and then uses `Set.mem_setOf_eq`, the basic membership rule for set-builder notation. If a set is written as $`\{y\mid P(y)\}`$, then$`a\in\{y\mid P(y)\}`$is equivalent to$P(a)$. Since `subdifferential f x` is defined as

```math
\{u\in H\mid \forall y\in H,\ f(y)\ge f(x)+\langle u,y-x\rangle\},
```

this rewrite changes the goal to

$$
\forall y\in H,\qquad f(y)\ge f(x)+\langle u,y-x\rangle.
$$

Next the proof invokes the cited lemma `subdifferential_demiclosed_real_valued`. That lemma says: if $f$ is convex on all of $H$, lower semicontinuous, $x_n$ converges weakly to $x$, $u_n$ converges strongly to $u$, and for every $n$ and every $z$,

$$
f(z)\ge f(x_n)+\langle u_n,z-x_n\rangle,
$$

then for every $z$,

$$
f(z)\ge f(x)+\langle u,z-x\rangle.
$$

This conclusion is exactly the unfolded goal above, so the proof supplies the lemma’s hypotheses and then uses `exact` to apply it.

The first four arguments to the lemma are directly `hf_conv`, `hf_lsc`, `hx_weak`, and `hu_strong`. The remaining needed hypothesis is the pointwise subgradient inequality for all $n$ and $z$. The theorem’s hypothesis `hu_sub` gives only the membership form

$$
u_n\in \partial f(x_n)
$$

for each $n$. Therefore the proof constructs the required inequality by an anonymous `by` block:

- `intro n z` introduces an arbitrary $n\in\mathbb{N}$ and $z\in H$. The goal for this subproof becomes

$$
f(z)\ge f(x_n)+\langle u_n,z-x_n\rangle.
$$

- `have h := hu_sub n` obtains the hypothesis that $u_n\in\partial f(x_n)$.
- `rw [subdifferential, Set.mem_setOf_eq] at h` unfolds that membership in the local hypothesis $h$. After the rewrite, $h$ has become the universal statement

$$
\forall y\in H,\qquad f(y)\ge f(x_n)+\langle u_n,y-x_n\rangle.
$$

- `exact h z` applies that statement to $y=z$, producing

$$
f(z)\ge f(x_n)+\langle u_n,z-x_n\rangle,
$$

which closes the subproof.

The lemma `subdifferential_demiclosed_real_valued` then yields

$$
\forall z\in H,\qquad f(z)\ge f(x)+\langle u,z-x\rangle,
$$

which is precisely the goal after unfolding $u\in\partial f(x)$. Hence the final `exact` completes the proof. No `simp` or `linarith` step is used; the argument is a definitional unfolding of the subdifferential followed by application of the cited demiclosedness lemma.

