## Source file
`Beck_Teboulle_FISTA_2009/items/lem_5.lean`

## Lean statement
```lean
theorem sequence_inequality {a b : ℕ → ℝ} {c : ℝ}
    (hpos_a : ∀ k, 0 < a k) (hpos_b : ∀ k, 0 < b k)
    (hineq : ∀ k, a k - a (k + 1) ≥ b (k + 1) - b k)
    (hbound : a 1 + b 1 ≤ c) (hc_pos : 0 < c) (k : ℕ) (hk : 1 ≤ k) :
    a k ≤ c
```

## Statement explanation
The theorem `sequence_inequality` concerns two real-valued sequences $a:\mathbb N\to\mathbb R$ and $b:\mathbb N\to\mathbb R$, a real number $c$, and a natural number $k$. Its hypotheses are:

- $a_k>0$ for every natural number $k$;
- $b_k>0$ for every natural number $k$;
- for every $k$,

  $$
  a_k-a_{k+1}\ge b_{k+1}-b_k;
  $$

- $a_1+b_1\le c$;
- $c>0$;
- $1\le k$.

The conclusion is

$$
a_k\le c.
$$

Mathematically, the key point is that the inequality

$$
a_k-a_{k+1}\ge b_{k+1}-b_k
$$

is equivalent to

$$
a_k+b_k\ge a_{k+1}+b_{k+1}.
$$

Thus the sequence of sums $s_k=a_k+b_k$ is nonincreasing. Since

$$
s_1=a_1+b_1\le c,
$$

we have $s_k\le c$. Because $b_k>0$, we also have

$$
a_k<a_k+b_k=s_k,
$$

so $a_k<s_k\le c$, and in particular $a_k\le c$. The proof as written does not actually use the hypotheses $a_k>0$ or $c>0$; they are present in the statement but not invoked in the Lean proof.

## Lean proof
```lean
by
  have htelescope : a 1 - a k ≥ b k - b 1 := by
    refine Nat.le_induction (by simpa using le_refl (0 : ℝ)) (fun m hm h_ih => ?_) k hk
    have hineq_m := hineq m
    linarith
  have hpos_bk : 0 < b k := hpos_b k
  linarith
```

## Proof explanation
The proof starts by proving the telescoped inequality

$$
a_1-a_k\ge b_k-b_1.
$$

It defines this as the local fact `htelescope`. No `intro` command is used here, because the variables and hypotheses of the theorem are already available in the proof context.

To prove `htelescope`, the proof uses `Nat.le_induction`. The predicate being proved by induction is

$$
P(m):\quad a_1-a_m\ge b_m-b_1.
$$

The induction starts at $m=1$, as indicated by the later application to $k$ with the hypothesis $1\le k$.

The base case is proved by
```lean
by simpa using le_refl (0 : ℝ)
```
The term `le_refl (0 : ℝ)` proves $0\le 0$. The target base case is $P(1)$, namely

$$
a_1-a_1\ge b_1-b_1.
$$

Both sides simplify to $0$, so $0\ge 0$, which is the same as $0\le 0$. The tactic `simpa` performs these simplifications and uses `le_refl` to close the base case.

The induction step is
```lean
fun m hm h_ih => ?_
```
Here $m$ is the current index, `hm` is the hypothesis $1\le m$, and `h_ih` is the induction hypothesis

$$
P(m):\quad a_1-a_m\ge b_m-b_1.
$$

The goal in this step is to prove $P(m+1)$, namely

$$
a_1-a_{m+1}\ge b_{m+1}-b_1.
$$

The proof invokes `hineq m`, which is exactly the given inequality specialized to the index $m$:

$$
a_m-a_{m+1}\ge b_{m+1}-b_m.
$$

Adding this inequality to the induction hypothesis gives

$$
(a_1-a_m)+(a_m-a_{m+1})
\ge
(b_m-b_1)+(b_{m+1}-b_m).
$$

The $a_m$ terms and the $b_m$ terms cancel, yielding

$$
a_1-a_{m+1}\ge b_{m+1}-b_1,
$$

which is $P(m+1)$. The tactic `linarith` performs precisely this linear-arithmetic cancellation and proves the induction step.

Applying `Nat.le_induction` to $k$ and the hypothesis $hk:1\le k$ then gives $P(k)$, that is,

$$
a_1-a_k\ge b_k-b_1.
$$

This is the fact `htelescope`.

Next the proof records
```lean
have hpos_bk : 0 < b k := hpos_b k
```
This is just the assumed positivity of the sequence $b$ specialized to the index $k$:

$$
b_k>0.
$$

Finally, `linarith` closes the goal $a_k\le c$. The inequalities available are:

$$
a_1-a_k\ge b_k-b_1,
$$

which is equivalent to

$$
a_k+b_k\le a_1+b_1,
$$

and

$$
a_1+b_1\le c.
$$

Combining them gives

$$
a_k+b_k\le c.
$$

Since $b_k>0$, we have

$$
a_k<a_k+b_k\le c,
$$

so in particular $a_k\le c$. The tactic `linarith` combines these linear facts and produces exactly the desired conclusion.

