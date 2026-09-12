## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_1.lean`

## Lean statement
```lean
theorem lemma5 (a b ε : ℕ → ℝ) (θ : ℝ) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hε : Summable fun k ↦ ‖ε k‖)
    (ha : ∀ k ≥ k₀, a k - a (k - 1) ≤ θ + ε k)
    (hb : ∀ k ≥ k₀, b (k + 1) - b k ≤ a k)
    (hnonneg : ∀ k ≥ k₀, 0 ≤ b k) : θ ≥ 0
```

## Statement explanation
The declaration `lemma5` is a theorem about three real sequences $a,b,\varepsilon:\mathbb N\to\mathbb R$, a real number $\theta$, and a natural number $k_0$. It assumes $1\le k_0$, so that expressions such as $k-1$ for $k\ge k_0$ correspond to the usual predecessor index. It assumes that the series of norms $\sum_k \|\varepsilon_k\|$ is summable; since the values are real, this means $\sum_k |\varepsilon_k|$ is convergent or summable in the usual sense. It assumes the first recurrence

$$
a_k-a_{k-1}\le \theta+\varepsilon_k
\qquad\text{for all }k\ge k_0,
$$

the second recurrence

$$
b_{k+1}-b_k\le a_k
\qquad\text{for all }k\ge k_0,
$$

and the nonnegativity condition

$$
0\le b_k
\qquad\text{for all }k\ge k_0.
$$

The conclusion is

$$
\theta\ge 0.
$$

Thus the theorem says that if $a$ satisfies a first-order recurrence with asymptotic drift $\theta$ and summable errors, and if another nonnegative sequence $b$ has forward differences bounded above by $a$, then the drift $\theta$ cannot be negative. Equivalently, a negative $\theta$ would force $a$ to become eventually very negative, which would force $b$ to decrease at a linear rate and eventually become negative, contradicting the nonnegativity of $b$.

## Lean proof
```lean
by
  rcases linear_bound_of_first_recurrence a ε θ k₀ hk₀ hε ha with ⟨A, hA⟩
  by_contra hnot
  have hθ : θ < 0 := lt_of_not_ge hnot
  let c : ℝ := -θ / 2
  have hc : 0 < c := by dsimp [c]; nlinarith
  rcases exists_nat_gt (A / c) with ⟨N₀, hN₀⟩
  let N : ℕ := max k₀ (max 1 N₀)
  have hkN : k₀ ≤ N := le_max_left _ _
  have h1N : 1 ≤ N := le_trans (le_max_left 1 N₀) (le_max_right k₀ _)
  have hN₀N : N₀ ≤ N := le_trans (le_max_right 1 N₀) (le_max_right k₀ _)
  have hNc : A < (N : ℝ) * c := by
    apply (div_lt_iff₀ hc).mp
    exact lt_of_lt_of_le hN₀ (by exact_mod_cast hN₀N)
  have hθc : θ = -2 * c := by dsimp [c]; ring
  have ha_neg : ∀ k ≥ N, a k ≤ -c := by
    intro k hk
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hA' := hA k (le_trans hkN hk)
    rw [hθc] at hA'
    have h1Nr : (1 : ℝ) ≤ N := by exact_mod_cast h1N
    nlinarith [mul_nonneg (sub_nonneg.mpr hNk) hc.le,
      mul_nonneg (sub_nonneg.mpr h1Nr) hc.le]
  rcases exists_nat_gt (b N / c) with ⟨L, hL⟩
  have hLc : b N < (L : ℝ) * c := (div_lt_iff₀ hc).mp hL
  have htail := b_tail_le_neg_mul a b k₀ N c hkN hb ha_neg L
  have hnn := hnonneg (N + L) (le_trans hkN (Nat.le_add_right N L))
  nlinarith
```

## Proof explanation
The proof first invokes `linear_bound_of_first_recurrence`. That cited result states that for sequences $a,\varepsilon:\mathbb N\to\mathbb R$, a real number $\theta$, and a natural number $k_0$ with $1\le k_0$, if $\sum_k \|\varepsilon_k\|$ is summable and if

$$
a_k-a_{k-1}\le \theta+\varepsilon_k
\qquad\text{for all }k\ge k_0,
$$

then there exists a real constant $A$ such that

$$
a_m\le m\theta+A
\qquad\text{for all }m\ge k_0.
$$

In the proof this is applied with the current $a,\varepsilon,\theta,k_0$, using the hypotheses `hε` and `ha`. The result is a pair $\langle A,hA\rangle$, where $hA$ is the assertion that for every $m\ge k_0$,

$$
a_m\le m\theta+A.
$$

Mathematically, this lemma converts the recurrence for $a$ into a global affine upper bound for $a_m$ with slope $\theta$.

The proof then argues by contradiction. It assumes the negation of the desired conclusion, so `hnot` is the statement that $\theta\ge0$ is false. The command `by_contra` introduces this contradictory assumption. From it, `lt_of_not_ge` gives

$$
\theta<0.
$$

The proof defines

$$
c=-\frac{\theta}{2}.
$$

Because $\theta<0$, one has $c>0$. The Lean proof verifies this with `dsimp [c]` to unfold the definition of $c$, followed by `nlinarith`.

Next the proof uses `exists_nat_gt (A/c)`, the Archimedean property, to choose a natural number $N_0$ such that

$$
\frac{A}{c}<N_0.
$$

It then defines

$$
N=\max(k_0,\max(1,N_0)).
$$

From the definition of $N$, the proof obtains

$$
k_0\le N,\qquad 1\le N,\qquad N_0\le N.
$$

These are proved using the basic properties of `max`: `le_max_left` says that the first argument of a maximum is at most the maximum, and `le_max_right` says that the second argument is at most the maximum. The inequalities are composed with `le_trans`. Since $N_0\le N$, the earlier inequality $A/c<N_0$ gives $A/c<N$. Because $c>0$, multiplying by $c$ preserves the inequality, so

$$
A<Nc.
$$

The proof obtains this using `(div_lt_iff₀ hc).mp`, which is the equivalence between $A/c<N$ and $A<Nc$ for positive $c$.

The proof also records that, by definition of $c$,

$$
\theta=-2c.
$$

This is proved by `dsimp [c]` and `ring`.

The next goal is to show that $a_k\le -c$ for every $k\ge N$. Fix such a $k$, introduced by `intro k hk`. Since $N\ge k_0$ and $k\ge N$, we have $k\ge k_0$, so the previously obtained affine bound applies:

$$
a_k\le k\theta+A.
$$

The proof rewrites $\theta$ as $-2c$, giving

$$
a_k\le -2kc+A.
$$

Using $A<Nc$, it follows that

$$
a_k< -2kc+Nc=-c(2k-N).
$$

Now $k\ge N\ge1$, so $2k-N\ge1$. Since $c>0$, this implies

$$
-c(2k-N)\le -c.
$$

Therefore

$$
a_k\le -c.
$$

This establishes `ha_neg`, the statement that for all $k\ge N$, $a_k\le -c$. The final inequality is discharged by `nlinarith`, using also the nonnegativity of $(k-N)c$ and $(N-1)c$, which encode $k\ge N$ and $N\ge1$.

The proof then uses `exists_nat_gt (b N / c)` again to choose a natural number $L$ such that

$$
\frac{b_N}{c}<L.
$$

Since $c>0$, this is equivalent to

$$
b_N<Lc,
$$

again by `(div_lt_iff₀ hc).mp`.

Now the cited result `b_tail_le_neg_mul` is applied. That result says that if $k_0\le N$, if

$$
b_{k+1}-b_k\le a_k
\qquad\text{for all }k\ge k_0,
$$

and if

$$
a_k\le -c
\qquad\text{for all }k\ge N,
$$

then for every natural number $L$,

$$
b_{N+L}-b_N\le -Lc.
$$

The mathematical content is a telescoping estimate: for $k=N,N+1,\dots,N+L-1$, each difference $b_{k+1}-b_k$ is bounded above by $a_k$, and each $a_k$ is at most $-c$. Summing these $L$ inequalities gives

$$
b_{N+L}-b_N\le -Lc.
$$

In the current proof, the hypotheses needed by this cited result are exactly $hkN$, the recurrence `hb`, and the just-established `ha_neg`. Hence the proof obtains

$$
b_{N+L}-b_N\le -Lc.
$$

Finally, the proof uses the nonnegativity hypothesis for $b$. Since $N\ge k_0$, we also have $N+L\ge k_0$. The command `Nat.le_add_right N L` gives $N\le N+L$, and combining this with $k_0\le N$ gives $k_0\le N+L$. Therefore `hnonneg` applies at the index $N+L$, yielding

$$
0\le b_{N+L}.
$$

Now the inequalities combine as follows:

$$
b_{N+L}\le b_N-Lc,
$$

and from $b_N<Lc$,

$$
b_N-Lc< Lc-Lc=0.
$$

Thus

$$
b_{N+L}<0,
$$

which contradicts $0\le b_{N+L}$. The final `nlinarith` closes this contradiction using the inequalities `htail`, `hLc`, and `hnn`. Since the assumption $\theta<0$ led to a contradiction, the original negation is false, and therefore

$$
\theta\ge0.
$$

