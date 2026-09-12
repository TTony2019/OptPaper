## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_2.lean`

## Lean statement
```lean
theorem lemma7 (p : ℕ → ℝ) (ω K : ℝ)
    (hp : ∀ k, 0 ≤ p k) (hω : ω < 1)
    (hrec : ∃ k₀, ∀ k ≥ k₀, p k - ω * p (k - 1) ≤ K) :
    Bornology.IsBounded (Set.range p)
```

## Statement explanation
The declaration `lemma7` concerns a real sequence $p=(p_k)_{k\in\mathbb N}$, together with real parameters $\omega$ and $K$. The hypotheses are:

- $p_k\ge 0$ for every $k\in\mathbb N$;
- $\omega\lt 1$;
- there exists some $k_0\in\mathbb N$ such that for every natural number $k$ with $k_0\le k$,

```math
p_k-\omega\,p_{k-1}\le K,
```

  where $k-1$ is Lean's truncated subtraction on $\mathbb N$.

The conclusion is that the set of values

```math
\{p_k : k\in\mathbb N\}
```

is bounded in $\mathbb R$, formalized as `Bornology.IsBounded (Set.range p)`.

Mathematically, the theorem says that an eventually valid scalar recurrence of the form $p_k\le K+\omega p_{k-1}$, with nonnegative $p_k$ and with coefficient $\omega\lt 1$, forces the whole sequence $p$ to be uniformly bounded. When $\omega\le 0$, the recurrence immediately gives an upper bound on the tail. When $0\lt \omega\lt 1$, the recurrence is a contraction-type inequality, and the proof constructs a barrier $C$ such that the whole tail from $k_0$ onward stays below $C$, then combines this with the finite initial segment. Nonnegativity supplies the lower bound.

## Lean proof
```lean
by
  rcases hrec with ⟨k₀, hrec0⟩
  let S : ℝ := ∑ i ∈ Finset.range k₀, p i
  have hprefix : ∀ k, k < k₀ → p k ≤ S := by
    intro k hk
    simpa [S] using prefix_le_sum p hp hk
  by_cases hωnonpos : ω ≤ 0
  · let U : ℝ := max S K
    apply bounded_of_nonneg_upper p hp (U := U)
    intro k
    by_cases hk : k₀ ≤ k
    · have hmul : ω * p (k - 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hωnonpos (hp _)
      have htail : p k ≤ K := by
        have := (sub_le_iff_le_add.mp (hrec0 k hk))
        nlinarith
      exact htail.trans (by simp [U])
    · have hpre : p k ≤ S := hprefix k (by omega)
      exact hpre.trans (by simp [U])
  · have hωpos : 0 < ω := lt_of_not_ge hωnonpos
    have hden : 0 < 1 - ω := by nlinarith
    let C : ℝ := max (p k₀) (max K 0 / (1 - ω))
    have hCnonneg : 0 ≤ C := by
      apply le_trans (hp k₀)
      simp [C]
    have hC_K : K ≤ (1 - ω) * C := by
      have hdiv : max K 0 / (1 - ω) ≤ C := by
        simp [C]
      have hmax : max K 0 ≤ C * (1 - ω) := (div_le_iff₀ hden).mp hdiv
      nlinarith [le_max_left K 0]
    have hbarrier : ω * C + K ≤ C := by
      nlinarith
    have htail : ∀ n : ℕ, p (k₀ + n) ≤ C := by
      intro n
      induction n with
      | zero =>
          simp [C]
      | succ n ihn =>
          have hk : k₀ ≤ k₀ + n + 1 := by omega
          have hstep := sub_le_iff_le_add.mp (hrec0 (k₀ + n + 1) hk)
          have hmul : ω * p (k₀ + n) ≤ ω * C :=
            mul_le_mul_of_nonneg_left ihn (le_of_lt hωpos)
          norm_num [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hstep
          have hnext : p (k₀ + n + 1) ≤ C := by
            calc
              p (k₀ + n + 1) ≤ K + ω * p (k₀ + n) := hstep
              _ ≤ K + ω * C := add_le_add_right hmul K
              _ = ω * C + K := add_comm _ _
              _ ≤ C := hbarrier
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext
    let U : ℝ := max S C
    apply bounded_of_nonneg_upper p hp (U := U)
    intro k
    by_cases hk : k₀ ≤ k
    · have htail' : p k ≤ C := by
        rw [← Nat.add_sub_of_le hk]
        exact htail (k - k₀)
      exact htail'.trans (by simp [U])
    · have hpre : p k ≤ S := hprefix k (by omega)
      exact hpre.trans (by simp [U])
```

## Proof explanation
The proof first unpacks the eventual recurrence. The command `rcases hrec with ⟨k₀, hrec0⟩` replaces the existential hypothesis by a fixed threshold $k_0$ and the statement `hrec0`, namely

```math
\forall k,\quad k_0\le k \implies p_k-\omega\,p_{k-1}\le K.
```

It then defines

$$
S=\sum_{i=0}^{k_0-1} p_i,
$$

the sum of the initial block of the sequence.

The auxiliary fact `prefix_le_sum` says that if $0\le p_i$ for every $i$, and $k\lt k_0$, then

$$
p_k\le \sum_{i=0}^{k_0-1} p_i.
$$

The proof specializes this to the given sequence $p$, using `hp` for nonnegativity and the hypothesis $k\lt k_0$, and obtains

$$
hprefix:\quad \forall k,\ k<k_0 \implies p_k\le S.
$$

This controls all terms before the threshold $k_0$.

The proof now splits into two cases according to the sign of $\omega$.

In the first case, `hωnonpos : ω ≤ 0`. The proof sets

$$
U=\max(S,K).
$$

It then applies the lemma `bounded_of_nonneg_upper`. That lemma states that if $p$ is a sequence with $0\le p_k$ for all $k$, and if there exists a real number $U$ such that $p_k\le U$ for all $k$, then the range of $p$ is bounded. Thus, after applying it, it remains to prove

$$
\forall k,\quad p_k\le U.
$$

The command `intro k` fixes an arbitrary index $k$.

If $k_0\le k$, the recurrence `hrec0 k hk` gives

```math
p_k-\omega\,p_{k-1}\le K.
```

Using `sub_le_iff_le_add.mp`, this is converted into

```math
p_k\le K+\omega\,p_{k-1}.
```

Since $\omega\le 0$ and $p_{k-1}\ge 0$, the lemma `mul_nonpos_of_nonpos_of_nonneg` gives

```math
\omega\,p_{k-1}\le 0.
```

Hence $`K+\omega\,p_{k-1}\le K`$, so `nlinarith` derives

$$
p_k\le K.
$$

Because $U=\max(S,K)$, we have $K\le U$, so $p_k\le U$.

If instead $k\lt k_0$, then `omega` converts the failure of $k_0\le k$ into $k\lt k_0$. The earlier prefix bound gives $p_k\le S$, and since $S\le U=\max(S,K)$, we again get $p_k\le U$. Thus the upper bound $U$ works for every $k$, and `bounded_of_nonneg_upper` finishes the first case.

In the second case, the hypothesis `hωnonpos : ω ≤ 0` fails. The command `lt_of_not_ge hωnonpos` gives

$$
0<\omega.
$$

Together with $\omega\lt 1$, this implies

$$
1-\omega>0,
$$

proved by `nlinarith` as `hden`.

The proof defines the barrier

```math
C=\max\!\left(p_{k_0},\ \frac{\max(K,0)}{1-\omega}\right).
```

It first records `hCnonneg : 0 ≤ C`. Indeed, since $0\le p_{k_0}$ and $C$ is a maximum containing $p_{k_0}$, we have $p_{k_0}\le C$, hence $0\le C$.

Next the proof establishes `hC_K`, namely

$$
K\le (1-\omega)C.
$$

Since $C$ is at least $\max(K,0)/(1-\omega)$, we have

$$
\frac{\max(K,0)}{1-\omega}\le C.
$$

Because $1-\omega\gt 0$, the lemma `div_le_iff₀` allows multiplying through by the positive denominator:

$$
\max(K,0)\le C(1-\omega).
$$

Since $K\le \max(K,0)$ by `le_max_left`, `nlinarith` concludes

$$
K\le (1-\omega)C.
$$

From this, the proof derives the barrier inequality

$$
\omega C+K\le C.
$$

Indeed, $K\le (1-\omega)C=C-\omega C$, and adding $\omega C$ to both sides gives $\omega C+K\le C$. This is `hbarrier`, proved by `nlinarith`.

The proof now shows by induction that the entire tail from $k_0$ stays below $C$:

$$
\forall n\in\mathbb N,\quad p_{k_0+n}\le C.
$$

For $n=0$, this is $p_{k_0}\le C$, immediate from the definition of $C$ as a maximum. For the induction step, assume $p_{k_0+n}\le C$. The recurrence at index $k_0+n+1$, which satisfies $k_0\le k_0+n+1$ by `omega`, gives

```math
p_{k_0+n+1}-\omega\,p_{k_0+n}\le K.
```

Using `sub_le_iff_le_add.mp`, this becomes

```math
p_{k_0+n+1}\le K+\omega\,p_{k_0+n}.
```

The command `norm_num` with `Nat.add_sub_cancel` and `Nat.succ_eq_add_one` simplifies $(k_0+n+1)-1$ to $k_0+n$. Since $\omega\gt 0$, the induction hypothesis $p_{k_0+n}\le C$ can be multiplied by $\omega$ via `mul_le_mul_of_nonneg_left`, giving

```math
\omega\,p_{k_0+n}\le \omega C.
```

Therefore

```math
p_{k_0+n+1}\le K+\omega\,p_{k_0+n}\le K+\omega C=\omega C+K\le C,
```

using `add_le_add_right`, `add_comm`, and the barrier inequality. The command `simpa` rewrites $k_0+n+1$ as $k_0+(n+1)$, completing the induction.

Finally, the proof sets

$$
U=\max(S,C)
$$

and again applies `bounded_of_nonneg_upper`. It remains to prove $p_k\le U$ for arbitrary $k$. If $k_0\le k$, then `Nat.add_sub_of_le` rewrites $k$ as $k_0+(k-k_0)$. The tail bound gives

$$
p_k=p_{k_0+(k-k_0)}\le C\le U.
$$

If $k_0\le k$ fails, then `omega` gives $k\lt k_0$, and the prefix bound gives

$$
p_k\le S\le U.
$$

Thus $p_k\le U$ for every $k$. Since `hp` already gives $0\le p_k$ for every $k$, the lemma `bounded_of_nonneg_upper` yields

$$
\mathrm{Bornology.IsBounded}(\mathrm{Set.range} p),
$$

which is exactly the desired boundedness of the sequence $p$.

