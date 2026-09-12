## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_lem_2.lean`

## Lean statement
```lean
theorem alvarez_sequence_convergence
    (psi delta alphaSeq : ℕ → ℝ)
    (hpsi_nonneg : ∀ n, 0 ≤ psi n)
    (hdelta_nonneg : ∀ n, 0 ≤ delta n)
    (halpha_nonneg : ∀ n, 0 ≤ alphaSeq n)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      psi (n + 1) ≤ psi n + alphaSeq n * (psi n - psi (n - 1)) + delta n)
    (hsum_delta : Summable delta)
    (alpha : ℝ)
    (halpha_bound : ∀ n : ℕ, 1 ≤ n → alphaSeq n ≤ alpha)
    (halpha_lt : alpha < 1) :
    Summable (fun n : ℕ => max (psi (n + 2) - psi (n + 1)) 0) ∧
      ∃ psiStar : ℝ, 0 ≤ psiStar ∧ Tendsto psi atTop (nhds psiStar)
```

## Statement explanation
The theorem `alvarez_sequence_convergence` concerns three real sequences indexed by the natural numbers. Write $a_n=\mathrm{alphaSeq}_n$, $\delta_n$, and $\psi_n$. The hypotheses are:

- $\psi_n\ge 0$ for every $n$;
- $\delta_n\ge 0$ for every $n$;
- $a_n\ge 0$ for every $n$;
- for every $n\ge 1$,

  $$
  \psi_{n+1}\le \psi_n+a_n(\psi_n-\psi_{n-1})+\delta_n;
  $$

- the series $\sum_n\delta_n$ is summable;
- there is a real number $\alpha$ such that $a_n\le \alpha$ for every $n\ge 1$;
- $\alpha<1$.

The recurrence is a second-order difference inequality. Equivalently, if $d_n=\psi_{n+1}-\psi_n$, then for $n\ge 1$,

$$
d_n\le a_n d_{n-1}+\delta_n.
$$

Thus each increment is controlled by the previous increment with coefficient $a_n$, plus a nonnegative summable forcing term $\delta_n$. Since $a_n$ is bounded above by $\alpha<1$, the recurrence is dissipative. The conclusion is twofold:

$$
\sum_n \max(\psi_{n+2}-\psi_{n+1},0)
$$

is summable, and there exists a real number $\psi^\star$ such that

$$
0\le \psi^\star
\quad\text{and}\quad
\psi_n\to \psi^\star \quad\text{as }n\to\infty.
$$

In words, the total upward movement of $\psi$, measured by the positive parts of its increments, is finite, and the nonnegative sequence $\psi_n$ converges to a nonnegative limit.

## Lean proof
```lean
by
  let d : ℕ → ℝ := fun n => psi (n + 1) - psi n
  let q : ℕ → ℝ := fun n => max (d n) 0
  let σ : ℕ → ℝ := fun n => delta (n + 1)
  have halpha_nonneg' : 0 ≤ alpha :=
    le_trans (halpha_nonneg 1) (halpha_bound 1 (by omega))
  have hσ_nonneg : ∀ n, 0 ≤ σ n := by
    intro n; exact hdelta_nonneg (n + 1)
  have hσ_sum : Summable σ := by
    simpa [σ] using (summable_nat_add_iff 1).mpr hsum_delta
  have hq_nonneg : ∀ n, 0 ≤ q n := by
    intro n; exact le_max_right _ _
  have hq_rec : ∀ n, q (n + 1) ≤ alpha * q n + σ n := by
    intro n
    have hr := hrec (n + 1) (by omega)
    have hd : d (n + 1) ≤ alphaSeq (n + 1) * d n + σ n := by
      dsimp [d, σ]
      simpa [add_assoc, add_left_comm, add_comm] using hr
    have hmul : alphaSeq (n + 1) * d n ≤ alpha * q n := by
      dsimp [q]
      by_cases hdn : 0 ≤ d n
      · rw [max_eq_left hdn]
        exact mul_le_mul_of_nonneg_right (halpha_bound (n + 1) (by omega)) hdn
      · have hdneg : d n ≤ 0 := le_of_not_ge hdn
        rw [max_eq_right (le_of_not_ge hdn)]
        have ha0 : 0 ≤ alphaSeq (n + 1) := halpha_nonneg _
        nlinarith
    have hdl : d (n + 1) ≤ alpha * q n + σ n := by linarith
    dsimp [q]
    by_cases hp : 0 ≤ d (n + 1)
    · rw [max_eq_left hp]
      exact hdl
    · rw [max_eq_right (le_of_not_ge hp)]
      exact add_nonneg (mul_nonneg halpha_nonneg' (hq_nonneg n)) (hσ_nonneg n)
  have hq_sum : Summable q := by
    let D : ℝ := q 0 + ∑' n, σ n
    have hD : 0 ≤ D := add_nonneg (hq_nonneg 0) (tsum_nonneg hσ_nonneg)
    have hpartial_sigma : ∀ N, (Finset.range N).sum σ ≤ ∑' n, σ n := by
      intro N
      exact hσ_sum.sum_le_tsum _ (fun i _ => hσ_nonneg i)
    have hsum_rec : ∀ N, (Finset.range (N + 1)).sum q ≤
        alpha * (Finset.range N).sum q + D := by
      intro N
      rw [show (Finset.range (N + 1)).sum q = q 0 + (Finset.range N).sum (fun k => q (k + 1)) by
        simpa [add_comm] using (Finset.sum_range_succ' q N)]
      have hrec_sum : (Finset.range N).sum (fun k => q (k + 1)) ≤
          (Finset.range N).sum (fun k => alpha * q k + σ k) := by
        exact Finset.sum_le_sum (fun k hk => hq_rec k)
      have hsplit : (Finset.range N).sum (fun k => alpha * q k + σ k) =
          alpha * (Finset.range N).sum q + (Finset.range N).sum σ := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      rw [hsplit] at hrec_sum
      dsimp [D]
      linarith [hpartial_sigma N]
    have hbound : ∀ N, (Finset.range N).sum q ≤ D / (1 - alpha) := by
      intro N
      have hden : 0 < 1 - alpha := by linarith
      induction N with
      | zero => exact div_nonneg hD hden.le
      | succ N ih =>
          have hs := hsum_rec N
          have hmul := mul_le_mul_of_nonneg_left ih halpha_nonneg'
          have heq : alpha * (D / (1 - alpha)) + D = D / (1 - alpha) := by
            field_simp [ne_of_gt hden]
            ring
          calc
            (Finset.range (N + 1)).sum q ≤ alpha * (Finset.range N).sum q + D := hs
            _ ≤ alpha * (D / (1 - alpha)) + D := by linarith
            _ = D / (1 - alpha) := heq
    exact summable_of_sum_range_le hq_nonneg hbound
  have hpos : Summable (fun n : ℕ => max (psi (n + 2) - psi (n + 1)) 0) := by
    simpa [q, d] using (summable_nat_add_iff 1).mpr hq_sum
  let p : ℕ → ℝ := fun n => max (psi (n + 1) - psi n) 0
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, p i
  let u : ℕ → ℝ := fun n => psi n - S n
  have hp_nonneg : ∀ n, 0 ≤ p n := by intro n; exact le_max_right _ _
  have hu_anti : Antitone u := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [u, S]
    rw [Finset.sum_range_succ]
    have hi : psi (n + 1) - psi n ≤ p n := le_max_left _ _
    linarith
  have hS_le : ∀ n, S n ≤ ∑' i, p i := by
    intro n
    have hp_sum : Summable p := by
      simpa [p] using hq_sum
    exact hp_sum.sum_le_tsum _ (fun i _ => hp_nonneg i)
  have hu_bdd : BddBelow (Set.range u) := by
    refine ⟨-(∑' i, p i), ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp [u]
    linarith [hpsi_nonneg n, hS_le n]
  have hu_lim : Tendsto u atTop (nhds (⨅ n, u n)) := tendsto_atTop_ciInf hu_anti hu_bdd
  have hS_lim : Tendsto S atTop (nhds (∑' i, p i)) := by
    have hp_sum : Summable p := by
      simpa [p] using hq_sum
    simpa [S] using hp_sum.hasSum.tendsto_sum_nat
  obtain ⟨l, hl⟩ : ∃ l : ℝ, Tendsto psi atTop (nhds l) := by
    refine ⟨(⨅ n, u n) + ∑' i, p i, ?_⟩
    have hsum := hu_lim.add hS_lim
    convert hsum using 1 <;> simp [u, S, sub_add_cancel]
  refine ⟨hpos, l, ?_, hl⟩
  exact ge_of_tendsto hl (Filter.Eventually.of_forall hpsi_nonneg)
```

## Proof explanation
The proof begins by introducing abbreviations. Let

$$
d_n=\psi_{n+1}-\psi_n,\qquad
q_n=\max(d_n,0),\qquad
\sigma_n=\delta_{n+1}.
$$

Here $q_n$ is the positive part of the increment $d_n$, and $\sigma$ is just $\delta$ shifted by one index.

First, the proof derives $0\le\alpha$. Since $0\le a_1$ and $a_1\le\alpha$, transitivity gives $0\le\alpha$. This is used later to know that multiplication by $\alpha$ preserves nonnegativity.

Next, $\sigma$ is nonnegative because $\sigma_n=\delta_{n+1}$ and every $\delta_k\ge0$. Also $\sigma$ is summable: shifting a summable sequence by one index preserves summability. This is the content of `summable_nat_add_iff 1`, applied to $\delta$, giving summability of $n\mapsto\delta_{n+1}$.

The sequence $q$ is nonnegative because $q_n=\max(d_n,0)\ge0$. The central recurrence for $q$ is then proved:

$$
q_{n+1}\le \alpha q_n+\sigma_n.
$$

To obtain it, the original recurrence is applied with index $n+1$, which is allowed since $1\le n+1$. It gives

$$
\psi_{n+2}\le \psi_{n+1}+a_{n+1}(\psi_{n+1}-\psi_n)+\delta_{n+1}.
$$

Subtracting $\psi_{n+1}$ yields

$$
d_{n+1}\le a_{n+1}d_n+\sigma_n.
$$

The proof now compares $a_{n+1}d_n$ with $\alpha q_n$. If $d_n\ge0$, then $q_n=d_n$, and multiplying $a_{n+1}\le\alpha$ by the nonnegative number $d_n$ gives

$$
a_{n+1}d_n\le \alpha d_n=\alpha q_n.
$$

If $d_n<0$, then $q_n=0$, so $\alpha q_n=0$, while $a_{n+1}\ge0$ and $d_n\le0$ imply

$$
a_{n+1}d_n\le0=\alpha q_n.
$$

Thus in all cases

$$
d_{n+1}\le \alpha q_n+\sigma_n.
$$

Finally, passing from $d_{n+1}$ to its positive part $q_{n+1}$, the same inequality holds: if $d_{n+1}\ge0$, then $q_{n+1}=d_{n+1}$; if $d_{n+1}<0$, then $q_{n+1}=0$, and the right-hand side $\alpha q_n+\sigma_n$ is nonnegative because $\alpha\ge0$, $q_n\ge0$, and $\sigma_n\ge0$. Hence

$$
q_{n+1}\le \alpha q_n+\sigma_n.
$$

The proof then shows that $q$ is summable. Define

$$
D=q_0+\sum_{n=0}^\infty \sigma_n.
$$

Since $q_0\ge0$ and $\sigma_n\ge0$, one has $D\ge0$. For every $N$, the finite partial sum of $\sigma$ up to $N-1$ is at most the total sum $\sum_n\sigma_n$, because the series is summable with nonnegative terms.

Let

$$
Q_N=\sum_{k=0}^{N-1} q_k.
$$

Using the recurrence $q_{k+1}\le \alpha q_k+\sigma_k$, summing over $k=0,\dots,N-1$, and splitting the sum, one obtains

$$
Q_{N+1}\le \alpha Q_N+D.
$$

Here the term $q_0$ and the tail bound for $\sum\sigma_k$ combine into $D$. Since $0\le\alpha<1$, the denominator $1-\alpha$ is positive. An induction on $N$ then gives

$$
Q_N\le \frac{D}{1-\alpha}
$$

for every $N$. Indeed, the base case is trivial because $Q_0=0\le D/(1-\alpha)$, and the induction step uses

$$
Q_{N+1}\le \alpha Q_N+D
\le \alpha\frac{D}{1-\alpha}+D
=\frac{D}{1-\alpha}.
$$

The last equality is the algebraic identity

$$
\alpha\frac{D}{1-\alpha}+D=\frac{D}{1-\alpha},
$$

valid because $\alpha<1$. Since $q_n\ge0$ for all $n$ and all partial sums are uniformly bounded, the lemma `summable_of_sum_range_le` yields that $q$ is summable. Therefore $q$ represents a convergent nonnegative series.

The first conclusion follows by shifting $q$. Since $q_{n+1}=\max(\psi_{n+2}-\psi_{n+1},0)$, the summability of $q$ implies the summability of

$$
n\mapsto \max(\psi_{n+2}-\psi_{n+1},0),
$$

again using that shifting a summable sequence by one preserves summability.

To prove convergence of $\psi$, the proof defines

$$
p_n=\max(\psi_{n+1}-\psi_n,0),
\qquad
S_n=\sum_{i=0}^{n-1} p_i,
\qquad
u_n=\psi_n-S_n.
$$

Here $p=q$, so $p$ is nonnegative and summable. The sequence $S_n$ is the partial sum sequence of $p$.

The sequence $u$ is shown to be antitone. Indeed,

$$
u_{n+1}=\psi_{n+1}-S_{n+1}
=\psi_{n+1}-(S_n+p_n),
$$

so

$$
u_{n+1}-u_n
=(\psi_{n+1}-\psi_n)-p_n
=d_n-p_n.
$$

But $p_n=\max(d_n,0)\ge d_n$, hence $u_{n+1}-u_n\le0$. Thus $u_{n+1}\le u_n$ for every $n$, so $u$ is decreasing.

The sequence $u$ is also bounded below. Since $p$ is summable with nonnegative terms, every partial sum $S_n$ satisfies

$$
S_n\le \sum_{i=0}^\infty p_i.
$$

Therefore

$$
u_n=\psi_n-S_n\ge -\sum_{i=0}^\infty p_i,
$$

because $\psi_n\ge0$. Hence $u$ is bounded below. For a decreasing real sequence that is bounded below, the sequence converges to its infimum. This is the content of `tendsto_atTop_ciInf`, which gives

$$
u_n\to \inf_n u_n.
$$

Meanwhile, since $p$ is summable, its partial sums converge to its total sum:

$$
S_n=\sum_{i=0}^{n-1}p_i\to \sum_{i=0}^\infty p_i.
$$

Now

$$
\psi_n=u_n+S_n.
$$

Therefore, by adding the two limits,

$$
\psi_n\to \inf_n u_n+\sum_{i=0}^\infty p_i.
$$

The proof takes this value as the desired limit $l$. It remains only to show $0\le l$. Since every $\psi_n\ge0$, the sequence $\psi$ is eventually nonnegative, and a limit of a sequence that is eventually nonnegative is nonnegative. This is the role of `ge_of_tendsto` applied to the convergence $\psi_n\to l$ and the hypothesis $\psi_n\ge0$ for all $n$.

Thus the proof constructs the nonnegative limit $l$, proves the required summability of the positive parts of the shifted increments, and concludes both parts of the theorem.

