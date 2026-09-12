## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/lem_3.lean`

## Lean statement
```lean
theorem lemma13 (p ε : ℕ → ℝ) (η : ℝ) (k₀ : ℕ)
    (hη : 0 < η ∧ η < 1)
    (hε : Filter.limsup ε Filter.atTop ≤ 0)
    (hε_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop ε)
    (hrec : ∀ k ≥ k₀, p (k + 1) ≤ η * p k + ε k) :
    Filter.limsup p Filter.atTop ≤ 0
```

## Statement explanation
The declaration `lemma13` concerns two real sequences $p:\mathbb N\to\mathbb R$ and $\varepsilon:\mathbb N\to\mathbb R$, a real number $\eta$, and a natural number $k_0$. Its hypotheses are:

- $0<\eta<1$, so $\eta$ is a contraction factor strictly between $0$ and $1$.
- $\displaystyle \limsup_{k\to\infty}\varepsilon(k)\le 0$.
- $\varepsilon$ is eventually bounded above: there exists some real $M$ such that $\varepsilon(k)\le M$ for all sufficiently large $k$. In Lean this is expressed by `Filter.IsBoundedUnder (· ≤ ·) Filter.atTop ε`.
- For every $k\ge k_0$,

  $$
  p(k+1)\le \eta p(k)+\varepsilon(k).
  $$

The conclusion is

$$
\limsup_{k\to\infty} p(k)\le 0.
$$

Mathematically, the theorem says that a sequence $p$ satisfying an eventually valid perturbed contraction inequality, where the perturbation sequence $\varepsilon$ has nonpositive limit superior and is eventually bounded above, must itself have nonpositive limit superior. The conclusion is not that $p$ converges, only that its upper limiting behavior is at most $0$.

## Lean proof
```lean
by
  rcases hη with ⟨hη_pos, hη_lt_one⟩
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hgap_pos : 0 < 1 - η := sub_pos.mpr hη_lt_one
  have hgap_ne : 1 - η ≠ 0 := ne_of_gt hgap_pos
  apply limsup_le_zero_of_eventually_lt_pos p
  intro y hy
  let q : ℝ := y * (1 - η) / 2
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hε_eventual : ∀ᶠ k in Filter.atTop, ε k ≤ q := by
    filter_upwards [Filter.eventually_lt_add_pos_of_limsup_le
      (u := ε) hε_bdd hε hq_pos] with k hk
    simpa using hk.le
  obtain ⟨Kε, hε_tail⟩ := Filter.eventually_atTop.1 hε_eventual
  let N : ℕ := max k₀ Kε
  have hrecq : ∀ k ≥ N, p (k + 1) ≤ η * p k + q := by
    intro k hk
    have hk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
    have hkε : Kε ≤ k := le_trans (le_max_right _ _) hk
    calc
      p (k + 1) ≤ η * p k + ε k := hrec k hk₀
      _ ≤ η * p k + q := by linarith [hε_tail k hkε]
  have hq_div_lt_y : q / (1 - η) < y := by
    have hq_div_eq : q / (1 - η) = y / 2 := by
      dsimp [q]
      field_simp [hgap_ne]
    rw [hq_div_eq]
    linarith
  exact eventually_lt_of_contract_recurrence p η q N hη_nonneg hη_lt_one hq_pos hrecq y hq_div_lt_y
```

## Proof explanation
The proof begins by splitting the hypothesis $0<\eta\land \eta<1$ via `rcases hη with ⟨hη_pos, hη_lt_one⟩`. Thus we obtain $0<\eta$ and $\eta<1$. From $0<\eta$, the proof records $0\le \eta$ using `hη_pos.le`; this nonnegativity is later required by the contraction recurrence lemma. From $\eta<1$, it records

$$
0<1-\eta
$$

using `sub_pos.mpr hη_lt_one`. It also records $1-\eta\ne 0$ using `ne_of_gt`, since a positive real number is nonzero. This nonzero condition is needed for later division by $1-\eta$.

Next the proof applies the cited lemma `limsup_le_zero_of_eventually_lt_pos` to the sequence $p$. That lemma states that if for every positive real $y$ one has eventually

$$
p(n)<y,
$$

then

$$
\limsup p\le 0.
$$

So the goal is reduced to proving

$$
\forall y>0,\ \text{eventually } p(n)<y.
$$

Accordingly, the proof introduces an arbitrary real $y$ together with the hypothesis $0<y$ by `intro y hy`. It then defines the auxiliary quantity

$$
q=\frac{y(1-\eta)}2.
$$

Because $y>0$ and $1-\eta>0$, we have $q>0$. The proof checks this using `positivity`, after unfolding the local definition of $q$ with `dsimp [q]`.

The next step derives an eventual upper bound for $\varepsilon$. The invocation of `Filter.eventually_lt_add_pos_of_limsup_le` uses the eventual boundedness hypothesis `hε_bdd`, the hypothesis $\limsup \varepsilon\le 0$, and the positivity of $q$. In this context it provides the eventual strict inequality

$$
\varepsilon(k)<0+q=q.
$$

The tactic `filter_upwards` turns this into the desired eventual statement, and `simpa using hk.le` converts the strict inequality $\varepsilon(k)<q$ into $\varepsilon(k)\le q$. Thus the proof has established

$$
\text{eventually } \varepsilon(k)\le q.
$$

Using `Filter.eventually_atTop.1`, the proof converts this eventual statement into a tail statement: there exists a natural number $K_\varepsilon$ such that for all $k\ge K_\varepsilon$,

$$
\varepsilon(k)\le q.
$$

The proof then sets

$$
N=\max(k_0,K_\varepsilon).
$$

For every $k\ge N$, both $k\ge k_0$ and $k\ge K_\varepsilon$ hold. The first inequality is obtained from $k_0\le \max(k_0,K_\varepsilon)$ via `le_max_left`, and the second from $K_\varepsilon\le \max(k_0,K_\varepsilon)$ via `le_max_right`.

Now the proof proves the modified recurrence

$$
p(k+1)\le \eta p(k)+q
$$

for all $k\ge N$. For such a $k$, the original recurrence gives

$$
p(k+1)\le \eta p(k)+\varepsilon(k),
$$

because $k\ge k_0$. Also, from the tail bound on $\varepsilon$, we have $\varepsilon(k)\le q$. Therefore

$$
\eta p(k)+\varepsilon(k)\le \eta p(k)+q.
$$

The proof records this chain with `calc`, and the final comparison is discharged by `linarith`, which uses the inequality $\varepsilon(k)\le q$.

It remains to check that the threshold $q/(1-\eta)$ is strictly below $y$. The proof computes

$$
\frac{q}{1-\eta}
=\frac{y(1-\eta)/2}{1-\eta}
=\frac y2.
$$

This is done by unfolding $q$ with `dsimp [q]` and clearing the denominator with `field_simp`, using the previously established fact that $1-\eta\ne 0$. Since $0<y$, we have $y/2<y$. The proof rewrites $q/(1-\eta)$ to $y/2$ using `rw`, and then `linarith` proves

$$
\frac{q}{1-\eta}<y.
$$

Finally, the proof applies the cited theorem `eventually_lt_of_contract_recurrence`. Its content is exactly the following: if $p$ is a real sequence, $0\le \eta$, $\eta<1$, $q>0$, and for all $k\ge N$,

$$
p(k+1)\le \eta p(k)+q,
$$

then for every real $r$ satisfying

$$
\frac{q}{1-\eta}<r,
$$

one has eventually

$$
p(n)<r.
$$

Here this is specialized to the same sequence $p$, the same $\eta$, the auxiliary $q$, the threshold $N$, and the value $r=y$. The hypotheses supplied are $0\le\eta$, $\eta<1$, $q>0$, the modified recurrence, and $q/(1-\eta)<y$. The conclusion is exactly the remaining goal:

$$
\text{eventually } p(n)<y.
$$

Since $y>0$ was arbitrary, this proves the premise required by `limsup_le_zero_of_eventually_lt_pos`, and therefore the desired conclusion

$$
\limsup_{k\to\infty}p(k)\le 0
$$

follows.

