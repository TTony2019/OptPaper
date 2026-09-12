## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/lem_2.lean`

## Lean statement
```lean
lemma lemma_2_3
    (phi delta alphaSeq : ℕ → ℝ) (alphaBar : ℝ)
    (hphi_nonneg : ∀ k : ℕ, 0 ≤ phi k)
    (hdelta_nonneg : ∀ k : ℕ, 0 ≤ delta k)
    (hrec :
      ∀ k : ℕ,
        phi (k + 1) ≤
          phi k + alphaSeq k * (phi k - phi (k - 1)) + delta k)
    (hdelta_sum : Summable delta)
    (halpha : ∀ k : ℕ, 0 ≤ alphaSeq k ∧ alphaSeq k ≤ alphaBar)
    (halphaBar : alphaBar < 1) :
    Summable (fun k : ℕ ↦ posPart (phi k - phi (k - 1))) ∧
      ∃ phiStar : ℝ, 0 ≤ phiStar ∧ Tendsto phi atTop (𝓝 phiStar)
```

## Statement explanation
The lemma concerns three real sequences indexed by the natural numbers,

$$
\phi : \mathbb N \to \mathbb R,\qquad
\delta : \mathbb N \to \mathbb R,\qquad
\mathrm{alphaSeq} : \mathbb N \to \mathbb R,
$$

and a real number $\mathrm{alphaBar}$. The sequence $\phi$ is assumed nonnegative: for every $k\in\mathbb N$,

$$
0 \le \phi(k).
$$

The sequence $\delta$ is also assumed nonnegative:

$$
0 \le \delta(k)
$$

for every $k$, and its series is assumed summable:

$$
\sum_{k\in\mathbb N} \delta(k) \ \text{converges}.
$$

The recurrence hypothesis says that for every $k\in\mathbb N$,

$$
\phi(k+1)
\le \phi(k) + \mathrm{alphaSeq}(k)\bigl(\phi(k)-\phi(k-1)\bigr) + \delta(k).
$$

Here the expression $k-1$ is Lean’s natural-number predecessor: for $k=0$, $k-1=0$, so at $k=0$ the term $\phi(k)-\phi(k-1)$ is $\phi(0)-\phi(0)=0$; for $k\ge 1$ it is the usual previous index. Thus the recurrence is an inertial-type inequality controlled by the previous difference $\phi(k)-\phi(k-1)$, with nonnegative errors $\delta(k)$.

The coefficient sequence is assumed to lie between $0$ and $\mathrm{alphaBar}$:

$$
0 \le \mathrm{alphaSeq}(k) \le \mathrm{alphaBar}
$$

for every $k$, and the relaxation/inertia parameter is contracted:

$$
\mathrm{alphaBar} < 1.
$$

The conclusion is a conjunction of two statements. First, the positive parts of the successive differences are summable:

$$
\sum_{k\in\mathbb N} \mathrm{posPart}\!\bigl(\phi(k)-\phi(k-1)\bigr)
\ \text{converges},
$$

where $\mathrm{posPart}(t)=\max(t,0)$. Second, there exists a real number $\mathrm{phiStar}$ such that

$$
0 \le \mathrm{phiStar}
$$

and the sequence converges:

$$
\phi(k)\to \mathrm{phiStar}.
$$

So the lemma says that under an inertial recurrence with summable nonnegative forcing, a nonnegative sequence has summable positive increments and converges to a finite nonnegative limit.

## Lean proof
```lean
by
  set theta := fun k : ℕ => phi k - phi (k - 1) with htheta_def
  have htheta_zero : theta 0 = 0 := by
    dsimp [theta]
    simp
  have hpos_theta_zero : posPart (theta 0) = 0 := by
    rw [htheta_zero]
    dsimp [posPart]
    simp
  have halphaBar_nonneg : 0 ≤ alphaBar := by
    exact le_trans (halpha 0).1 (halpha 0).2
  have hone_sub_pos : 0 < 1 - alphaBar := by linarith
  have htheta_rec (k : ℕ) : theta (k + 1) ≤ alphaSeq k * theta k + delta k := by
    dsimp [theta]
    have h := hrec k
    linarith
  have hpos_rec (k : ℕ) :
      posPart (theta (k + 1)) ≤ alphaBar * posPart (theta k) + delta k := by
    have hmono : posPart (theta (k + 1)) ≤
        posPart (alphaSeq k * theta k + delta k) :=
      posPart_mono (htheta_rec k)
    have hsplit : posPart (alphaSeq k * theta k + delta k) ≤
        posPart (alphaSeq k * theta k) + delta k :=
      posPart_add_le_add_of_nonneg (hdelta_nonneg k)
    have hhom : posPart (alphaSeq k * theta k) = alphaSeq k * posPart (theta k) :=
      posPart_mul_of_nonneg (halpha k).1
    have hbound : alphaSeq k * posPart (theta k) ≤ alphaBar * posPart (theta k) := by
      exact mul_le_mul_of_nonneg_right (halpha k).2 (posPart_nonneg _)
    linarith
  set Dtotal := ∑' k, delta k with hDtotal_def
  have hDpartial_le_total (n : ℕ) :
      (Finset.range n).sum delta ≤ Dtotal := by
    simpa [Dtotal] using hdelta_sum.sum_le_tsum (Finset.range n)
      (fun i _hi => hdelta_nonneg i)
  have hsum_rec (n : ℕ) :
      (Finset.range n).sum (fun k => posPart (theta (k + 1))) ≤
        alphaBar * (Finset.range n).sum (fun k => posPart (theta k)) +
          (Finset.range n).sum delta := by
    calc
      (Finset.range n).sum (fun k => posPart (theta (k + 1)))
          ≤ (Finset.range n).sum
              (fun k => alphaBar * posPart (theta k) + delta k) := by
            exact Finset.sum_le_sum (fun k _hk => hpos_rec k)
      _ = alphaBar * (Finset.range n).sum (fun k => posPart (theta k)) +
          (Finset.range n).sum delta := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hS_bound (n : ℕ) :
      (Finset.range n).sum (fun k => posPart (theta k)) ≤
        Dtotal / (1 - alphaBar) := by
    have hDtotal_nonneg : 0 ≤ Dtotal := by
      simpa [Dtotal] using tsum_nonneg (fun k => hdelta_nonneg k)
    have hquot_nonneg : 0 ≤ Dtotal / (1 - alphaBar) := by
      exact div_nonneg hDtotal_nonneg hone_sub_pos.le
    by_cases hn : n = 0
    · subst n
      simpa using hquot_nonneg
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      set S : ℝ := (Finset.range (m + 1)).sum (fun k => posPart (theta k)) with hS_def
      have hsum := hsum_rec (m + 1)
      have hshift :
          (Finset.range (m + 1)).sum (fun k => posPart (theta (k + 1))) =
            (Finset.range (m + 2)).sum (fun k => posPart (theta k)) -
              posPart (theta 0) := by
        rw [Finset.sum_range_succ' (f := fun k => posPart (theta k)) (n := m + 1)]
        ring
      have hSsucc :
          (Finset.range (m + 2)).sum (fun k => posPart (theta k)) =
            S + posPart (theta (m + 1)) := by
        rw [hS_def]
        exact Finset.sum_range_succ _ _
      have hsum' :
          S + posPart (theta (m + 1)) ≤ alphaBar * S +
            (Finset.range (m + 1)).sum delta := by
        rw [hshift, hSsucc, hpos_theta_zero, sub_zero] at hsum
        simpa [S, hS_def] using hsum
      have hmain : (1 - alphaBar) * S ≤ (Finset.range (m + 1)).sum delta := by
        have hdrop : S ≤ alphaBar * S + (Finset.range (m + 1)).sum delta := by
          nlinarith [hsum', posPart_nonneg (theta (m + 1))]
        nlinarith
      have hmain_total : (1 - alphaBar) * S ≤ Dtotal :=
        le_trans hmain (hDpartial_le_total (m + 1))
      have hdiv : S ≤ Dtotal / (1 - alphaBar) := by
        exact (le_div_iff₀' hone_sub_pos).2 hmain_total
      simpa [S, hS_def] using hdiv
  have h_summable_theta : Summable (fun k : ℕ => posPart (theta k)) := by
    exact summable_of_sum_range_le (fun k => posPart_nonneg (theta k)) hS_bound
  have h_goal_i : Summable (fun k : ℕ ↦ posPart (phi k - phi (k - 1))) := by
    simpa [theta] using h_summable_theta
  set T := ∑' k, posPart (theta k) with hT_def
  set w := fun k : ℕ =>
    phi k - (Finset.range (k + 1)).sum (fun j => posPart (theta j)) with hw_def
  have hw_step (k : ℕ) : w (k + 1) ≤ w k := by
    have hcalc : w (k + 1) - w k = theta (k + 1) - posPart (theta (k + 1)) := by
      dsimp [w, theta]
      rw [Finset.sum_range_succ]
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      ring
    have hdiff : theta (k + 1) - posPart (theta (k + 1)) ≤ 0 := by
      linarith [posPart_ge_self (theta (k + 1))]
    linarith
  have hw_antitone : Antitone w := by
    intro a b hab
    induction' hab with b hb ih
    · exact le_rfl
    · exact le_trans (hw_step b) ih
  have hT_nonneg : 0 ≤ T := by
    simpa [T] using tsum_nonneg (fun k => posPart_nonneg (theta k))
  have hpartial_le_T (k : ℕ) :
      (Finset.range (k + 1)).sum (fun j => posPart (theta j)) ≤ T := by
    simpa [T] using h_summable_theta.sum_le_tsum (Finset.range (k + 1))
      (fun i _hi => posPart_nonneg (theta i))
  have hw_lower (k : ℕ) : -T ≤ w k := by
    dsimp [w]
    have hsum := hpartial_le_T k
    have hphi := hphi_nonneg k
    linarith
  have hw_bdd : BddBelow (Set.range w) := by
    refine ⟨-T, ?_⟩
    rintro y ⟨k, rfl⟩
    exact hw_lower k
  set L := ⨅ k, w k with hL_def
  have hw_tendsto : Tendsto w atTop (𝓝 L) := by
    simpa [L] using tendsto_atTop_ciInf hw_antitone hw_bdd
  have hpartial_tendsto :
      Tendsto (fun k : ℕ => (Finset.range (k + 1)).sum
        (fun j => posPart (theta j))) atTop (𝓝 T) := by
    have ht := h_summable_theta.hasSum.tendsto_sum_nat
    have hcomp := ht.comp (tendsto_add_atTop_nat 1)
    simpa [T, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcomp
  have hphi_tendsto : Tendsto phi atTop (𝓝 (L + T)) := by
    have hadd := hw_tendsto.add hpartial_tendsto
    have heq : (fun k : ℕ =>
        w k + (Finset.range (k + 1)).sum (fun j => posPart (theta j))) = phi := by
      funext k
      dsimp [w]
      ring
    simpa [heq] using hadd
  have h_limit_nonneg : 0 ≤ L + T := by
    exact ge_of_tendsto hphi_tendsto (Filter.Eventually.of_forall hphi_nonneg)
  exact ⟨h_goal_i, ⟨L + T, h_limit_nonneg, hphi_tendsto⟩⟩
```

## Proof explanation
The proof begins by introducing the abbreviation

$$
\theta(k)=\phi(k)-\phi(k-1).
$$

The tactic `set` only names this expression; it adds no new mathematical assumption. Because Lean’s subtraction on natural numbers is truncated, $0-1=0$, so

$$
\theta(0)=\phi(0)-\phi(0)=0.
$$

The proof records this as `htheta_zero`, and then uses the definition $\mathrm{posPart}(t)=\max(t,0)$ to get

$$
\mathrm{posPart}(\theta(0))=0.
$$

Next, the proof extracts nonnegativity of $\mathrm{alphaBar}$ from the coefficient bounds. Since

$$
0\le \mathrm{alphaSeq}(0)\le \mathrm{alphaBar},
$$

transitivity gives $0\le \mathrm{alphaBar}$. Together with $\mathrm{alphaBar}<1$, the linear-arithmetic tactic `linarith` proves

$$
0<1-\mathrm{alphaBar}.
$$

This positive denominator will later control the growth of the positive parts.

The recurrence for $\theta$ is then derived. From

$$
\phi(k+1)
\le \phi(k)+\mathrm{alphaSeq}(k)\bigl(\phi(k)-\phi(k-1)\bigr)+\delta(k),
$$

subtracting $\phi(k)$ from both sides gives

$$
\theta(k+1)=\phi(k+1)-\phi(k)
\le \mathrm{alphaSeq}(k)\theta(k)+\delta(k).
$$

This is the inequality `htheta_rec`.

The key one-step estimate for the positive parts follows by combining the local `posPart` lemmas. First, monotonicity of $\mathrm{posPart}$, stated by `posPart_mono`, gives

$$
\mathrm{posPart}(\theta(k+1))
\le \mathrm{posPart}\bigl(\mathrm{alphaSeq}(k)\theta(k)+\delta(k)\bigr).
$$

The lemma `posPart_add_le_add_of_nonneg` says that if $0\le y$, then

$$
\mathrm{posPart}(x+y)\le \mathrm{posPart}(x)+y.
$$

Applying it with $x=\mathrm{alphaSeq}(k)\theta(k)$ and $y=\delta(k)$, using $0\le \delta(k)$, yields

$$
\mathrm{posPart}\bigl(\mathrm{alphaSeq}(k)\theta(k)+\delta(k)\bigr)
\le \mathrm{posPart}\bigl(\mathrm{alphaSeq}(k)\theta(k)\bigr)+\delta(k).
$$

Since $\mathrm{alphaSeq}(k)\ge 0$, the homogeneity lemma `posPart_mul_of_nonneg` gives

$$
\mathrm{posPart}\bigl(\mathrm{alphaSeq}(k)\theta(k)\bigr)
=\mathrm{alphaSeq}(k)\mathrm{posPart}(\theta(k)).
$$

Finally, because $\mathrm{alphaSeq}(k)\le \mathrm{alphaBar}$ and $\mathrm{posPart}(\theta(k))\ge 0$ by `posPart_nonneg`, multiplication by the nonnegative factor preserves the inequality:

$$
\mathrm{alphaSeq}(k)\mathrm{posPart}(\theta(k))
\le
\mathrm{alphaBar}\mathrm{posPart}(\theta(k)).
$$

Combining these inequalities gives

$$
\mathrm{posPart}(\theta(k+1))
\le
\mathrm{alphaBar}\mathrm{posPart}(\theta(k))+\delta(k).
$$

The proof then defines

$$
D=\sum_{k\in\mathbb N}\delta(k).
$$

Since $\delta(k)\ge 0$ for all $k$, every finite partial sum is at most the full sum:

$$
\sum_{k=0}^{n-1}\delta(k)\le D.
$$

This uses the standard finite-sum comparison for nonnegative summable series.

Summing the one-step estimate over $k=0,\dots,n-1$ gives

$$
\sum_{k=0}^{n-1}\mathrm{posPart}(\theta(k+1))
\le
\mathrm{alphaBar}\sum_{k=0}^{n-1}\mathrm{posPart}(\theta(k))
+\sum_{k=0}^{n-1}\delta(k).
$$

The proof uses `Finset.sum_add_distrib` and `Finset.mul_sum` to distribute the finite sum and factor out $\mathrm{alphaBar}$.

The next goal is a uniform bound on the partial sums of the nonnegative sequence $\mathrm{posPart}(\theta(k))$. The proof shows that for every $n$,

$$
\sum_{k=0}^{n-1}\mathrm{posPart}(\theta(k))
\le
\frac{D}{1-\mathrm{alphaBar}}.
$$

The case $n=0$ is trivial because the sum is $0$. For $n=m+1$, the proof writes

$$
S=\sum_{k=0}^{m}\mathrm{posPart}(\theta(k)).
$$

From the summed estimate for $n=m+1$, the left-hand sum is shifted:

$$
\sum_{k=0}^{m}\mathrm{posPart}(\theta(k+1))
=\sum_{k=0}^{m+1}\mathrm{posPart}(\theta(k))
-\mathrm{posPart}(\theta(0)).
$$

Since $\mathrm{posPart}(\theta(0))=0$, this becomes

$$
S+\mathrm{posPart}(\theta(m+1)).
$$

Dropping the nonnegative term $\mathrm{posPart}(\theta(m+1))$ gives

$$
S\le \mathrm{alphaBar} S+\sum_{k=0}^{m}\delta(k).
$$

Rearranging,

$$
(1-\mathrm{alphaBar})S\le \sum_{k=0}^{m}\delta(k)\le D.
$$

Because $1-\mathrm{alphaBar}>0$, division by this positive number yields

$$
S\le \frac{D}{1-\mathrm{alphaBar}}.
$$

Thus the partial sums of $\mathrm{posPart}(\theta(k))$ are uniformly bounded.

The theorem `summable_of_sum_range_le` is then used: a nonnegative sequence whose finite sums over initial intervals are uniformly bounded is summable. Therefore

$$
\sum_{k\in\mathbb N}\mathrm{posPart}(\theta(k))
$$

converges. Since $\theta(k)=\phi(k)-\phi(k-1)$, this proves the first part of the conclusion:

$$
\sum_{k\in\mathbb N}\mathrm{posPart}\bigl(\phi(k)-\phi(k-1)\bigr)
$$

is summable.

For the convergence of $\phi$, the proof sets

$$
T=\sum_{k\in\mathbb N}\mathrm{posPart}(\theta(k)),
$$

which is finite by the previous step, and defines

$$
w(k)=\phi(k)-\sum_{j=0}^{k}\mathrm{posPart}(\theta(j)).
$$

Then it computes the difference

$$
w(k+1)-w(k)
=\theta(k+1)-\mathrm{posPart}(\theta(k+1)).
$$

The lemma `posPart_ge_self` states $t\le \mathrm{posPart}(t)$. Hence

$$
\theta(k+1)-\mathrm{posPart}(\theta(k+1))\le 0,
$$

so

$$
w(k+1)\le w(k).
$$

By induction on the inequality $a\le b$, the proof concludes that $w$ is antitone:

$$
a\le b \implies w(b)\le w(a).
$$

Next, $T\ge 0$, because it is the sum of nonnegative terms. Also, for every $k$,

$$
\sum_{j=0}^{k}\mathrm{posPart}(\theta(j))\le T,
$$

using the standard property that a finite partial sum of a summable nonnegative series is at most the total sum. Since $\phi(k)\ge 0$, this yields

$$
w(k)
=\phi(k)-\sum_{j=0}^{k}\mathrm{posPart}(\theta(j))
\ge -T.
$$

Therefore the range of $w$ is bounded below by $-T$.

The proof lets

$$
L=\inf_k w(k).
$$

Because $w$ is antitone and bounded below, the theorem `tendsto_atTop_ciInf` gives

$$
w(k)\to L.
$$

At the same time, since the series $\sum_k \mathrm{posPart}(\theta(k))$ is summable with sum $T$, its partial sums converge to $T$. Composing the partial-sum convergence with the shift $k\mapsto k+1$ gives

$$
\sum_{j=0}^{k}\mathrm{posPart}(\theta(j))\to T.
$$

Now the identity

$$
\phi(k)
=w(k)+\sum_{j=0}^{k}\mathrm{posPart}(\theta(j))
$$

shows that $\phi$ is the sum of two convergent sequences. Therefore

$$
\phi(k)\to L+T.
$$

Finally, since every $\phi(k)\ge 0$ and $\phi(k)\to L+T$, the limit is nonnegative:

$$
0\le L+T.
$$

This is the standard “nonnegative terms have a nonnegative limit” argument, formalized by `ge_of_tendsto` together with the fact that all $\phi(k)$ are nonnegative. Taking $\mathrm{phiStar}=L+T$ completes the proof of the existence of a nonnegative limit.

