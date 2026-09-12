## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_1.lean`

## Lean statement
```lean
theorem lemma_2_3_two_step_summability (xi eps : Nat -> Real) (a b : Real)
    (hxi_nonneg : ∀ n, 0 <= xi n)
    (heps_nonneg : ∀ n, 0 <= eps n)
    (heps_sum : Summable eps)
    (hb_nonneg : 0 <= b)
    (hab : a + b < 1)
    (hrec : ∀ n, 1 <= n -> xi (n + 1) <= a * xi n + b * xi (n - 1) + eps n) :
    Summable xi
```

## Statement explanation
The theorem concerns two real sequences $\xi=(\xi_n)_{n\in\mathbb N}$ and $\varepsilon=(\varepsilon_n)_{n\in\mathbb N}$, written in Lean as `xi` and `eps`, together with two real parameters $a$ and $b$. Its hypotheses are:

- $\xi_n\ge 0$ for every $n$, i.e. the sequence $\xi$ is nonnegative.
- $\varepsilon_n\ge 0$ for every $n$, i.e. the sequence $\varepsilon$ is nonnegative.
- $\varepsilon$ is summable, meaning that $\sum_{n=0}^{\infty}\varepsilon_n$ converges.
- $b\ge 0$.
- $a+b<1$.
- For every $n\ge 1$,

  $$
  \xi_{n+1}\le a\xi_n+b\xi_{n-1}+\varepsilon_n.
  $$

The conclusion is that $\xi$ itself is summable, i.e.

$$
\sum_{n=0}^{\infty}\xi_n
$$

converges.

Mathematically, this is a summability criterion for a nonnegative sequence satisfying a two-step linear recurrence inequality with a nonnegative summable forcing term. The coefficient condition $a+b<1$ and the assumption $b\ge0$ are enough to force the partial sums of $\xi$ to be bounded, and hence, since all terms are nonnegative, the series $\sum \xi_n$ converges. The proof obtains an explicit uniform upper bound for every finite partial sum.

## Lean proof
```lean
by
  have hden_pos : 0 < 1 - a - b := by linarith
  let C : Real := ((1 - a) * xi 0 + xi 1 + ∑' n, eps n) / (1 - a - b)
  have hshift_two : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => xi (m + 2)) + xi 0 + xi 1 =
        Finset.sum (Finset.range (k + 2)) xi := by
    intro k
    induction k with
    | zero => simp [Finset.sum_range_succ]
    | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [← ih]
        ring
  have hshift_one : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => xi (m + 1)) + xi 0 =
        Finset.sum (Finset.range (k + 1)) xi := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [← ih]
        ring
  have htail_le_tsum : ∀ k : Nat,
      Finset.sum (Finset.range k) (fun m => eps (m + 1)) <= ∑' n, eps n := by
    intro k
    rw [← Finset.sum_image]
    · exact heps_sum.sum_le_tsum ((Finset.range k).image (fun m => m + 1)) (by
        intro n hn
        exact heps_nonneg n)
    · intro x hx y hy hxy
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxy)
  have hpartial : ∀ k : Nat, 1 <= k ->
      (1 - a - b) * Finset.sum (Finset.range (k + 1)) xi <=
        (1 - a) * xi 0 + xi 1 + Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
    intro k hk
    have hsum_rec :
        Finset.sum (Finset.range k) (fun m => xi (m + 2)) <=
          a * Finset.sum (Finset.range k) (fun m => xi (m + 1)) +
          b * Finset.sum (Finset.range k) xi +
          Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
      calc
        Finset.sum (Finset.range k) (fun m => xi (m + 2))
            <= Finset.sum (Finset.range k)
                (fun m => a * xi (m + 1) + b * xi m + eps (m + 1)) := by
              exact Finset.sum_le_sum (fun m hm => by
                simpa [Nat.add_assoc] using
                  hrec (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
        _ = a * Finset.sum (Finset.range k) (fun m => xi (m + 1)) +
              b * Finset.sum (Finset.range k) xi +
              Finset.sum (Finset.range k) (fun m => eps (m + 1)) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
    set S : Real := Finset.sum (Finset.range (k + 1)) xi
    set L : Real := Finset.sum (Finset.range k) (fun m => xi (m + 2))
    set A : Real := Finset.sum (Finset.range k) (fun m => xi (m + 1))
    set B : Real := Finset.sum (Finset.range k) xi
    set E : Real := Finset.sum (Finset.range k) (fun m => eps (m + 1))
    have hLsum : L + xi 0 + xi 1 = S + xi (k + 1) := by
      dsimp [L, S]
      have hsucc :
          Finset.sum (Finset.range (k + 1)) xi + xi (k + 1) =
            Finset.sum (Finset.range (k + 2)) xi := by
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
          (Finset.sum_range_succ xi (k + 1)).symm
      nlinarith [hshift_two k]
    have hAsum : A + xi 0 = S := by
      dsimp [A, S]
      exact hshift_one k
    have hBsum : B + xi k = S := by
      dsimp [B, S]
      simpa [Nat.succ_eq_add_one] using (Finset.sum_range_succ xi k).symm
    have hmain : S + xi (k + 1) - xi 0 - xi 1 <= (a + b) * S - a * xi 0 - b * xi k + E := by
      have hA' : A = S - xi 0 := by linarith
      have hB' : B = S - xi k := by linarith
      have hL' : L = S + xi (k + 1) - xi 0 - xi 1 := by linarith
      have hrec' : L <= a * A + b * B + E := by simpa [L, A, B, E] using hsum_rec
      rw [hL', hA', hB'] at hrec'
      nlinarith
    have hxkp1 : 0 <= xi (k + 1) := hxi_nonneg _
    have hbxk : 0 <= b * xi k := mul_nonneg hb_nonneg (hxi_nonneg _)
    dsimp [S, E] at hmain ⊢
    nlinarith
  have hbound : ∀ n : Nat, Finset.sum (Finset.range n) xi <= C := by
    intro n
    cases n with
    | zero =>
        have hnum_nonneg : 0 <= (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
          have ha_nonneg : 0 <= 1 - a := by linarith
          have htsum_nonneg : 0 <= ∑' n, eps n := tsum_nonneg heps_nonneg
          nlinarith [mul_nonneg ha_nonneg (hxi_nonneg 0), hxi_nonneg 1, htsum_nonneg]
        dsimp [C]
        exact div_nonneg hnum_nonneg hden_pos.le
    | succ n =>
        cases n with
        | zero =>
            rw [Finset.sum_range_one]
            have hnum_ge : (1 - a - b) * xi 0 <= (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
              have htsum_nonneg : 0 <= ∑' n, eps n := tsum_nonneg heps_nonneg
              have hbx0 : 0 <= b * xi 0 := mul_nonneg hb_nonneg (hxi_nonneg _)
              have hx1 : 0 <= xi 1 := hxi_nonneg _
              nlinarith
            dsimp [C]
            rw [div_eq_inv_mul]
            exact (le_inv_mul_iff₀ hden_pos).2 hnum_ge
        | succ k =>
            have hk : 1 <= k + 1 := by omega
            have hpart := hpartial (k + 1) hk
            have htail := htail_le_tsum (k + 1)
            have hnum : (1 - a - b) * Finset.sum (Finset.range ((k + 1) + 1)) xi <=
                (1 - a) * xi 0 + xi 1 + ∑' n, eps n := by
              nlinarith
            dsimp [C]
            rw [div_eq_inv_mul]
            exact (le_inv_mul_iff₀ hden_pos).2 hnum
  exact summable_of_sum_range_le hxi_nonneg hbound
```

## Proof explanation
The proof begins by noting that $a+b<1$ implies

$$
0<1-a-b.
$$

This is the local fact `hden_pos`, proved by `linarith` from the hypothesis $a+b<1$. The positivity of $1-a-b$ will later allow division by this quantity.

Next the proof defines

$$
C=\frac{(1-a)\xi_0+\xi_1+\sum_{n=0}^{\infty}\varepsilon_n}{1-a-b}.
$$

This is the candidate bound for all partial sums of $\xi$. The numerator is finite because $\varepsilon$ is summable, and the denominator is positive by `hden_pos`.

The proof then establishes two finite-sum reindexing identities. For every $k$,

$$
\sum_{m=0}^{k-1}\xi_{m+2}+\xi_0+\xi_1
=\sum_{i=0}^{k+1}\xi_i.
$$

This is `hshift_two`. Similarly, for every $k$,

$$
\sum_{m=0}^{k-1}\xi_{m+1}+\xi_0
=\sum_{i=0}^{k}\xi_i.
$$

This is `hshift_one`. Both are proved by induction on $k$. In the base cases, the sums over empty ranges vanish, and `simp` simplifies the expressions. In the successor step, the proof uses `Finset.sum_range_succ`, which expresses a sum over $0,\ldots,k$ as the previous sum plus the last term, and then `ring` rearranges the resulting algebraic identity.

Next the proof shows that the shifted finite sums of the nonnegative summable sequence $\varepsilon$ are bounded by the total sum. Specifically, for every $k$,

$$
\sum_{m=0}^{k-1}\varepsilon_{m+1}
\le
\sum_{n=0}^{\infty}\varepsilon_n.
$$

This is `htail_le_tsum`. The sum $\sum_{m=0}^{k-1}\varepsilon_{m+1}$ is a finite sum over the indices $1,2,\ldots,k$. The proof rewrites it as a sum over the image of the range $k$ under the map $m\mapsto m+1$, using `Finset.sum_image`. To justify this rewriting, it proves injectivity of that map on the relevant set: if $x+1=y+1$, then $x=y$, via `Nat.succ.inj`. Then it applies `heps_sum.sum_le_tsum`, which says that for a summable nonnegative sequence, every finite sum over a finite set is at most the total infinite sum. Thus the tail-shaped finite sums of $\varepsilon$ are controlled by the full sum $\sum \varepsilon_n$.

The central estimate is `hpartial`, which states that for every $k\ge1$,

$$
(1-a-b)\sum_{i=0}^{k}\xi_i
\le
(1-a)\xi_0+\xi_1+\sum_{m=0}^{k-1}\varepsilon_{m+1}.
$$

To prove this, the proof first sums the recurrence inequality. For each $m=0,\ldots,k-1$, applying the hypothesis to $n=m+1$ gives

$$
\xi_{m+2}\le a\xi_{m+1}+b\xi_m+\varepsilon_{m+1}.
$$

Summing these inequalities from $m=0$ to $m=k-1$, using `Finset.sum_le_sum`, yields

$$
\sum_{m=0}^{k-1}\xi_{m+2}
\le
a\sum_{m=0}^{k-1}\xi_{m+1}
+b\sum_{m=0}^{k-1}\xi_m
+\sum_{m=0}^{k-1}\varepsilon_{m+1}.
$$

The equality step uses `Finset.sum_add_distrib` to distribute a sum of three terms, and `Finset.mul_sum` to pull the constants $a$ and $b$ out of the finite sums. This is the local fact `hsum_rec`.

Then the proof introduces abbreviations

$$
S=\sum_{i=0}^{k}\xi_i,\qquad
L=\sum_{m=0}^{k-1}\xi_{m+2},\qquad
A=\sum_{m=0}^{k-1}\xi_{m+1},\qquad
B=\sum_{m=0}^{k-1}\xi_m,\qquad
E=\sum_{m=0}^{k-1}\varepsilon_{m+1}.
$$

Using the previously proved reindexing identities, it obtains

$$
L+\xi_0+\xi_1=S+\xi_{k+1},\qquad
A+\xi_0=S,\qquad
B+\xi_k=S.
$$

Therefore

$$
L=S+\xi_{k+1}-\xi_0-\xi_1,\qquad
A=S-\xi_0,\qquad
B=S-\xi_k.
$$

Substituting these into `hsum_rec` gives

$$
S+\xi_{k+1}-\xi_0-\xi_1
\le
(a+b)S-a\xi_0-b\xi_k+E.
$$

Rearranging,

$$
(1-a-b)S
\le
(1-a)\xi_0+\xi_1+E-\xi_{k+1}-b\xi_k.
$$

Since $\xi_{k+1}\ge0$ and, because $b\ge0$ and $\xi_k\ge0$, also $b\xi_k\ge0$, the terms $-\xi_{k+1}$ and $-b\xi_k$ can be dropped from the upper bound. Hence

$$
(1-a-b)S
\le
(1-a)\xi_0+\xi_1+E.
$$

Replacing $S$ and $E$ by their definitions gives exactly `hpartial`. The arithmetic rearrangements here are handled by `nlinarith`, using the nonnegativity facts $\xi_{k+1}\ge0$ and $b\xi_k\ge0$.

The proof then proves `hbound`, the statement that every finite partial sum of $\xi$ is at most $C$:

$$
\sum_{i=0}^{n-1}\xi_i\le C
$$

for every natural number $n$. The proof splits into three cases.

First, for $n=0$, the partial sum is empty and equals $0$. The proof shows $0\le C$. It checks that the numerator

$$
(1-a)\xi_0+\xi_1+\sum_{n=0}^{\infty}\varepsilon_n
$$

is nonnegative. Indeed, $1-a\ge0$ follows from $0<1-a-b$ and $b\ge0$, and $1-a$ times $\xi_0$ is nonnegative because $\xi_0\ge0$. Also $\xi_1\ge0$, and $\sum \varepsilon_n\ge0$ by `tsum_nonneg` applied to the nonnegativity of $\varepsilon$. Then `div_nonneg` gives $0\le C$ because the denominator $1-a-b$ is positive.

Second, for $n=1$, the partial sum is $\xi_0$. The proof shows

$$
(1-a-b)\xi_0
\le
(1-a)\xi_0+\xi_1+\sum_{n=0}^{\infty}\varepsilon_n.
$$

This is equivalent to

$$
0\le b\xi_0+\xi_1+\sum_{n=0}^{\infty}\varepsilon_n,
$$

which follows from $b\ge0$, $\xi_0\ge0$, $\xi_1\ge0$, and $\sum\varepsilon_n\ge0$. Then the inequality $\xi_0\le C$ is obtained by dividing by the positive number $1-a-b$. In Lean this division step is expressed by rewriting $C$ with `div_eq_inv_mul`, turning the goal into $\xi_0\le (1-a-b)^{-1}N$, where $N$ is the numerator, and then applying `le_inv_mul_iff₀` with the positivity of $1-a-b$. That lemma says precisely that for positive $d$, $x\le d^{-1}N$ is equivalent to $d x\le N$.

Third, for $n=k+2$, the partial sum is

$$
\sum_{i=0}^{k+1}\xi_i.
$$

The proof uses `hpartial` with $k+1$, which requires $1\le k+1$ and is supplied by `omega`. Thus

$$
(1-a-b)\sum_{i=0}^{k+1}\xi_i
\le
(1-a)\xi_0+\xi_1+\sum_{m=0}^{k}\varepsilon_{m+1}.
$$

It also uses `htail_le_tsum` with $k+1$ to bound the finite sum of $\varepsilon$'s by the full infinite sum:

$$
\sum_{m=0}^{k}\varepsilon_{m+1}
\le
\sum_{n=0}^{\infty}\varepsilon_n.
$$

Combining these inequalities gives

$$
(1-a-b)\sum_{i=0}^{k+1}\xi_i
\le
(1-a)\xi_0+\xi_1+\sum_{n=0}^{\infty}\varepsilon_n.
$$

Then, exactly as in the $n=1$ case, the proof divides by the positive number $1-a-b$ using `div_eq_inv_mul` and `le_inv_mul_iff₀`, obtaining

$$
\sum_{i=0}^{k+1}\xi_i\le C.
$$

This completes the proof that every finite partial sum of $\xi$ is bounded above by $C$.

Finally, the proof applies `summable_of_sum_range_le` to the nonnegativity hypothesis `hxi_nonneg` and the uniform bound `hbound`. The content of that result is that if a sequence of nonnegative real numbers has all its finite partial sums bounded above by a fixed constant, then the corresponding series is summable. Since the hypotheses give $\xi_n\ge0$ for every $n$ and the proof has shown

$$
\sum_{i=0}^{n-1}\xi_i\le C
$$

for every $n$, the lemma yields `Summable xi`, which is exactly the conclusion of the theorem.

