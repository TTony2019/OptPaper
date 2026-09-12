## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_6.lean`

## Lean statement
```lean
theorem ext_thm_6_painleve_kuratowski {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (c : ℝ) (xstar : X) (hc_lt_one : c < 1)
    (hcontr : ∀ x y : X, dist (T x) (T y) ≤ c * dist x y)
    (hfix : T xstar = xstar) :
    (∀ (εseq : ℕ → ℝ) (yseq : ℕ → X), (∀ n, 0 < εseq n) →
        Tendsto εseq atTop (nhds 0) →
        (∀ n, dist (yseq n) (T (yseq n)) ≤ εseq n) →
        Tendsto yseq atTop (nhds xstar)) ∧
      (∀ ε : ℝ, 0 ≤ ε → dist xstar (T xstar) ≤ ε)
```

## Statement explanation
The declaration `ext_thm_6_painleve_kuratowski` is a theorem about a self-map \(T:X\to X\) of a type \(X\) equipped with a pseudo-metric-space structure. Let \(d\) denote `dist`. The theorem takes a real coefficient \(c\), a point \(x_\star\in X\), and assumes \(c<1\), the contraction-type inequality
\[
d(Tx,Ty)\le c\,d(x,y)\qquad\text{for all }x,y\in X,
\]
and the fixed-point equation
\[
T x_\star=x_\star.
\]
No lower bound such as \(0\le c\) is assumed; the only numerical hypothesis is \(c<1\).

The conclusion is a conjunction of two statements. The first is a stability statement for approximate fixed points. It says that for every sequence of real errors \(\varepsilon_n\) and every sequence \(y_n\in X\), if each \(\varepsilon_n>0\), if \(\varepsilon_n\to0\), and if each \(y_n\) is an \(\varepsilon_n\)-approximate fixed point of \(T\), meaning
\[
d(y_n,T y_n)\le \varepsilon_n
\]
for every \(n\), then
\[
y_n\to x_\star.
\]
Thus any sequence of approximate fixed points whose errors tend to zero must converge to the exact fixed point \(x_\star\).

The second conjunct says that for every real number \(\varepsilon\) with \(0\le\varepsilon\),
\[
d(x_\star,T x_\star)\le\varepsilon.
\]
Because \(x_\star\) is fixed, \(T x_\star=x_\star\), so this inequality is actually \(d(x_\star,x_\star)=0\le\varepsilon\). It records that the exact fixed point is an \(\varepsilon\)-fixed point for every nonnegative tolerance. The positivity hypothesis on the error sequence is present in the statement but is not used in the proof.

## Lean proof
```lean
by
  constructor
  · intro εseq yseq _ hlim hyseq
    have hle : ∀ n, dist (yseq n) xstar ≤ εseq n / (1 - c) := fun n =>
      epsilon_fix_dist_le T c xstar hc_lt_one hcontr hfix (hyseq n)
    have hlim' : Tendsto (fun n => εseq n / (1 - c)) atTop (nhds 0) := by
      simpa using hlim.div_const (1 - c)
    have hdist : Tendsto (fun n => dist (yseq n) xstar) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
        (Eventually.of_forall fun _ => dist_nonneg) (Eventually.of_forall hle)
    exact tendsto_iff_dist_tendsto_zero.mpr hdist
  · intro ε hε
    rw [hfix, dist_self]
    exact hε
```

## Proof explanation
The proof begins with the tactic `constructor`, which splits the conjunction goal into two separate goals, one for the sequence-stability statement and one for the \(\varepsilon\)-inequality.

For the first conjunct, the proof uses `intro` to introduce the two sequences, the positivity hypothesis, the limit hypothesis \(\varepsilon_n\to0\), and the approximate-fixed-point inequalities. The positivity hypothesis is discarded as `_`, since it is not needed in the argument.

The next step introduces the intermediate fact that for every \(n\),
\[
d(y_n,x_\star)\le \frac{\varepsilon_n}{1-c}.
\]
This is obtained by applying the cited result `epsilon_fix_dist_le` separately for each \(n\). That result states, for a pseudo-metric space, a map \(T\), a real number \(c\), a point \(x_\star\), a contraction-type inequality
\[
d(Tx,Ty)\le c\,d(x,y),
\]
the assumptions \(c<1\) and \(T x_\star=x_\star\), and a point \(y\) satisfying
\[
d(y,T y)\le\varepsilon,
\]
that
\[
d(y,x_\star)\le \frac{\varepsilon}{1-c}.
\]
Specialized to the present proof, with \(y=y_n\) and \(\varepsilon=\varepsilon_n\), the approximate-fixedness hypothesis \(d(y_n,T y_n)\le\varepsilon_n\) yields
\[
d(y_n,x_\star)\le \frac{\varepsilon_n}{1-c}.
\]
This is the standard estimate that an approximate fixed point of a contraction lies close to an exact fixed point.

The proof then shows that the upper bound sequence \(\varepsilon_n/(1-c)\) tends to \(0\). From the hypothesis that \(\varepsilon_n\to0\), the result `hlim.div_const` gives that the sequence
\[
n\mapsto \frac{\varepsilon_n}{1-c}
\]
tends to
\[
\frac{0}{1-c}=0.
\]
The tactic `simpa` performs the simplification needed to turn the resulting limit expression into the stated target that this quotient sequence tends to \(0\). Since \(c<1\), the denominator \(1-c\) is not zero, though the intended conclusion is simply that division by the fixed constant preserves the limit.

At this point the proof has:
\[
0\le d(y_n,x_\star)
\]
for all \(n\), by nonnegativity of distance, and
\[
d(y_n,x_\star)\le \frac{\varepsilon_n}{1-c}
\]
for all \(n\). It converts these pointwise inequalities into eventual inequalities using `Eventually.of_forall`. Then it invokes the squeeze theorem for filters, named `tendsto_of_tendsto_of_tendsto_of_le_of_le'`. Its role here is: if the lower sequence is eventually at most \(d(y_n,x_\star)\), if \(d(y_n,x_\star)\) is eventually at most the upper sequence, and if both the lower and upper sequences tend to \(0\), then the middle sequence also tends to \(0\). The lower sequence is the constant sequence \(0\), supplied by `tendsto_const_nhds`, and the upper sequence is \(\varepsilon_n/(1-c)\), which was just shown to tend to \(0\). Therefore the proof obtains
\[
d(y_n,x_\star)\to0.
\]

Finally, the proof applies `tendsto_iff_dist_tendsto_zero.mpr`. In a pseudo-metric space, a sequence \(y_n\) converges to \(x_\star\) exactly when the real sequence \(d(y_n,x_\star)\) converges to \(0\). Since the previous step established \(d(y_n,x_\star)\to0\), this equivalence gives the desired convergence
\[
y_n\to x_\star.
\]
This completes the first conjunct.

For the second conjunct, the proof uses `intro` to introduce an arbitrary real number \(\varepsilon\) and the hypothesis \(0\le\varepsilon\). The tactic `rw` then rewrites using `hfix`, replacing \(T x_\star\) by \(x_\star\), and then rewrites \(d(x_\star,x_\star)\) to \(0\) using `dist_self`. The goal therefore becomes
\[
0\le\varepsilon.
\]
This is exactly the introduced hypothesis, so the tactic `exact` closes the goal using it. Thus the second conjunct is established.

